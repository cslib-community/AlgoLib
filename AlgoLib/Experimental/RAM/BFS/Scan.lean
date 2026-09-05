/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Memory

/-!
# Verified adjacency-row scanning

Local instruction contracts and the row loop's correctness/time verification conditions.
-/

namespace AlgoLib.Experimental.RAM.BFS
open Checked Checked.Source

/-- Ghost effect of mark-before-enqueue. -/
def discover (seen : Finset Nat) (queue : List Nat) (v : Nat) : Finset Nat × List Nat :=
  if v ∈ seen then (seen, queue) else (insert v seen, queue ++ [v])

private def reads : List Simple := [
  .assign addr (.bin .mul (.lit 5) (.reg ptr)),
  .assign addr (.bin .add (.reg addr) (.lit 3)),
  .assign neighbor (.load (.reg addr)),
  .assign addr (.bin .mul (.lit 5) (.reg neighbor)),
  .assign addr (.bin .add (.reg addr) (.lit 1)),
  .assign marked (.load (.reg addr))]
private def writes : List Simple := [
  .store (.reg addr) (.lit 1),
  .assign addr (.bin .mul (.lit 5) (.reg tail)),
  .assign addr (.bin .add (.reg addr) (.lit 2)),
  .store (.reg addr) (.reg neighbor),
  .assign tail (.bin .add (.reg tail) (.lit 1))]
private def advance : List Simple := [
  .assign addr (.bin .mul (.lit 5) (.reg ptr)),
  .assign addr (.bin .add (.reg addr) (.lit 4)),
  .assign ptr (.load (.reg addr))]

private theorem scanBody_shape : scanBody =
    .seq (.block reads) (.seq (.ite (.eq (.reg marked) (.lit 0))
      (.block writes) (.block [])) (.block advance)) := rfl

/-- The generated straight-line obligations: one entry costs at most fifteen
instructions/tests, preserves the immutable heap and head, advances one link,
and changes the ghost queue exactly by `discover`. -/
theorem scanBody_correct {n : Nat} {s : State} {seen : Finset Nat} {queue : List Nat}
    {v : Nat} (hv : v < n)
    (view : View n s.memory seen queue (s.regs head))
    (ht : s.regs tail = s.regs head + queue.length)
    (hd : s.memory (5 * s.regs ptr + 3) = v) :
    ∃ k t, Exec scanBody.compile s k t ∧ k ≤ 15 ∧
      t.regs head = s.regs head ∧
      t.regs tail = t.regs head + (discover seen queue v).2.length ∧
      t.regs ptr = s.memory (5 * s.regs ptr + 4) ∧
      GraphFrame s.memory t.memory ∧
      View n t.memory (discover seen queue v).1 (discover seen queue v).2 (t.regs head) := by
  have hm := view.marks v hv
  let r := block reads s
  have hr : r.regs marked = if v ∈ seen then 1 else 0 := by
    simpa [r, reads, block, Simple.eval, Expr.eval, State.set, Operand.eval, BinOp.eval,
      addr, neighbor, ptr, marked, hd] using hm
  by_cases hseen : v ∈ seen
  · let t := block advance r
    have hx : Eval scanBody s 10 t := by
      rw [scanBody_shape]
      exact .seq (.block reads s) (.seq
        (.ifFalse (by change decide (r.regs marked = 0) = false; simp [hr, hseen]) (.block [] r))
        (.block advance r))
    have hmem : t.memory = s.memory := rfl
    have hhead : t.regs head = s.regs head := by
      simp [t, r, advance, reads, block, Simple.eval, Expr.eval, State.set, Operand.eval,
        BinOp.eval, head, addr, ptr, neighbor, marked]
    refine ⟨10, t, hx.compile, by omega, hhead, ?_, ?_, ?_, ?_⟩
    · simpa [discover, hseen, t, r, advance, reads, block, Simple.eval, Expr.eval,
        State.set, Operand.eval, BinOp.eval, head, tail, addr, ptr, neighbor, marked] using ht
    · simp [t, r, advance, reads, block, Simple.eval, Expr.eval, State.set,
        Operand.eval, BinOp.eval, addr, ptr, neighbor, marked]
    · exact GraphFrame.refl _
    · simpa [discover, hseen, hmem, hhead] using view
  · let w := block writes r
    let t := block advance w
    have hx : Eval scanBody s 15 t := by
      rw [scanBody_shape]
      exact .seq (.block reads s) (.seq
        (.ifTrue (by change decide (r.regs marked = 0) = true; simp [hr, hseen]) (.block writes r))
        (.block advance w))
    have hmem : t.memory = enqueueMemory s.memory v (s.regs tail) := by
      simp [t, w, r, advance, writes, reads, block, Simple.eval, Expr.eval,
        State.set, Operand.eval, BinOp.eval, enqueueMemory, addr, ptr, neighbor, marked, tail, hd]
    have hhead : t.regs head = s.regs head := by
      simp [t, w, r, advance, writes, reads, block, Simple.eval, Expr.eval, State.set,
        Operand.eval, BinOp.eval, head, tail, addr, ptr, neighbor, marked]
    have hf : GraphFrame s.memory t.memory := by rw [hmem]; exact enqueue_frame _ _ _
    refine ⟨15, t, hx.compile, by omega, hhead, ?_, ?_, hf, ?_⟩
    · simp [discover, hseen, t, w, r, advance, writes, reads, block, Simple.eval, Expr.eval,
        State.set, Operand.eval, BinOp.eval, head, tail, addr, ptr, neighbor, marked, ht,
        Nat.add_assoc]
    · have htp : t.regs ptr = t.memory (5 * s.regs ptr + 4) := by
        simp [t, w, r, advance, writes, reads, block, Simple.eval, Expr.eval, State.set,
          Operand.eval, BinOp.eval, tail, addr, ptr, neighbor, marked]
        rfl
      exact htp.trans (hf.2.2 _)
    · simpa [discover, hseen, hmem, hhead, ht] using view.enqueue (v := v)

/-- Pure ghost scan, used only in specifications and proofs. -/
def scan (xs : List Nat) (seen : Finset Nat) (queue : List Nat) : Finset Nat × List Nat :=
  match xs with
  | [] => (seen, queue)
  | v :: vs => let d := discover seen queue v; scan vs d.1 d.2

/-- Ghost row cursor and discovery state for a modular scan proof. -/
structure ScanGhost where
  remaining : List Nat
  seen : Finset Nat
  queue : List Nat

def ScanRep (n : Nat) (before : State) (result : Finset Nat × List Nat)
    (g : ScanGhost) (s : State) : Prop :=
  (∀ v ∈ g.remaining, v < n) ∧ Chain s.memory (s.regs ptr) g.remaining ∧
  View n s.memory g.seen g.queue (s.regs head) ∧
  s.regs tail = s.regs head + g.queue.length ∧ s.regs head = before.regs head ∧
  GraphFrame before.memory s.memory ∧ scan g.remaining g.seen g.queue = result

/-- The inner-loop VCs are local: advance one link, preserve the memory view,
and spend at most sixteen credits. The list-length potential is ghost data. -/
theorem scan_vc (n : Nat) (before : State) (result : Finset Nat × List Nat) :
    LoopVC scanTest scanBody.compile (ScanRep n before result)
      (fun g => 16 * g.remaining.length)
      (fun t => t.regs head = before.regs head ∧
        t.regs tail = t.regs head + result.2.length ∧
        GraphFrame before.memory t.memory ∧
        View n t.memory result.1 result.2 (t.regs head)) := by
  vcgen
  · rintro ⟨xs, seen, queue⟩ s ⟨_, hc, hv, ht, hh, hf, he⟩ hq
    cases xs with
    | nil => cases he; exact ⟨hh, ht, hf, hv⟩
    | cons v vs =>
      have : s.regs ptr = 0 := by simpa [scanTest, Test.eval, Operand.eval] using hq
      exact (hc.1 this).elim
  · rintro ⟨xs, seen, queue⟩ s ⟨valid, hc, hv, ht, hh, hf, he⟩ hq
    cases xs with
    | nil =>
      change s.regs ptr = 0 at hc
      simp [scanTest, Test.eval, Operand.eval, hc] at hq
    | cons v vs =>
      obtain ⟨k, t, hx, hk, hh', ht', hp, hf', hv'⟩ :=
        scanBody_correct (valid v (by simp)) hv ht hc.2.1
      refine ⟨⟨vs, (discover seen queue v).1, (discover seen queue v).2⟩,
        k, t, hx, ?_, ?_⟩
      · refine ⟨fun w hw => valid w (by simp [hw]), ?_, hv', ht',
          hh'.trans hh, hf.trans hf', he⟩
        rw [hp]
        exact hc.2.2.frame hf'
      · dsimp only
        simp only [List.length_cons]
        omega

/-- The scan loop refines an adjacency-list traversal. The generated time VC
also proves termination, and the bound includes the final false guard. -/
theorem scan_correct {n : Nat} {s : State} {seen : Finset Nat} {queue xs : List Nat}
    (valid : ∀ v ∈ xs, v < n)
    (chain : Chain s.memory (s.regs ptr) xs)
    (view : View n s.memory seen queue (s.regs head))
    (ht : s.regs tail = s.regs head + queue.length) :
    ∃ k t, Exec scanCode s k t ∧ k ≤ 16 * xs.length + 1 ∧
      t.regs head = s.regs head ∧
      t.regs tail = t.regs head + (scan xs seen queue).2.length ∧
      GraphFrame s.memory t.memory ∧
      View n t.memory (scan xs seen queue).1 (scan xs seen queue).2 (t.regs head) := by
  obtain ⟨k, t, hx, ⟨hh, ht, hf, hv⟩, hk⟩ := (scan_vc n s (scan xs seen queue)).sound
    (g := ⟨xs, seen, queue⟩) (s := s) ⟨valid, chain, view, ht, rfl, .refl _, rfl⟩
  exact ⟨k, t, hx, hk, hh, ht, hf, hv⟩

end AlgoLib.Experimental.RAM.BFS
