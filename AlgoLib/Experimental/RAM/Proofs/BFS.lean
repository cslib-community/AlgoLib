/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Library.GraphMemory
import AlgoLib.Experimental.RAM.Proofs.LoopVC
import Mathlib.Tactic

/-! Internal instruction invariants, reused by the typed source refinement. -/
namespace AlgoLib.Experimental.RAM.BFS
open Checked
/-- Register aliases: all are members of the existing fixed eight-register bank. -/
abbrev head : Reg := .base
abbrev tail : Reg := .count
abbrev ptr : Reg := .cursor
abbrev vertex : Reg := .key
abbrev addr : Reg := .next
abbrev neighbor : Reg := .temp
abbrev marked : Reg := .live

def scanBody : Code := .seq (.block [
  .bin .mul addr (.lit 5) (.reg ptr),
  .bin .add addr (.reg addr) (.lit 3),
  .load neighbor (.reg addr),
  .bin .mul addr (.lit 5) (.reg neighbor),
  .bin .add addr (.reg addr) (.lit 1),
  .load marked (.reg addr)])
  (.seq (.ite (.eq (.reg marked) (.lit 0)) (.block [
  .store (.reg addr) (.lit 1),
  .bin .mul addr (.lit 5) (.reg tail),
  .bin .add addr (.reg addr) (.lit 2),
  .store (.reg addr) (.reg neighbor),
  .bin .add tail (.reg tail) (.lit 1)]) (.block [])) (.block [
  .bin .mul addr (.lit 5) (.reg ptr),
  .bin .add addr (.reg addr) (.lit 4),
  .load ptr (.reg addr)]))
def scanTest : Test := .lt (.lit 0) (.reg ptr)
def scanCode : Code := .while scanTest scanBody
def popBody : Code := .block [
    .bin .mul addr (.lit 5) (.reg head),
    .bin .add addr (.reg addr) (.lit 2),
    .load vertex (.reg addr),
    .bin .add head (.reg head) (.lit 1),
    .bin .mul addr (.lit 5) (.reg vertex),
    .load ptr (.reg addr)]
def bfsTest : Test := .lt (.reg head) (.reg tail)
def bfsBody : Code := .seq popBody scanCode
def bfsLoop : Code := .while bfsTest bfsBody
open Checked

/-- Ghost effect of mark-before-enqueue. -/
def discover (seen : Finset Nat) (queue : List Nat) (v : Nat) : Finset Nat × List Nat :=
  if v ∈ seen then (seen, queue) else (insert v seen, queue ++ [v])

private def reads : List Instr := [
  .bin .mul addr (.lit 5) (.reg ptr),
  .bin .add addr (.reg addr) (.lit 3),
  .load neighbor (.reg addr),
  .bin .mul addr (.lit 5) (.reg neighbor),
  .bin .add addr (.reg addr) (.lit 1),
  .load marked (.reg addr)]
private def writes : List Instr := [
  .store (.reg addr) (.lit 1),
  .bin .mul addr (.lit 5) (.reg tail),
  .bin .add addr (.reg addr) (.lit 2),
  .store (.reg addr) (.reg neighbor),
  .bin .add tail (.reg tail) (.lit 1)]
private def advance : List Instr := [
  .bin .mul addr (.lit 5) (.reg ptr),
  .bin .add addr (.reg addr) (.lit 4),
  .load ptr (.reg addr)]

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
    ∃ k t, Exec scanBody s k t ∧ k ≤ 15 ∧
      t.regs head = s.regs head ∧
      t.regs tail = t.regs head + (discover seen queue v).2.length ∧
      t.regs ptr = s.memory (5 * s.regs ptr + 4) ∧
      GraphFrame s.memory t.memory ∧
      View n t.memory (discover seen queue v).1 (discover seen queue v).2 (t.regs head) := by
  have hm := view.marks v hv
  let r := blockEval reads s
  have hr : r.regs marked = if v ∈ seen then 1 else 0 := by
    simpa [r, reads, blockEval, Instr.eval, State.set, Operand.eval, BinOp.eval,
      addr, neighbor, ptr, marked, hd] using hm
  by_cases hseen : v ∈ seen
  · let t := blockEval advance r
    have hx : Exec scanBody s 10 t := by
      rw [scanBody_shape]
      exact .seq (.block reads s) (.seq
        (.ifFalse (by change decide (r.regs marked = 0) = false; simp [hr, hseen]) (.block [] r))
        (.block advance r))
    have hmem : t.memory = s.memory := rfl
    have hhead : t.regs head = s.regs head := by
      simp [t, r, advance, reads, blockEval, Instr.eval, State.set, Operand.eval,
        BinOp.eval, head, addr, ptr, neighbor, marked]
    refine ⟨10, t, hx, by omega, hhead, ?_, ?_, ?_, ?_⟩
    · simpa [discover, hseen, t, r, advance, reads, blockEval, Instr.eval,
        State.set, Operand.eval, BinOp.eval, head, tail, addr, ptr, neighbor, marked] using ht
    · simp [t, r, advance, reads, blockEval, Instr.eval, State.set,
        Operand.eval, BinOp.eval, addr, ptr, neighbor, marked]
    · exact GraphFrame.refl _
    · simpa [discover, hseen, hmem, hhead] using view
  · let w := blockEval writes r
    let t := blockEval advance w
    have hx : Exec scanBody s 15 t := by
      rw [scanBody_shape]
      exact .seq (.block reads s) (.seq
        (.ifTrue (by change decide (r.regs marked = 0) = true; simp [hr, hseen]) (.block writes r))
        (.block advance w))
    have hmem : t.memory = enqueueMemory s.memory v (s.regs tail) := by
      simp [t, w, r, advance, writes, reads, blockEval, Instr.eval,
        State.set, Operand.eval, BinOp.eval, enqueueMemory, addr, ptr, neighbor, marked, tail, hd]
    have hhead : t.regs head = s.regs head := by
      simp [t, w, r, advance, writes, reads, blockEval, Instr.eval, State.set,
        Operand.eval, BinOp.eval, head, tail, addr, ptr, neighbor, marked]
    have hf : GraphFrame s.memory t.memory := by rw [hmem]; exact enqueue_frame _ _ _
    refine ⟨15, t, hx, by omega, hhead, ?_, ?_, hf, ?_⟩
    · simp [discover, hseen, t, w, r, advance, writes, reads, blockEval, Instr.eval,
        State.set, Operand.eval, BinOp.eval, head, tail, addr, ptr, neighbor, marked, ht,
        Nat.add_assoc]
    · have htp : t.regs ptr = t.memory (5 * s.regs ptr + 4) := by
        simp [t, w, r, advance, writes, reads, blockEval, Instr.eval, State.set,
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
    LoopVC scanTest scanBody (ScanRep n before result)
      (fun g => 16 * g.remaining.length)
      (fun t => t.regs head = before.regs head ∧
        t.regs tail = t.regs head + result.2.length ∧
        GraphFrame before.memory t.memory ∧
        View n t.memory result.1 result.2 (t.regs head)) := by
  constructor
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

open Checked

@[simp] theorem scan_seen (xs : List Nat) (seen : Finset Nat) (queue : List Nat) (v : Nat) :
    v ∈ (scan xs seen queue).1 ↔ v ∈ seen ∨ v ∈ xs := by
  induction xs generalizing seen queue with
  | nil => simp [scan]
  | cons u us ih =>
    simp only [scan]
    rw [ih]
    by_cases hu : u ∈ seen <;> simp [discover, hu] <;> aesop

@[simp] theorem scan_queue (xs : List Nat) (seen : Finset Nat) (queue : List Nat) (v : Nat) :
    v ∈ (scan xs seen queue).2 ↔ v ∈ queue ∨ (v ∈ xs ∧ v ∉ seen) := by
  induction xs generalizing seen queue with
  | nil => simp [scan]
  | cons u us ih =>
    simp only [scan]
    rw [ih]
    by_cases hu : u ∈ seen
    · simp only [discover, if_pos hu, List.mem_cons]
      constructor
      · tauto
      · rintro (h | ⟨h | h, hn⟩)
        · exact Or.inl h
        · subst v; contradiction
        · exact Or.inr ⟨h, hn⟩
    · simp only [discover, if_neg hu, List.mem_append,
        Finset.mem_insert, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h | h) | ⟨h, hn⟩)
        · exact Or.inl h
        · subst v; exact Or.inr ⟨Or.inl rfl, hu⟩
        · exact Or.inr ⟨Or.inr h, fun hv => hn (Or.inr hv)⟩
      · tauto

theorem scan_distinct (xs : List Nat) (seen : Finset Nat) (queue : List Nat)
    (hq : queue.Nodup) (hqseen : ∀ v ∈ queue, v ∈ seen) : (scan xs seen queue).2.Nodup := by
  induction xs generalizing seen queue with
  | nil => exact hq
  | cons v vs ih =>
    simp only [scan]
    by_cases hv : v ∈ seen
    · simpa [discover, hv] using ih seen queue hq hqseen
    · simp only [discover, if_neg hv]
      apply ih
      · have hvq : v ∉ queue := fun h => hv (hqseen v h)
        simpa using hq.append (List.nodup_singleton v) (List.disjoint_singleton.mpr hvq)
      · intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact Finset.mem_insert_of_mem (hqseen w hw)
        · exact Finset.mem_insert_self _ _

/-- Discovered vertices are the processed vertices together with the FIFO. -/
def discovered (done : Finset Nat) (queue : List Nat) : Finset Nat := done ∪ queue.toFinset

@[simp] theorem mem_discovered {done : Finset Nat} {queue : List Nat} {v : Nat} :
    v ∈ discovered done queue ↔ v ∈ done ∨ v ∈ queue := by simp [discovered]

/-- Maintenance of the mathematical invariant, independently of memory layout. -/
theorem Invariant.process {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) {source u : Nat} {done : Finset Nat} {queue : List Nat}
    (h : Invariant a G source done (u :: queue)) :
    let result := scan (a.neighbors u) (discovered done (u :: queue)) queue
    result.1 = discovered (insert u done) result.2 ∧
      Invariant a G source (insert u done) result.2 := by
  dsimp only
  have hu : u < a.n := h.valid_queue u (by simp)
  have hud : u ∉ done := h.disjoint u (by simp)
  have hqu : u ∉ queue := (List.nodup_cons.mp h.distinct).1
  have hq := h.distinct.of_cons
  have heq : (scan (a.neighbors u) (discovered done (u :: queue)) queue).1 =
      discovered (insert u done) (scan (a.neighbors u) (discovered done (u :: queue)) queue).2 := by
    ext v
    simp only [scan_seen, mem_discovered, scan_queue, Finset.mem_insert, List.mem_cons]
    tauto
  refine ⟨heq, ?_⟩
  constructor
  · exact scan_distinct _ _ _ hq (fun v hv => by simp [hv])
  · intro v hv hd
    rw [scan_queue] at hv
    rcases hv with hv | ⟨_, hn⟩
    · rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hqu hv
      · exact h.disjoint v (by simp [hv]) hd
    · apply hn
      simp only [mem_discovered, List.mem_cons]
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hd
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hu
    · exact h.valid_done v hv
  · intro v hv
    rcases (scan_queue _ _ _ _).mp hv with hv | ⟨hv, _⟩
    · exact h.valid_queue v (by simp [hv])
    · exact a.valid u hu v hv
  · have hs : source ∈ (scan (a.neighbors u) (discovered done (u :: queue)) queue).1 :=
      (scan_seen _ _ _ _).mpr (Or.inl (mem_discovered.mpr h.source_seen))
    simpa [heq] using hs
  · intro v hv
    have hs : v ∈ (scan (a.neighbors u) (discovered done (u :: queue)) queue).1 := by
      rw [heq]; exact mem_discovered.mpr hv
    rcases (scan_seen _ _ _ _).mp hs with hs | hs
    · exact h.sound v (mem_discovered.mp hs)
    · exact .step (h.sound u (by simp)) ((rep.adjacency u hu v).mp hs)
  · intro v hv w hw
    have hs : w ∈ (scan (a.neighbors u) (discovered done (u :: queue)) queue).1 := by
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (scan_seen _ _ _ _).mpr (Or.inr hw)
      · exact (scan_seen _ _ _ _).mpr (Or.inl (mem_discovered.mpr (h.closed v hv w hw)))
    simpa [heq] using hs

/-- Charge each unprocessed vertex for its dequeue, guards, and adjacency scan. -/
def potential (a : Adjacency) (done : Finset Nat) : Nat :=
  ∑ v ∈ Finset.range a.n \ done, (8 + 16 * (a.neighbors v).length)

theorem potential_process (a : Adjacency) (done : Finset Nat) {u : Nat}
    (hu : u < a.n) (hud : u ∉ done) :
    potential a (insert u done) + (8 + 16 * (a.neighbors u).length) = potential a done := by
  have he : Finset.range a.n \ insert u done = (Finset.range a.n \ done).erase u := by
    ext v; simp; tauto
  unfold potential
  rw [he]
  exact Finset.sum_erase_add _ _ (by simp [hu, hud])

theorem potential_initial (a : Adjacency) : potential a ∅ = 8 * a.n + 16 * a.entries := by
  simp [potential, Adjacency.entries, Finset.sum_add_distrib, Finset.mul_sum,
    Nat.mul_comm]

/-- Ghost data at the outer loop header. -/
abbrev Frontier := Finset Nat × List Nat

def LoopRep {β : Type*} (a : Adjacency) (G : Graph Nat β) (source : Nat)
    (g : Frontier) (s : State) : Prop :=
  Invariant a G source g.1 g.2 ∧ Heap a s.memory ∧
  View a.n s.memory (discovered g.1 g.2) g.2 (s.regs head) ∧
  s.regs tail = s.regs head + g.2.length

private def popped (s : State) : State :=
  blockEval [
    .bin .mul addr (.lit 5) (.reg head),
    .bin .add addr (.reg addr) (.lit 2),
    .load vertex (.reg addr),
    .bin .add head (.reg head) (.lit 1),
    .bin .mul addr (.lit 5) (.reg vertex),
    .load ptr (.reg addr)] s

private theorem pop_correct (s : State) :
    Exec popBody s 6 (popped s) ∧
    (popped s).memory = s.memory ∧
    (popped s).regs head = s.regs head + 1 ∧
    (popped s).regs tail = s.regs tail ∧
    (popped s).regs ptr = s.memory (5 * s.memory (5 * s.regs head + 2)) := by
  refine ⟨Exec.block _ s, rfl, ?_, ?_, ?_⟩ <;>
    simp [popped, blockEval, Instr.eval, State.set, Operand.eval, BinOp.eval,
      head, tail, addr, vertex, ptr]

/-- Generated loop VCs for both reachability and running time. The proof only
uses the row-scan contract, the graph invariant, and one potential identity. -/
theorem bfs_vc {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) (source : Nat) :
    LoopVC bfsTest bfsBody (LoopRep a G source) (fun g => potential a g.1)
      (fun s => ReturnsReachable G source (fun v => v < a.n ∧ s.memory (5 * v + 1) = 1)) := by
  constructor
  · intro g s h hstop
    obtain ⟨hi, _, hv, ht⟩ := h
    have hnil : g.2 = [] := by
      have : ¬ s.regs head < s.regs tail := by simpa [bfsTest, Test.eval, Operand.eval] using hstop
      have : g.2.length = 0 := by omega
      exact List.eq_nil_of_length_eq_zero this
    have hc := (hnil ▸ hi).exit rep
    intro v
    constructor
    · rintro ⟨hvn, hmark⟩
      apply (hc v).mp
      have := hv.marks v hvn
      simp [hnil] at this
      split_ifs at this with hm
      · exact hm
      · omega
    · intro hr
      have hd := (hc v).mpr hr
      have hvn := hi.valid_done v hd
      exact ⟨hvn, by simpa [hnil, hd] using hv.marks v hvn⟩
  · rintro ⟨done, queue⟩ s ⟨hi, heap, view, ht⟩ hgo
    cases queue with
    | nil => simp [bfsTest, Test.eval, Operand.eval, ht] at hgo
    | cons u queue =>
      have hu := hi.valid_queue u (by simp)
      have hud := hi.disjoint u (by simp)
      have hslot : s.memory (5 * s.regs head + 2) = u := by simpa using view.slots 0 u rfl
      obtain ⟨hx, hm, hh, htail, hp⟩ := pop_correct s
      have hchain : Chain (popped s).memory ((popped s).regs ptr) (a.neighbors u) := by
        rw [hp, hm, hslot]; exact heap u hu
      have hview : View a.n (popped s).memory (discovered done (u :: queue)) queue
          ((popped s).regs head) := by rw [hm, hh]; exact view.pop
      have htt : (popped s).regs tail = (popped s).regs head + queue.length := by
        rw [htail, hh]; simp only [List.length_cons] at ht; omega
      obtain ⟨k, t, hs, hk, hh', ht', hf, hv⟩ := scan_correct (a.valid u hu) hchain hview htt
      obtain ⟨heq, hi'⟩ := hi.process rep
      refine ⟨(insert u done, (scan (a.neighbors u) (discovered done (u :: queue)) queue).2),
        6 + k, t, .seq hx hs, ?_, ?_⟩
      · exact ⟨hi', heap.frame (by simpa [hm] using hf), by simpa [heq] using hv, ht'⟩
      · have hp := potential_process a done hu hud
        dsimp only
        omega

/-- The machine loop returns exactly the reachable set in linear time in the
number of vertices plus stored adjacency entries. -/
theorem bfs_loop_correct {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) {source : Nat} {s : State}
    (h : LoopRep a G source (∅, [source]) s) :
    ∃ k t, Exec bfsLoop s k t ∧
      ReturnsReachable G source (fun v => v < a.n ∧ t.memory (5 * v + 1) = 1) ∧
      k ≤ 8 * a.n + 32 * rep.edges.card + 1 := by
  obtain ⟨k, t, hx, hQ, hk⟩ := (bfs_vc rep source).sound h
  refine ⟨k, t, hx, hQ, ?_⟩
  simp only [potential_initial] at hk
  have := rep.incidenceBound
  omega

open Checked

abbrev size : Reg := .limit

def clearBody : Code := .block [
  .bin .mul addr (.lit 5) (.reg head),
  .bin .add addr (.reg addr) (.lit 1),
  .store (.reg addr) (.lit 0),
  .bin .add head (.reg head) (.lit 1)]

def clearTest : Test := .lt (.reg head) (.reg size)
def clearCode : Code := .while clearTest clearBody

private def cleared (s : State) : State := blockEval [
  .bin .mul addr (.lit 5) (.reg head),
  .bin .add addr (.reg addr) (.lit 1),
  .store (.reg addr) (.lit 0),
  .bin .add head (.reg head) (.lit 1)] s

private theorem clear_correct (s : State) : Exec clearBody s 4 (cleared s) ∧
    (cleared s).regs head = s.regs head + 1 ∧
    (cleared s).regs size = s.regs size ∧
    (cleared s).regs vertex = s.regs vertex ∧
    (cleared s).memory = Function.update s.memory (5 * s.regs head + 1) 0 := by
  refine ⟨Exec.block _ s, ?_, ?_, ?_, ?_⟩ <;>
    simp [cleared, blockEval, Instr.eval, State.set, Operand.eval, BinOp.eval,
      head, size, addr, vertex]

/-- The initialization VCs include clearing every flag; zeroed scratch memory is
not an assumption on the caller. Queue cells are initialized when enqueued. -/
theorem clear_vc (n source : Nat) (m : Memory) :
    LoopVC clearTest clearBody
      (fun j s => s.regs head = j ∧ j ≤ n ∧ s.regs size = n ∧ s.regs vertex = source ∧
        GraphFrame m s.memory ∧ ∀ v < j, s.memory (5 * v + 1) = 0)
      (fun j => 5 * (n - j))
      (fun s => s.regs size = n ∧ s.regs vertex = source ∧ GraphFrame m s.memory ∧
        ∀ v < n, s.memory (5 * v + 1) = 0) := by
  constructor
  · rintro j s ⟨hj, hjn, hn, hs, hf, hz⟩ hq
    have : ¬ j < n := by simpa [clearTest, Test.eval, Operand.eval, hj, hn] using hq
    have : j = n := by omega
    exact ⟨hn, hs, hf, this ▸ hz⟩
  · rintro j s ⟨hj, hjn, hn, hs, hf, hz⟩ hq
    have hjlt : j < n := by simpa [clearTest, Test.eval, Operand.eval, hj, hn] using hq
    obtain ⟨hx, hh, hn', hs', hm⟩ := clear_correct s
    refine ⟨j + 1, 4, cleared s, hx, ?_, by omega⟩
    refine ⟨hh.trans (by omega), by omega, hn'.trans hn, hs'.trans hs, ?_, ?_⟩
    · rw [hm]; exact hf.trans (graphFrame_write _ _ 0 1 (Or.inl rfl))
    · intro v hv
      rw [hm, hj]
      by_cases h : v = j
      · subst v; simp
      · rw [Function.update_of_ne (by omega)]
        exact hz v (by omega)

/-- Put the source in the FIFO and mark it before entering the BFS loop. -/
def seed : Code := .block [
  .bin .mul addr (.lit 5) (.reg vertex),
  .bin .add addr (.reg addr) (.lit 1),
  .store (.reg addr) (.lit 1),
  .store (.lit 2) (.reg vertex),
  .mov head (.lit 0),
  .mov tail (.lit 1)]

private def seeded (s : State) : State := blockEval [
  .bin .mul addr (.lit 5) (.reg vertex),
  .bin .add addr (.reg addr) (.lit 1),
  .store (.reg addr) (.lit 1),
  .store (.lit 2) (.reg vertex),
  .mov head (.lit 0),
  .mov tail (.lit 1)] s

private theorem seed_correct (s : State) : Exec seed s 6 (seeded s) ∧
    (seeded s).regs head = 0 ∧ (seeded s).regs tail = 1 ∧
    (seeded s).memory = enqueueMemory s.memory (s.regs vertex) 0 := by
  refine ⟨Exec.block _ s, ?_, ?_, ?_⟩ <;>
    simp [seeded, blockEval, Instr.eval, State.set, Operand.eval, BinOp.eval,
      head, tail, addr, vertex, enqueueMemory]

/-- One fixed RAM program, independent of graph size, source, and input contents. -/
def bfsCode : Code := .seq (.block [.mov head (.lit 0)])
  (.seq clearCode (.seq seed bfsLoop))

/-- The complete uniform algorithm: actual RAM execution, exact reachability,
and a linear bound including flag initialization. `n` is the number of vertices
and `m` is the number of labelled edges, including parallel edges. -/
theorem bfs_correct {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) (source : Nat) (hs : source < a.n) (s : State)
    (hn : s.regs size = a.n) (hsource : s.regs vertex = source) (heap : Heap a s.memory) :
    ∃ k t, Exec bfsCode s k t ∧
      ReturnsReachable G source (fun v => v < a.n ∧ t.memory (5 * v + 1) = 1) ∧
      k ≤ 13 * a.n + 32 * rep.edges.card + 9 := by
  let z := s.set head 0
  have hz : z.regs head = 0 := by simp [z, State.set]
  have hzn : z.regs size = a.n := by simpa [z, State.set, size, head] using hn
  have hzs : z.regs vertex = source := by simpa [z, State.set, vertex, head] using hsource
  obtain ⟨i, u, hu, ⟨hun, hus, hf, hzero⟩, hi⟩ := (clear_vc a.n source s.memory).sound
    (g := 0) (s := z) ⟨hz, by omega, hzn, hzs, .refl _, by simp⟩
  obtain ⟨he, hh, ht, hm⟩ := seed_correct u
  have hview : View a.n (seeded u).memory (discovered ∅ [source]) [source]
      ((seeded u).regs head) := by
    have emptyView : View a.n u.memory ∅ [] 0 := ⟨by simpa using hzero, by simp⟩
    simpa [hm, hh, hus, discovered] using emptyView.enqueue (v := source)
  have hinv : Invariant a G source ∅ [source] := by
    refine ⟨by simp, by simp, by simp, ?_, by simp, ?_, by simp⟩
    · intro v hv; simpa using (List.mem_singleton.mp hv ▸ hs)
    · intro v hv
      have : v = source := by simpa using hv
      subst v
      exact .refl ((rep.vertices source).mpr hs)
  have hrep : LoopRep a G source (∅, [source]) (seeded u) := by
    refine ⟨hinv, ?_, hview, by simp [hh, ht]⟩
    rw [hm, hus]
    exact (heap.frame hf).frame (enqueue_frame _ _ _)
  obtain ⟨j, t, hj, hQ, hjcost⟩ := bfs_loop_correct rep hrep
  refine ⟨1 + (i + (6 + j)), t, .seq (.block _ s) (.seq hu (.seq he hj)), hQ, ?_⟩
  simp only [Nat.sub_zero] at hi
  omega


end AlgoLib.Experimental.RAM.BFS
