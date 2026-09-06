/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Realization
import AlgoLib.Experimental.RAM.Backend.Language.Refinement
import AlgoLib.Experimental.RAM.Backend.Certificates.InsertionSort

/-!
# Insertion representation adapter

Constructs the logical todo/sorted state, its physical representation, and certified insertion and
guard operations.

Reuses local instruction certificates and typed refinement. Public equations are exposed by
Library/Insertion; algorithm files never unfold this representation.
-/
namespace AlgoLib.Experimental.RAM.Authoring.Insertion
open Checked Checked.Language

/-- The unprocessed prefix is listed in processing order (right to left). -/
structure State where
  todo : List Nat
  sorted : List Nat
  deriving DecidableEq

def effect (g : State) : State :=
  match g.todo with
  | [] => g
  | x :: xs => ⟨xs, List.orderedInsert (· ≤ ·) x g.sorted⟩

def model : Model State where
  Represents g s := Refinement.Ready s ∧ (Refinement.view s).regs .base = 0 ∧
    (Refinement.view s).regs .count = g.todo.length ∧
    (Refinement.view s).regs .limit = g.todo.length + g.sorted.length ∧
    Segment s 0 g.todo.reverse ∧ Segment s g.todo.length g.sorted
  overhead := 50

theorem segment_contents {s : Store} {b : Nat} {xs : List Nat}
    (h : Segment s b xs) : contents s.heap b xs.length = xs := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    change s.heap b :: contents s.heap (b+1) xs.length = x :: xs
    rw [h.head, ih h.tail]

/-- A linear-time insertion into an adjacent suffix. This is a reusable array
operation, with a contract independent of the outer sorting invariant. -/
def insertNext : Action State where
  requires g := g.todo ≠ []
  effect := effect
  work g := g.sorted.length + 1

instance insertNextImplementation : ActionImplementation model insertNext where
  implementation := Refinement.lift outerBody
  correct g s hs hg := by
    dsimp only [insertNext] at *
    obtain ⟨ready, hb, hc, he, hprefix, suffix⟩ := hs
    cases htodo : g.todo with
    | nil => exact (hg htodo).elim
    | cons x xs =>
      have hp : Segment s 0 (xs.reverse ++ [x]) := by simpa [htodo] using hprefix
      have hcount : (Refinement.view s).regs .count = xs.length + 1 := by simpa [htodo] using hc
      let u := blockEval prepare (Refinement.view s)
      have ub : u.regs .base = 0 := by
        simpa [u, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval,
          Checked.State.set] using hb
      have uc : u.regs .count = xs.length := by
        simp [u, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval,
          Checked.State.set, hcount]
      have up : u.regs .cursor = xs.length := by
        simp [u, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval,
          Checked.State.set, hcount, hb]
      have uk : u.regs .key = x := by
        simpa [u, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval, Checked.State.set,
          hcount, hb] using hp.last
      have un : u.regs .next = u.regs .cursor + 1 := by
        simp [u, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval, Checked.State.set]
      have ul : u.regs .live = 1 := by
        simp [u, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval, Checked.State.set]
      have ue : u.regs .limit = (Refinement.view s).regs .limit := by
        simp [u, prepare, blockEval, Instr.eval, Operand.eval, BinOp.eval, Checked.State.set]
      have uend : u.regs .limit = u.regs .cursor + g.sorted.length + 1 := by
        rw [ue, up, he]; simp only [htodo, List.length_cons]; omega
      obtain ⟨k, t, ht, hm, htb, htc, hte, hk⟩ := insertCode_exec g.sorted.length u un uend ul
      have hx : Exec outerBody (Refinement.view s) (5+k) t := .seq (.block _ _) ht
      obtain ⟨j, w, hw, hr, hwv, hj⟩ := Refinement.lift_correct hx (by decide) s ready rfl
      have hmem : w.heap = (insert xs.length x g.sorted.length s.heap).memory := by
        have hh := (congrArg Checked.State.memory hwv).trans hm
        rw [up, uk] at hh
        exact hh
      refine ⟨j, w, hw, ⟨hr, ?_, ?_, ?_, ?_, ?_⟩, by dsimp [model]; omega⟩
      · rw [hwv, htb, ub]
      · simpa [effect, htodo, hwv] using htc.trans uc
      · simpa [effect, htodo, hwv, he, List.orderedInsert_length, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hte.trans ue
      · simp only [effect, htodo]
        intro i hi
        rw [hmem, insert_frame _ _ _ _ _ (Or.inl (by simpa using hi))]
        exact hp.prefix i hi
      · simp only [effect, htodo]
        change Segment w xs.length (List.orderedInsert (· ≤ ·) x g.sorted)
        have hcontents : contents w.heap xs.length (g.sorted.length+1) =
            List.orderedInsert (· ≤ ·) x g.sorted := by
          rw [hmem, insert_contents]
          congr 1
          apply segment_contents
          simpa [htodo] using suffix
        have get : ∀ (ys : List Nat) (b : Nat),
            contents w.heap b ys.length = ys → Segment w b ys := by
          intro ys
          induction ys with
          | nil => intro b _; exact Segment.nil _ _
          | cons y ys ih =>
            intro b hh
            have hh' : w.heap b = y ∧ contents w.heap (b+1) ys.length = ys := by
              simpa [contents] using hh
            intro i hi
            cases i with
            | zero => simpa using hh'.1
            | succ i =>
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih (b+1) hh'.2 i (by simpa using hi)
        apply get
        simpa [List.orderedInsert_length] using hcontents

def more : Guard State where
  test g := !g.todo.isEmpty

instance moreImplementation : GuardImplementation model more where
  implementation := Refinement.condition outerTest
  correct g s hs := by
    dsimp only [more] at *
    rw [Refinement.condition_eval]
    simp only [outerTest, Test.eval, Operand.eval, hs.2.2.1]
    cases g.todo <;> simp
  cost := by simp [model]

end AlgoLib.Experimental.RAM.Authoring.Insertion
