/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Language.Syntax
import AlgoLib.Experimental.RAM.Language.Refinement
import AlgoLib.Experimental.RAM.Proofs.InsertionSort

/-!
# Insertion sort through the complete source-to-RAM stack

The source program inserts each predecessor into a sorted suffix. Its actual
compiled execution satisfies sortedness, permutation, the frame, and a quadratic
bound. Instruction-level invariant proofs serve only as refinement certificates.
-/
namespace AlgoLib.Experimental.RAM.Algorithms.InsertionSort
open Checked Checked.Language

private abbrev base := Refinement.slot .base
private abbrev remaining := Refinement.slot .count
private abbrev stop := Refinement.slot .limit
private abbrev hole := Refinement.slot .cursor
private abbrev key := Refinement.slot .key
private abbrev next := Refinement.slot .next
private abbrev candidate := Refinement.slot .temp
private abbrev active := Refinement.slot .live
private abbrev A := Refinement.memory

/-- One closed DSL program for every array length and every input value. -/
def sourceProgram : Cmd := program {
  stop := base + remaining;
  while 0 < remaining {
    remaining := remaining - 1;
    hole := base + remaining;
    key := A[hole];
    next := hole + 1;
    active := 1;
    while 0 < active {
      if next < stop {
        candidate := A[next];
        if key <= candidate {
          active := 0;
        } else {
          A[hole] := candidate;
          hole := next;
          next := next + 1;
        }
      } else {
        active := 0;
      }
    }
    A[hole] := key;
  }
}

/-- Machine-checked agreement with the invariant proof's instruction structure. -/
theorem refinement : (Refinement.lift sortCode).normalize = sourceProgram.normalize := rfl

def Post (s t : Store) : Prop :=
  (contents t.heap (s.vars .word base.name) (s.vars .word remaining.name)).Pairwise (· ≤ ·) ∧
  (contents t.heap (s.vars .word base.name) (s.vars .word remaining.name)).Perm
    (contents s.heap (s.vars .word base.name) (s.vars .word remaining.name)) ∧
  ∀ a, a < s.vars .word base.name ∨
    s.vars .word base.name + s.vars .word remaining.name ≤ a → t.heap a = s.heap a

def budget (n : Nat) : Nat := 20 * n ^ 2 + 40 * n + 10

/-- The algorithm contract is about the DSL semantics, including expression work. -/
theorem correct : Contract sourceProgram Refinement.Ready Post
    (fun s => budget (s.vars .word remaining.name)) := by
  intro s hs
  obtain ⟨k, t, hx, hsorted, hperm, hframe, hk⟩ := sortCode_correct (Refinement.view s)
  obtain ⟨j, u, hu, _, hview, hj⟩ :=
    Refinement.lift_correct hx (by decide) s hs rfl
  refine ⟨j, u, hu.transfer refinement, ?_, ?_⟩
  · have hm : u.heap = t.memory := congrArg State.memory hview
    exact ⟨by simpa [Post, Refinement.view, hm] using hsorted,
      by simpa [Refinement.view, hm] using hperm,
      by simpa [Refinement.view, hm] using hframe⟩
  · dsimp [budget, Refinement.view, remaining, Refinement.slot] at *
    omega

/-- The generated verification conditions for the displayed source program are discharged. -/
theorem verification (s : Store) (h : Refinement.Ready s) :
    VC sourceProgram (fun t _ => Post s t) s (budget (s.vars .word remaining.name)) :=
  correct.vc s h

/-- The canonical fuel-free executable uses the source compiler and VCG. -/
def method : Method where
  body := sourceProgram
  requires := Refinement.Ready
  ensures := Post
  budget s := budget (s.vars .word remaining.name)
  verification := VC.contract _ _ _ _ verification

def input (xs : List Nat) : Store where
  vars ty name := if ty = .word ∧ name = remaining.name then xs.length else 0
  heap := ofList xs

private theorem contents_input (xs : List Nat) : contents (ofList xs) 0 xs.length = xs := by
  have get : ∀ n b i (hi : i < n),
      (contents (ofList xs) b n)[i]'(by simpa using hi) = ofList xs (b + i) := by
    intro n
    induction n with
    | zero => intro b i hi; omega
    | succ n ih =>
      intro b i hi
      cases i with
      | zero => rfl
      | succ i =>
        simpa [contents, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (b + 1) i (by omega)
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    rw [get _ _ _ hi']
    simp [ofList, List.getElem?_eq_getElem hi']

structure Result where
  values : List Nat
  steps : Nat

def run (xs : List Nat) : Result :=
  let result := method.run (input xs) (by
    change Refinement.Ready (input xs)
    simp [input, Refinement.Ready])
  ⟨contents result.2.heap 0 xs.length, result.1⟩

theorem run_correct (xs : List Nat) : (run xs).values.Pairwise (· ≤ ·) ∧
    (run xs).values.Perm xs ∧ (run xs).steps ≤ budget xs.length := by
  have h := method.correct (input xs) (by
    change Refinement.Ready (input xs)
    simp [input, Refinement.Ready])
  simpa [run, method, Post, input, Refinement.slot, Refinement.name, contents_input] using
    And.intro h.2.1.1 (And.intro h.2.1.2.1 h.2.2)

theorem quadratic (xs : List Nat) (hn : 1 ≤ xs.length) : (run xs).steps ≤ 70 * xs.length ^ 2 := by
  have h := (run_correct xs).2.2
  have : xs.length ≤ xs.length ^ 2 := by nlinarith
  dsimp [budget] at h
  nlinarith

/-- End-to-end theorem: the compiled instructions establish the same contract. -/
theorem ram_correct (s : State) (hs : Refinement.Ready (observe s)) :
    ∃ k t, Exec sourceProgram.compile s k t ∧ Post (observe s) (observe t) ∧
      k ≤ budget ((observe s).vars .word remaining.name) := correct.ram s hs

end AlgoLib.Experimental.RAM.Algorithms.InsertionSort
