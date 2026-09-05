/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Syntax
import AlgoLib.Experimental.RAM.InsertionSort

/-!
# Insertion sort: code, termination, invariant, and a quadratic bound

The source below is executable Lean syntax. Its annotations generate verification
conditions; the compiler erases them and preserves exact RAM costs. The proof
is organized as a paper argument: insertion lemma, sorted-suffix invariant,
termination, then a recurrence for time. Low-level simulation lemmas live in
`InsertionSort.lean` and are reused as procedure specifications here.
-/

namespace AlgoLib.Experimental.RAM.Checked.Demo

open Source Reg

-- Source variable names are aliases for the finite RAM register bank.
abbrev i : Reg := count
abbrev j : Reg := cursor
abbrev x : Reg := key

/-- Insertion preserves the outer loop index. `entry` is a ghost snapshot. -/
def sameIndex (entry s : State) : Prop := s.regs i = entry.regs i

/-- Distance to the end, plus the last stop iteration. -/
def insertionVariant (s : State) : Nat :=
  if s.regs live = 0 then 0 else s.regs limit - s.regs next + 1

/-- Insert the saved key into the sorted suffix to the right of the hole. -/
def insertion : Stmt := imperative {
  while live > 0
    invariant sameIndex
    decreases insertionVariant
  {
    if next < limit {
      temp := A[next];
      if x <= temp {
        live := 0;
      } else {
        A[j] := temp;
        j := next;
        next := next + 1;
      }
    } else {
      live := 0;
    }
  }
  A[j] := x;
}

/-- Right-to-left insertion sort; the suffix to the right of `i` grows each pass. -/
def sorting : Stmt := imperative {
  limit := base + i;
  while i > 0
    invariant (fun entry s => s.regs i ≤ entry.regs i)
    decreases (fun s => s.regs i)
  {
    i := i - 1;
    j := base + i;
    x := A[j];
    next := j + 1;
    live := 1;
    call insertion;
  }
}

/-- The source compiler produces the previously verified insertion code exactly. -/
theorem insertion_compiles : insertion.compile = insertCode := rfl

/-- One compiled program, independent of the input or its annotations. -/
theorem sorting_compiles : sorting.compile = sortCode := rfl

/-- Generated insertion obligations: preserve the outer index and strictly
reduce the variant. An arbitrary postcondition on that index is allowed. -/
theorem insertion_vc (s : State) (Q : State → Prop)
    (hQ : ∀ t, t.regs i = s.regs i → Q t) : VC insertion Q s := by
  unfold insertion
  vcgen
  refine ⟨rfl, ?_, ?_⟩
  · intro t ht hl
    have hne : t.regs live ≠ 0 := by omega
    split_ifs
    · simp_all [sameIndex, insertionVariant, i, x]
    · simp_all [sameIndex, insertionVariant, i, j, x]
      omega
    · simp_all [sameIndex, insertionVariant, i]
  · intro t ht _
    exact hQ _ ht

/-- The outer index decreases; insertion preserves it. This verifies termination
from generated obligations, without supplying a runtime bound. -/
theorem sorting_vc (s : State) : VC sorting (fun _ => True) s := by
  unfold sorting
  vcgen
  intro t ht hpos
  apply insertion_vc
  intro u hu
  have heq : u.regs i = t.regs i - 1 := by simpa [i, j, x] using hu
  constructor <;> omega

/-- This is the executable: verification is performed once at definition time. -/
def insertionSort : TotalProgram := verified sorting sorting_vc

/-- The insertion lemma: adding one key to a sorted suffix preserves sortedness
and its multiset. This is ordinary list mathematics, with no machine state. -/
theorem insert_sorted (a : Nat) (xs : List Nat) (h : xs.Pairwise (· ≤ ·)) :
    (List.orderedInsert (· ≤ ·) a xs).Pairwise (· ≤ ·) ∧
      (List.orderedInsert (· ≤ ·) a xs).Perm (a :: xs) :=
  ⟨h.orderedInsert a xs, List.perm_orderedInsert _ _ _⟩

/-- Loop invariant: after processing `n` elements, the corresponding suffix is
sorted. The prefix is the actual sequence of outer-loop machine iterations. -/
theorem sorted_suffix (n remaining : Nat) (s : State)
    (hi : s.regs i = n + remaining)
    (he : s.regs limit = s.regs base + (n + remaining)) :
    ∃ k t, Prefix outerTest outerBody s k t ∧
      (contents t.memory (s.regs base + remaining) n).Pairwise (· ≤ ·) ∧
      (contents t.memory (s.regs base + remaining) n).Perm
        (contents s.memory (s.regs base + remaining) n) ∧
      k ≤ 4 * n ^ 2 + 8 * n := by
  obtain ⟨k, t, hx, hm, _, _, _, hk⟩ := outer_prefix n remaining s hi he
  refine ⟨k, t, hx, ?_, ?_, hk⟩
  · rw [hm, insertionSort_contents]
    exact List.pairwise_insertionSort _ _
  · rw [hm, insertionSort_contents]
    exact List.perm_insertionSort _ _

/-- One extra pass has at most `7n + 11` operations. This is the arithmetic
step for the recurrence `T(n+1) ≤ T(n) + 7n + 11`. -/
theorem quadratic_recurrence (n t : Nat) (h : t ≤ 4 * n ^ 2 + 8 * n) :
    t + (7 * n + 11) ≤ 4 * (n + 1) ^ 2 + 8 * (n + 1) := by nlinarith

/-- The executable's contract, for every initial memory and register state. -/
theorem insertionSort_correct (s : State) :
    let r := insertionSort.run s
    (contents r.2.memory (s.regs base) (s.regs i)).Pairwise (· ≤ ·) ∧
      (contents r.2.memory (s.regs base) (s.regs i)).Perm
        (contents s.memory (s.regs base) (s.regs i)) ∧
      (∀ a, a < s.regs base ∨ s.regs base + s.regs i ≤ a → r.2.memory a = s.memory a) ∧
      r.1 ≤ 4 * (s.regs i) ^ 2 + 8 * s.regs i + 2 := by
  obtain ⟨k, t, hx, hs, hp, hf, hk⟩ := sortCode_correct s
  have hrun := insertionSort.run_correct s
  change Exec sorting.compile s _ _ at hrun
  rw [sorting_compiles] at hrun
  obtain ⟨heq, ht⟩ := hrun.deterministic hx
  simpa only [heq, ht, i] using And.intro hs (And.intro hp (And.intro hf hk))

/-- Caller-facing convenience function: only the input, no fuel or proof argument. -/
def sort (xs : List Nat) : List Nat × Nat :=
  let (steps, final) := insertionSort.run (initial (ofList xs) 0 xs.length)
  (contents final.memory 0 xs.length, steps)

/-- info: ([1, 2, 3, 4], 71) -/
#guard_msgs in
#eval sort [3, 1, 4, 2]


/-- The accumulator in the following independent source-level example. -/
abbrev sum : Reg := key

/-- Paper invariant: `2*sum + j*(j+1)` is conserved. -/
def triangularInvariant (entry s : State) : Prop :=
  2 * s.regs sum + s.regs j * (s.regs j + 1) =
    2 * entry.regs sum + entry.regs j * (entry.regs j + 1)

/-- A complete contract proved by generated VCs, without reusing a RAM algorithm proof. -/
def summation : Method := method
  requires (fun _ => True)
  ensures (fun before after =>
    2 * after.regs sum = before.regs i * (before.regs i + 1))
  {
    sum := 0;
    j := i;
    while j > 0
      invariant triangularInvariant
      decreases (fun s => s.regs j)
    {
      sum := sum + j;
      j := j - 1;
    }
  }
  verified_by (by
    intro s _
    vcgen
    simp only [triangularInvariant, sum, j, i, ne_eq, reduceCtorEq, not_false_eq_true,
      Function.update_of_ne, Function.update_self, mul_zero, zero_add, true_and]
    constructor
    · intro t ht hpos
      refine ⟨?_, hpos⟩
      have : t.regs cursor - 1 + 1 = t.regs cursor := by omega
      nlinarith
    · intro t ht hz
      simpa [hz] using ht
  )

/-- info: (15, 18) -/
#guard_msgs in
#eval let (steps, final) := summation.run (initial (ofList []) 0 5)
      (final.regs sum, steps)

end AlgoLib.Experimental.RAM.Checked.Demo
