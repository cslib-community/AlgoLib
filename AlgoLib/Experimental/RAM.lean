/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith

/-!
# Experimental RAM: ordinary programs, memory, and a cost

This is the original shallow reference model. For enforced operation counts
and a uniform sorting-existence theorem, use `RAM.Machine` and
`RAM.InsertionSort` in the `AlgoLib.Experimental.RAM.Checked` namespace.
The checked sorting proof reuses this file's *memory* specification only.

This is a small, shallow, unit-cost RAM model intended for algorithm proofs.
A program returns a value, a memory, and a natural-number operation count.
Use ordinary `do` notation and structural recursion; use `simp` to expose the
semantics of primitives. There is no instruction encoding or program counter
in a user's correctness proof. `Ensures` optionally packages correctness and
a time bound, and its bind rule adds the bounds of sequential computations.

Memory has natural-number addresses and natural-number words. Reads, writes,
word arithmetic, comparisons, and branches each cost one. Unwritten memory is
supplied by the caller (the examples use zero). Arithmetic is unbounded and
subtraction saturates: this is a unit-cost natural RAM, not a fixed-width word
RAM or a bit-complexity model. Function updates are a *specification* of memory;
the running time of Lean's evaluator is not the modeled running time.

This is a shallow interface, not a cost-safety type system: `pure`, bind, and
Lean expressions themselves cost zero. Algorithm authors must express machine
work using the charged primitives. In particular, `tick` records loop control
that structural recursion hides. Proof-only list views are never RAM operations.
`RAM.Machine` supplies a restricted instruction language; `RAM.InsertionSort`
proves correctness and time directly for a fixed program in that language.

The example is in-place insertion sort on `[base, base + n)`, traversed from
right to left. First sort the suffix, then insert its saved predecessor by
moving smaller words one cell to the left. Both the functional specification
and the quadratic bound concern this same RAM execution. Refinement to
`List.insertionSort` lets us reuse its sortedness and permutation theorems.
-/

namespace AlgoLib.Experimental.RAM

/-- Total, randomly addressed memory. -/
abbrev Memory := Nat → Nat

/-- The observable result of a RAM computation. -/
structure Result (α : Type) where
  value : α
  memory : Memory
  steps : Nat

/-- A terminating computation. Termination is checked by Lean at definition time. -/
abbrev Program (α : Type) := Memory → Result α

instance : Monad Program where
  pure a := fun m => ⟨a, m, 0⟩
  bind p f := fun m =>
    let r := p m
    let s := f r.value r.memory
    ⟨s.value, s.memory, r.steps + s.steps⟩

@[simp] theorem run_pure {α : Type} (a : α) (m : Memory) :
    (pure a : Program α) m = ⟨a, m, 0⟩ := rfl

@[simp] theorem run_bind {α β : Type} (p : Program α) (f : α → Program β)
    (m : Memory) :
    (p >>= f) m =
      ⟨(f (p m).value (p m).memory).value,
        (f (p m).value (p m).memory).memory,
        (p m).steps + (f (p m).value (p m).memory).steps⟩ := rfl

instance : LawfulMonad Program := LawfulMonad.mk'
  (id_map := by intros; funext m; rfl)
  (pure_bind := by intros; funext m; simp)
  (bind_assoc := by intros; funext m; simp [Nat.add_assoc])

/-- Explicit accounting for structural loop control or an already justified block. -/
def tick (k : Nat) : Program Unit := fun m => ⟨(), m, k⟩

/-- Read one word. -/
def read (a : Nat) : Program Nat := fun m => ⟨m a, m, 1⟩

/-- Write one word. -/
def write (a v : Nat) : Program Unit := fun m => ⟨(), Function.update m a v, 1⟩

/-- Word addition (including address arithmetic). -/
def add (x y : Nat) : Program Nat := fun m => ⟨x + y, m, 1⟩

/-- Saturating word subtraction. -/
def sub (x y : Nat) : Program Nat := fun m => ⟨x - y, m, 1⟩

/-- Word multiplication under the unit-cost convention. -/
def mul (x y : Nat) : Program Nat := fun m => ⟨x * y, m, 1⟩

/-- Compare two words. -/
def le (x y : Nat) : Program Bool := fun m => ⟨decide (x ≤ y), m, 1⟩

/-- Equality comparison on words (or addresses). -/
def eq (x y : Nat) : Program Bool := fun m => ⟨decide (x = y), m, 1⟩

/-- A charged branch; only the chosen computation is executed. -/
def branch {α : Type} (b : Bool) (yes no : Program α) : Program α := do
  tick 1
  if b then yes else no

/-- A small derived operation: two reads and two writes, costing four units. -/
def swap (a b : Nat) : Program Unit := do
  let x ← read a
  let y ← read b
  write a y
  write b x

/-- A total-correctness contract with a uniform upper bound on modeled time. -/
def Ensures {α : Type} (P : Memory → Prop) (p : Program α)
    (Q : α → Memory → Prop) (budget : Nat) : Prop :=
  ∀ m, P m → Q (p m).value (p m).memory ∧ (p m).steps ≤ budget

/-- Sequential composition adds time budgets and passes the intermediate assertion. -/
theorem Ensures.bind {α β : Type} {P : Memory → Prop} {Q : α → Memory → Prop}
    {R : β → Memory → Prop} {p : Program α} {f : α → Program β} {a b : Nat}
    (hp : Ensures P p Q a) (hf : ∀ x, Ensures (Q x) (f x) R b) :
    Ensures P (p >>= f) R (a + b) := by
  intro m hm
  obtain ⟨hq, ha⟩ := hp m hm
  obtain ⟨hr, hb⟩ := hf (p m).value (p m).memory hq
  exact ⟨hr, Nat.add_le_add ha hb⟩

/-- The one-cell read/write law illustrates simplification of a whole program. -/
theorem read_after_write (m : Memory) (a x : Nat) :
    ((do write a x; read a) : Program Nat) m =
      ⟨x, Function.update m a x, 2⟩ := by
  simp [write, read]

/-- A mathematical view of a contiguous block, used only in specifications. -/
def contents (m : Memory) (base : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => m base :: contents m (base + 1) n

@[simp] theorem contents_length (m : Memory) (base n : Nat) :
    (contents m base n).length = n := by
  induction n generalizing base <;> simp [contents, *]

/-- Updating an earlier cell leaves a suffix view unchanged. -/
theorem contents_update_before (m : Memory) (base n a x : Nat) (h : a < base) :
    contents (Function.update m a x) base n = contents m base n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [contents, Function.update_of_ne (by omega : base ≠ a)]
    rw [ih (base + 1) (by omega)]

/-- Insert a saved word into the following `n` cells, using `base` as the hole.
The entry test costs one; continuing a loop charges one for the predecessor
of its recursion counter. Address addition, read, comparison, branch, and
write are separate primitives. The recursion performs actual RAM writes. -/
def insert (base x : Nat) : Nat → Program Unit
  | 0 => do
    tick 1
    write base x
  | n + 1 => do
    tick 1
    let next ← add base 1
    let y ← read next
    let small ← le x y
    branch small (write base x) (do
      write base y
      tick 1
      insert next x n)

/-- In-place insertion sort. The recursion counter and saved word are local
register values; loading the input into memory is outside this routine's cost. -/
def insertionSort (base : Nat) : Nat → Program Unit
  | 0 => tick 1
  | n + 1 => do
    tick 1
    let x ← read base
    let next ← add base 1
    tick 1
    insertionSort next n
    insert base x n

@[simp] theorem insert_zero (m : Memory) (base x : Nat) :
    insert base x 0 m = ⟨(), Function.update m base x, 2⟩ := rfl

/-- Execution equations keep primitive expansion out of downstream proofs. -/
theorem insert_succ (m : Memory) (base x n : Nat) :
    insert base x (n + 1) m =
      if x ≤ m (base + 1) then ⟨(), Function.update m base x, 6⟩
      else
        let r := insert (base + 1) x n (Function.update m base (m (base + 1)))
        ⟨r.value, r.memory, 7 + r.steps⟩ := by
  by_cases h : x ≤ m (base + 1)
  · simp [insert, tick, add, read, le, branch, write, h]
  · simp [insert, tick, add, read, le, branch, write, h]
    omega

@[simp] theorem insertionSort_zero (m : Memory) (base : Nat) :
    insertionSort base 0 m = ⟨(), m, 1⟩ := rfl

theorem insertionSort_succ (m : Memory) (base n : Nat) :
    insertionSort base (n + 1) m =
      let s := insertionSort (base + 1) n m
      let r := insert base (m base) n s.memory
      ⟨r.value, r.memory, 4 + s.steps + r.steps⟩ := by
  simp [insertionSort, tick, add, read]
  omega

/-- Insertion modifies only its `n + 1` output cells. -/
theorem insert_frame (m : Memory) (base x n a : Nat)
    (h : a < base ∨ base + n < a) :
    (insert base x n m).memory a = m a := by
  induction n generalizing base m with
  | zero =>
    simp only [insert_zero]
    exact Function.update_of_ne (by omega) ..
  | succ n ih =>
    rw [insert_succ]
    split
    · exact Function.update_of_ne (by omega) ..
    · dsimp only
      rw [ih _ _ (by omega)]
      exact Function.update_of_ne (by omega) ..

/-- The key refinement: the imperative insertion has the familiar list meaning.
No sortedness precondition is needed to establish this equation. -/
theorem insert_contents (m : Memory) (base x n : Nat) :
    contents (insert base x n m).memory base (n + 1) =
      List.orderedInsert (· ≤ ·) x (contents m (base + 1) n) := by
  induction n generalizing base m with
  | zero => simp [contents]
  | succ n ih =>
    rw [insert_succ]
    split <;> rename_i h
    · simp only [contents, List.orderedInsert_cons, h, if_true]
      rw [Function.update_self]
      congr 1
      exact contents_update_before m (base + 1) (n + 1) base x (by omega)
    · dsimp only
      rw [contents, insert_frame _ _ _ _ base (Or.inl (by omega))]
      rw [Function.update_self, ih, contents_update_before _ _ _ _ _ (by omega)]
      simp [contents, h]

/-- Sorting preserves every cell outside its input block. -/
theorem insertionSort_frame (m : Memory) (base n a : Nat)
    (h : a < base ∨ base + n ≤ a) :
    (insertionSort base n m).memory a = m a := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    rw [insertionSort_succ]
    dsimp only
    rw [insert_frame _ _ _ _ _ (by omega), ih _ (by omega)]

/-- Refinement removes the RAM implementation from subsequent functional proofs. -/
theorem insertionSort_contents (m : Memory) (base n : Nat) :
    contents (insertionSort base n m).memory base n =
      List.insertionSort (· ≤ ·) (contents m base n) := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    rw [insertionSort_succ]
    dsimp only
    rw [insert_contents, ih]
    rfl

/-- Insertion takes at most seven units per inspected cell, plus its base case. -/
theorem insert_steps_le (m : Memory) (base x n : Nat) :
    (insert base x n m).steps ≤ 7 * n + 2 := by
  induction n generalizing base m with
  | zero => simp
  | succ n ih =>
    rw [insert_succ]
    split
    · dsimp only; omega
    · dsimp only
      have := ih (Function.update m base (m (base + 1))) (base + 1)
      omega

/-- An explicit quadratic upper bound, valid for every initial memory. -/
theorem insertionSort_steps_le (m : Memory) (base n : Nat) :
    (insertionSort base n m).steps ≤ 4 * n ^ 2 + 3 * n + 1 := by
  induction n generalizing base with
  | zero => simp
  | succ n ih =>
    rw [insertionSort_succ]
    dsimp only
    have hs := ih (base + 1)
    have hi := insert_steps_le (insertionSort (base + 1) n m).memory base (m base) n
    calc
      _ ≤ 4 + (4 * n ^ 2 + 3 * n + 1) + (7 * n + 2) := by omega
      _ ≤ 4 * (n + 1) ^ 2 + 3 * (n + 1) + 1 := by
        nlinarith

/-- A uniform `O(n²)` witness: constant eight, threshold one, independent of
the initial memory and base address. This form needs no asymptotics machinery. -/
theorem insertionSort_steps_le_quadratic (m : Memory) (base n : Nat) (hn : 1 ≤ n) :
    (insertionSort base n m).steps ≤ 8 * n ^ 2 := by
  have h := insertionSort_steps_le m base n
  have : n ≤ n ^ 2 := by nlinarith
  nlinarith

/-- The public contract: sorted output, the same multiset of input words,
unchanged memory outside the block, and a quadratic time bound, all at once. -/
theorem insertionSort_correct (m : Memory) (base n : Nat) :
    let r := insertionSort base n m
    (contents r.memory base n).Pairwise (· ≤ ·) ∧
      (contents r.memory base n).Perm (contents m base n) ∧
      (∀ a, a < base ∨ base + n ≤ a → r.memory a = m a) ∧
      r.steps ≤ 4 * n ^ 2 + 3 * n + 1 := by
  dsimp only
  refine ⟨?_, ?_, insertionSort_frame m base n, insertionSort_steps_le m base n⟩
  · rw [insertionSort_contents]
    exact List.pairwise_insertionSort _ _
  · rw [insertionSort_contents]
    exact List.perm_insertionSort _ _

/-- A client-facing Hoare contract: record the input as a list, then obtain
sortedness, permutation, and time through the compositional interface. -/
theorem insertionSort_ensures (base n : Nat) (xs : List Nat) :
    Ensures (fun m => contents m base n = xs) (insertionSort base n)
      (fun _ m => (contents m base n).Pairwise (· ≤ ·) ∧
        (contents m base n).Perm xs) (4 * n ^ 2 + 3 * n + 1) := by
  intro m hm
  obtain ⟨hs, hp, _, ht⟩ := insertionSort_correct m base n
  exact ⟨⟨hs, hm ▸ hp⟩, ht⟩

/-- An input memory with zero outside the list's addresses. -/
def ofList (xs : List Nat) : Memory := fun a => xs[a]?.getD 0

-- These examples run the memory operations and check their exact modeled costs.
example : contents (insertionSort 0 4 (ofList [3, 1, 4, 2])).memory 0 4 = [1, 2, 3, 4] := by
  decide

example : (insertionSort 0 4 (ofList [3, 1, 4, 2])).steps = 54 := by
  decide

-- Duplicates, a nonzero base, and sentinel cells outside the sorted block.
example :
    let r := insertionSort 2 4 (ofList [99, 88, 3, 1, 3, 2, 77])
    contents r.memory 0 7 = [99, 88, 1, 2, 3, 3, 77] := by
  decide

-- Empty and singleton blocks include their charged loop tests.
example (m : Memory) (base : Nat) : (insertionSort base 0 m).steps = 1 := rfl

example (m : Memory) (base : Nat) : (insertionSort base 1 m).steps = 7 := rfl

-- Best and worst traversal patterns execute different numbers of operations.
example : (insertionSort 0 4 (ofList [1, 2, 3, 4])).steps = 37 := by decide

example : (insertionSort 0 4 (ofList [4, 3, 2, 1])).steps = 67 := by decide

end AlgoLib.Experimental.RAM
