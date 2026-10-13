/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Tactic
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Fin

/-!
# Pivot-partition helpers

Shared list lemmas for pivot-partitioning algorithms (`Quicksort`,
`Quickselect`, …).

These lemmas are purely about lists and finite sums. Each is stated at
its weakest natural generality: plain `α` for pure list-structure
facts, `PartialOrder α` where only antisymmetry/transitivity of `≤` is
used, and `LinearOrder α` where totality (`¬ x < p ↔ p ≤ x`) or
trichotomy is genuinely needed.
-/

namespace AlgoLib

open List

variable {α : Type*}

/-! ### Pure list structure (no order) -/

/-- Erasing a valid index from `head :: tail` leaves `tail.length`
elements, the `rest` of every uniform-pivot step lemma. -/
lemma length_eraseIdx_cons (head : α) (tail : List α)
    (i : Fin (head :: tail).length) :
    ((head :: tail).eraseIdx i).length = tail.length := by
  have hi := i.isLt
  simp only [List.length_cons] at hi
  simp [List.length_eraseIdx, Nat.lt_succ_iff.mp hi]

/-- `eraseIdx` gives back a permutation. -/
lemma perm_getElem_cons_eraseIdx
    (L : List α) (i : Fin L.length) :
    L.Perm (L[i] :: L.eraseIdx i) := by
  induction' i with i ih
  induction' L with hd tl ih generalizing i
  · aesop
  · rcases i with (_ | i) <;>
      simp_all +decide [List.eraseIdx]
    exact List.Perm.trans
      (List.Perm.cons _
        (ih _ <| by simpa using
          ‹i + 1 < List.length (hd :: tl)›))
      (List.Perm.swap ..)

/-- Counting accepting indices. The number of positions of `L`
whose element satisfies `P`, written as a `Fin`-indexed sum of
indicators, the pure list mathematics behind the list counting
principle `toPMF_randIdx_bind_countP`.

Proved by leaving the `Fin`-indexed world (`sum_ofFn` /
`ofFn_getElem_eq_map`) before inducting: a direct induction runs into
`Decidable`-instance motives that neither `rw` nor `simp` handle. -/
lemma sum_ite_getElem_eq_countP {β : Type*} [AddCommMonoidWithOne β]
    (L : List α) (P : α → Bool) :
    ∑ i : Fin L.length, (if P L[i] then (1 : β) else 0)
      = (L.countP P : β) := by
  simp only [Fin.getElem_fin]
  rw [← List.sum_ofFn,
    List.ofFn_getElem_eq_map L (fun a => if P a then (1 : β) else 0)]
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : P a
    · simp [h, add_comm]
    · simp [h]

/-! ### Sortedness (antisymmetry and transitivity) -/

section PartialOrder

variable [PartialOrder α]

/-- Two sorted permutations of each other are equal. -/
lemma eq_of_sortedLE_perm
    {l1 l2 : List α}
    (h1 : l1.SortedLE) (h2 : l2.SortedLE)
    (hp : l1.Perm l2) : l1 = l2 :=
  hp.eq_of_pairwise
    (fun _ _ _ _ hab hba =>
      le_antisymm hab hba)
    (sortedLE_iff_pairwise.mp h1)
    (sortedLE_iff_pairwise.mp h2)

/-- Concatenation `S1 ++ [p] ++ S2` is sorted when
`∀ x ∈ S1, x < p` and `∀ x ∈ S2, p ≤ x` and both
sublists are sorted. -/
lemma sorted_concat_pivot
    {S1 S2 : List α} {p : α}
    (h1 : S1.SortedLE) (h2 : S2.SortedLE)
    (hb1 : ∀ x ∈ S1, x < p)
    (hb2 : ∀ x ∈ S2, p ≤ x) :
    (S1 ++ [p] ++ S2).SortedLE := by
  rw [sortedLE_iff_pairwise]
  apply pairwise_append.mpr
  refine ⟨?_, sortedLE_iff_pairwise.mp h2,
    fun x hx y hy => ?_⟩
  · apply pairwise_append.mpr
    refine ⟨sortedLE_iff_pairwise.mp h1, pairwise_singleton _ _,
      fun x hx y hy => ?_⟩
    rw [mem_singleton.mp hy]
    exact (hb1 x hx).le
  · rcases mem_append.mp hx with hx1 | hxp
    · exact le_trans (hb1 x hx1).le (hb2 y hy)
    · rw [mem_singleton.mp hxp]; exact hb2 y hy

end PartialOrder

/-! ### Pivot partition (totality) -/

section LinearOrder

variable [LinearOrder α]

/-! ### The sorting specification

What we want to say about `Quicksort` is that it sorts. Sortedness is a
property, `List.SortedLE`, and a Dirac statement needs a value; the two
meet because "sorted, and a permutation of `L`" is satisfied by exactly
one list. That is a definite description, so it denotes, and `sortSpec L`
is what it denotes.

The definition mentions only the existence statement. The construction
that proves it lives inside the proof, where proof irrelevance makes it
unobservable: any two proofs of `exists_sortedLE_perm L` are
definitionally equal, so `sortSpec` cannot depend on which one is given.

Three facts are exported and nothing downstream needs more:
`sortedLE_sortSpec` (it is sorted), `sortSpec_perm` (it permutes `L`),
`eq_sortSpec` (it is the only such list). The price is that `sortSpec`
is noncomputable, which costs nothing for something that is never run —
`Quicksort` and `Quickselect` stay executable and `#eval`-able. -/

/-- Sorted permutations of a list are equal: the specification
"sorted, and a permutation of `L`" has at most one solution.

Stated in the shape the support-to-Dirac bridge
(`eq_pure_of_support_subsingleton`) asks for, since it is exactly the
hypothesis that pays for reading a support-tier theorem as a Dirac
one. -/
lemma sortedPerm_unique {L : List α} :
    ∀ x y : List α, (x.SortedLE ∧ x.Perm L) → (y.SortedLE ∧ y.Perm L) → x = y :=
  fun _ _ hx hy => eq_of_sortedLE_perm hx.1 hy.1 (hx.2.trans hy.2.symm)

/-- The specification has at least one solution. Proved by inserting
one element at a time into a sorted list; the construction is confined
to this proof and, by proof irrelevance, is invisible to `sortSpec`. -/
lemma exists_sortedLE_perm (L : List α) :
    ∃ S : List α, S.SortedLE ∧ S.Perm L := by
  induction L with
  | nil => exact ⟨[], by simp [sortedLE_iff_pairwise], Perm.refl []⟩
  | cons a l ih =>
    obtain ⟨S, hs, hp⟩ := ih
    exact ⟨S.orderedInsert (· ≤ ·) a,
      sortedLE_iff_pairwise.mpr
        ((sortedLE_iff_pairwise.mp hs).orderedInsert a _),
      (perm_orderedInsert _ a S).trans (hp.cons a)⟩

/-- The specification is a definite description: exactly one list is
sorted and a permutation of `L`. This is the statement `sortSpec`
denotes; the two halves are `exists_sortedLE_perm` and
`sortedPerm_unique`. -/
lemma existsUnique_sortedLE_perm (L : List α) :
    ∃! S : List α, S.SortedLE ∧ S.Perm L :=
  (exists_sortedLE_perm L).imp fun S h =>
    ⟨h, fun y hy => sortedPerm_unique y S hy h⟩

/-- The sorted list of `L`: the unique list that is sorted and a
permutation of `L` (see the section note). -/
noncomputable def sortSpec (L : List α) : List α :=
  (exists_sortedLE_perm L).choose

@[simp] lemma sortedLE_sortSpec (L : List α) : (sortSpec L).SortedLE :=
  (exists_sortedLE_perm L).choose_spec.1

@[simp] lemma sortSpec_perm (L : List α) : (sortSpec L).Perm L :=
  (exists_sortedLE_perm L).choose_spec.2

/-- Characterization: anything sorted and equivalent to `L` is
`sortSpec L`. Together with the two facts above this pins the
definition down completely, and it is the only fact about `sortSpec`
that any proof needs. -/
lemma eq_sortSpec {S L : List α} (hs : S.SortedLE) (hp : S.Perm L) :
    S = sortSpec L :=
  sortedPerm_unique S (sortSpec L) ⟨hs, hp⟩
    ⟨sortedLE_sortSpec L, sortSpec_perm L⟩

@[simp] lemma mem_sortSpec {a : α} {L : List α} : a ∈ sortSpec L ↔ a ∈ L :=
  (sortSpec_perm L).mem_iff

@[simp] lemma length_sortSpec (L : List α) : (sortSpec L).length = L.length :=
  (sortSpec_perm L).length_eq

@[simp] lemma sortSpec_nil : sortSpec ([] : List α) = [] :=
  (eq_sortSpec (by simp [sortedLE_iff_pairwise]) (Perm.refl [])).symm

/-- The `< pivot` side when partitioning `L` around the pivot `L[i]`.
Reducible, so statements written with `pivotLT` unify definitionally
with the raw `filter`/`eraseIdx` form an algorithm unfolds to. -/
abbrev pivotLT (L : List α) (i : Fin L.length) : List α :=
  (L.eraseIdx i).filter (· < L[i])

/-- The `≥ pivot` side when partitioning `L` around the pivot `L[i]`. -/
abbrev pivotGE (L : List α) (i : Fin L.length) : List α :=
  (L.eraseIdx i).filter (· ≥ L[i])

/-- Filtering a list by `(· < p)` and `(· ≥ p)` gives complementary
sub-lists. -/
lemma length_filter_lt_ge (l : List α) (p : α) :
    (l.filter (· < p)).length + (l.filter (· ≥ p)).length = l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    by_cases h : hd < p
    · rw [List.filter_cons_of_pos (by simpa using h),
        List.filter_cons_of_neg (by simpa using not_le.mpr h)]
      show (tl.filter (· < p)).length + 1 +
        (tl.filter (· ≥ p)).length = tl.length + 1
      omega
    · rw [List.filter_cons_of_neg (by simpa using h),
        List.filter_cons_of_pos (by simpa using not_lt.mp h)]
      show (tl.filter (· < p)).length +
        ((tl.filter (· ≥ p)).length + 1) = tl.length + 1
      omega

/-- The two pivot sides partition the remainder: their lengths sum to
`|L| − 1`. -/
lemma pivot_split_length (L : List α) (i : Fin L.length) :
    (pivotLT L i).length + (pivotGE L i).length = (L.eraseIdx i).length :=
  length_filter_lt_ge _ _

/-- Filter-partition around a pivot permutes the
original list. -/
lemma perm_filter_partition
    (L : List α) (i : Fin L.length) :
    ((L.eraseIdx i).filter
        (fun x => decide (x < L[i])) ++
      [L[i]] ++
      (L.eraseIdx i).filter
        (fun x => decide (x ≥ L[i]))).Perm L := by
  have hc :
    (L.eraseIdx i).filter
      (fun x => !(decide (x < L[i]))) =
    (L.eraseIdx i).filter
      (fun x => decide (x ≥ L[i])) := by
    apply List.filter_congr
    intro x _
    by_cases h : x < L[i.val]
    · simp [h, not_le.mpr h]
    · simp [h, not_lt.mp h]
  have hf := filter_append_perm
    (fun x => decide (x < L[i])) (L.eraseIdx i)
  rw [hc] at hf
  have hmid :
    ((L.eraseIdx i).filter
        (fun x => decide (x < L[i])) ++
      [L[i]] ++
      (L.eraseIdx i).filter
        (fun x => decide (x ≥ L[i]))).Perm
    (L[i] ::
      ((L.eraseIdx i).filter
          (fun x => decide (x < L[i])) ++
        (L.eraseIdx i).filter
          (fun x =>
            decide (x ≥ L[i])))) := by
    simp only [append_assoc]
    exact perm_middle
  exact hmid.trans
    ((Perm.cons _ hf).trans
      (perm_getElem_cons_eraseIdx L i).symm)

/-!
### The pivot-partition identity, in two tiers

The mathematics is one fact: sorting both sides of a pivot partition
and concatenating gives a sorted permutation of the whole list. It is
stated once, as a property (`sortedPerm_concat_pivot`), and the
equational form used by Dirac proofs (`sortSpec_partition`) is derived
from it by the uniqueness characterization. The two correctness tiers
therefore share their mathematics and differ only in packaging.
-/

/-- Assembly step, property form. If the two recursive outputs are
sorted permutations of the two pivot sides, then placing the pivot
between them yields a sorted permutation of `L`.

This is the entire mathematical content of Quicksort's correctness, and
it is the shape a support-tier proof consumes: hypotheses about the
recursive calls, a conclusion about the branch, no specification value
anywhere. -/
lemma sortedPerm_concat_pivot (L : List α) (i : Fin L.length)
    {S1 S2 : List α}
    (h1 : S1.SortedLE) (hp1 : S1.Perm (pivotLT L i))
    (h2 : S2.SortedLE) (hp2 : S2.Perm (pivotGE L i)) :
    (S1 ++ [L[i]] ++ S2).SortedLE ∧ (S1 ++ [L[i]] ++ S2).Perm L := by
  refine ⟨sorted_concat_pivot h1 h2 (fun x hx => ?_) (fun x hx => ?_), ?_⟩
  · simpa using of_mem_filter (hp1.mem_iff.mp hx)
  · simpa using of_mem_filter (hp2.mem_iff.mp hx)
  · exact ((hp1.append (Perm.refl [L[i]])).append hp2).trans
      (perm_filter_partition L i)

/-- Assembly step, equational form: the sorted list splits around any
pivot as `sort(< pivot) ++ [pivot] ++ sort(≥ pivot)`.

Derived from `sortedPerm_concat_pivot` by `eq_sortSpec` — the property
determines the value. Oriented branch = spec (the concatenation on the
left), the `spec_transport` convention, so `dirac_finish` can rewrite a
collapsed Quicksort branch to the specification. -/
lemma sortSpec_partition (L : List α) (i : Fin L.length) :
    sortSpec (pivotLT L i) ++ [L[i]] ++ sortSpec (pivotGE L i) =
      sortSpec L :=
  have h := sortedPerm_concat_pivot L i (sortedLE_sortSpec _)
    (sortSpec_perm _) (sortedLE_sortSpec _) (sortSpec_perm _)
  eq_sortSpec h.1 h.2

/-!
### Partition size lemma for distinct lists

When the list `L` has no duplicates, the rank function
`i ↦ |{j ≠ i : L[j] < L[i]}|` is a bijection on `Fin L.length`.
This lets us reindex any sum over pivot choices by rank.

The proof uses `Finset.sum_equiv` with an equivalence constructed
from the injective rank function on a finite type.
-/

/-- The rank of element `i` in a nodup list: number of elements
strictly less than `L[i]`, excluding position `i`. -/
private noncomputable def rank (L : List α) (i : Fin L.length) : Fin L.length :=
  ⟨((Finset.univ.erase i).filter (fun j => L[j] < L[i])).card,
   by
    calc ((Finset.univ.erase i).filter (fun j => L[j] < L[i])).card
        ≤ (Finset.univ.erase i).card := Finset.card_filter_le _ _
      _ = L.length - 1 := by simp [Finset.card_erase_of_mem]
      _ < L.length := Nat.sub_lt (Fin.pos i) Nat.one_pos⟩

/-- The rank function equals the filter-length on the erased list. -/
private lemma rank_eq_filter_length (L : List α) (hnd : L.Nodup) (i : Fin L.length) :
    ((L.eraseIdx i).filter (· < L[i])).length = (rank L i).val := by
  unfold rank
  have h_filter_eq :
    List.toFinset
      (List.filter (fun x => x < L[i])
        (L.eraseIdx i)) =
    Finset.image (fun x => L[x])
      (Finset.filter (fun x => L[x] < L[i])
        (Finset.univ.erase i)) := by
    ext; simp [Finset.mem_image]
    constructor
    · intro h
      obtain ⟨k, hk⟩ :=
        List.mem_iff_get.mp h.1
      use ⟨if k.val < i.val then k.val
           else k.val + 1, by grind⟩
      generalize_proofs at *; grind
    · rintro ⟨j, ⟨hj₁, hj₂⟩, rfl⟩
      rw [List.mem_iff_get]
      simp_all +decide [Fin.ext_iff]
      use ⟨if j.val < i.val then j.val
           else j.val - 1, by grind⟩
      generalize_proofs at *; grind
  rw [← List.toFinset_card_of_nodup]
  · rw [h_filter_eq,
      Finset.card_image_of_injective _
        (fun x y hxy => by
          simpa [Fin.ext_iff] using
            List.nodup_iff_injective_get.mp
              hnd hxy)]
  · exact List.Nodup.filter _
      (hnd.eraseIdx _)

/-- The complement rank equals `L.length - 1 - rank`. -/
private lemma complement_rank_eq (L : List α) (hnd : L.Nodup) (i : Fin L.length) :
    ((L.eraseIdx i).filter (· ≥ L[i])).length =
      L.length - 1 - (rank L i).val := by
  have h_split :
    ((L.eraseIdx i).filter (· < L[i])).length +
      ((L.eraseIdx i).filter (· ≥ L[i])).length =
      L.length - 1 := by
    rw [length_filter_lt_ge (L.eraseIdx i) L[i]]
    simp +decide [List.length_eraseIdx]
  exact eq_tsub_of_add_eq
    (by linarith [rank_eq_filter_length L hnd i])

/-- The rank function is injective on nodup lists. -/
private lemma rank_injective (L : List α) (hnd : L.Nodup) :
    Function.Injective (rank L) := by
  intro i j hij
  by_cases h1 : L[i] < L[j]
  · -- L[i] < L[j]: rank i ⊂ rank j, contradiction
    have h_subset : Finset.filter (fun x => L[x] < L[i]) (Finset.univ.erase i) ⊂
        Finset.filter (fun x => L[x] < L[j]) (Finset.univ.erase j) := by
      constructor
      · grind
      · simp_all +decide [Finset.subset_iff]
        exact ⟨i, by aesop⟩
    have := Finset.card_lt_card h_subset
    simp_all +decide [rank]
  · by_cases h2 : L[j] < L[i]
    · -- L[j] < L[i]: rank j ⊂ rank i, contradiction
      have h_subset : Finset.filter (fun x => L[x] < L[i]) (Finset.univ.erase i) ⊇
          Finset.image id (Finset.filter (fun x => L[x] < L[j]) (Finset.univ.erase j)) ∪ {j} := by
        grind
      have := Finset.card_mono h_subset
      simp_all +decide
      simp [rank, Fin.ext_iff] at hij; omega
    · -- L[i] = L[j]: use nodup injectivity
      exact List.nodup_iff_injective_get.mp hnd <|
        le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

/-- The rank function as an equivalence on `Fin L.length` for nodup lists. -/
private noncomputable def rankEquiv (L : List α) (hnd : L.Nodup) : Fin L.length ≃ Fin L.length :=
  Equiv.ofBijective (rank L) (Finite.injective_iff_bijective.mp (rank_injective L hnd))

/-- Reindexing partition sizes by rank for nodup lists, general form:
any function of the two partition sizes can be re-summed over ranks.
Works in any `AddCommMonoid` (used with `ℚ` for Quicksort's exact
formula and with `ENNReal` for Quickselect's bound).

The RHS is a `Finset.range` sum: everything downstream of a rank
reindexing (`Finset.sum_range_succ`, `sum_range_reflect`, harmonic
closed forms) lives on range sums, so the `Fin`-to-range hop happens
once, here, and never at a call site.

Uses `Finset.sum_equiv` with the rank equivalence for a clean
bijective reindexing. -/
lemma nodup_partition_sum₂ {β : Type*} [AddCommMonoid β]
    (L : List α) (hnd : L.Nodup) (f : ℕ → ℕ → β) :
    (∑ i : Fin L.length,
      f ((L.eraseIdx i).filter
          (· < L[i])).length
        ((L.eraseIdx i).filter
          (· ≥ L[i])).length) =
    ∑ r ∈ Finset.range L.length,
      f r (L.length - 1 - r) := by
  rw [← Fin.sum_univ_eq_sum_range]
  -- Rewrite LHS summand in terms of rank, then reindex
  have h_eq : ∀ i : Fin L.length,
      f ((L.eraseIdx i).filter (· < L[i])).length
        ((L.eraseIdx i).filter (· ≥ L[i])).length =
      f (rank L i).val (L.length - 1 - (rank L i).val) := by
    intro i; rw [rank_eq_filter_length L hnd i, complement_rank_eq L hnd i]
  simp_rw [h_eq]
  exact Finset.sum_equiv (rankEquiv L hnd)
    (fun _ => by simp)
    (fun _ _ => rfl)

end LinearOrder

/-! ### Pivot-rank arithmetic -/

/-- Pascal's rule for `choose 2`: `C(n+1, 2) = n + C(n, 2)`. -/
lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right]

/-- Discrete convexity of `Nat.choose · 2`: along the line `a + b = k`,
the sum `a.choose 2 + b.choose 2` is maximized at the corners.
Equivalent to `a(a − 1) + b(b − 1) + 2ab = (a + b)(a + b − 1)`. -/
lemma choose_two_add_le (a b : ℕ) :
    a.choose 2 + b.choose 2 ≤ (a + b).choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hb : (b + 1).choose 2 = b.choose 2 + b := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]; linarith
    have hab : (a + (b + 1)).choose 2 = (a + b).choose 2 + (a + b) := by
      rw [show a + (b + 1) = (a + b) + 1 from rfl,
        Nat.choose_succ_succ, Nat.choose_one_right]; linarith
    rw [hb, hab]; omega

/-- Arithmetic core of max-side recursion bounds: recursing into the
larger side of a rank-`r` pivot costs at most `max r (n-1-r)`, and
summed over all ranks this is at most `3n²/4` (stated multiplied out:
`4·Σ ≤ 3n²`). Used for Quickselect's linear bound. -/
lemma sum_max_le : ∀ n : ℕ,
    4 * ∑ r ∈ Finset.range n, max r (n - 1 - r) ≤ 3 * n ^ 2
  | 0 => by simp
  | 1 => by simp
  | (m + 2) => by
      -- Peel the first and last summands: each contributes `m + 1`, and
      -- the middle re-indexes to the `m`-sum shifted by one.
      have hrec : ∑ r ∈ Finset.range (m + 2), max r (m + 1 - r) =
          (∑ r ∈ Finset.range m, max r (m - 1 - r)) + (3 * m + 2) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        have h1 : ∀ r ∈ Finset.range m,
            max (r + 1) (m + 1 - (r + 1)) = max r (m - 1 - r) + 1 := by
          intro r hr
          have := Finset.mem_range.mp hr
          omega
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
        omega
      have ih := sum_max_le m
      have hsq : (m + 2) ^ 2 = m ^ 2 + 4 * m + 4 := by ring
      show 4 * ∑ r ∈ Finset.range (m + 2), max r (m + 1 - r) ≤ 3 * (m + 2) ^ 2
      omega

end AlgoLib
