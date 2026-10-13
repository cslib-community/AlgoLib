/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Complexity.ExpectedCost
import AlgoLib.Theory.Randomized.Complexity.TailBounds
import AlgoLib.Theory.Randomized.Correctness.Correctness
import AlgoLib.Util.Partition
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Quicksort

This module implements a modular version of Quicksort.

## Architecture

A single `Quicksort` definition is parameterized by both `RandMonad`
(for pivot selection) and `MonadCost ℕ` (for cost tracking). By
instantiating with different `MonadCost` instances, the same code
serves as:

* Untimed specification (`M = PMF`, no-op `tick`)
* Timed specification (`M = TimeMT ℕ PMF`, accumulating `tick`)
* Executable (`M = IO`, no-op `tick`)
* Executable timed (`M = TimeMT ℕ IO`, accumulating `tick`)

## Main results

For `L` the input list and `n` its length, we have:

* `quicksort_correct`: generic correctness over any
  `LawfulRandMonad`: the output distribution is the Dirac mass at
  `sortSpec L`, the algorithm deterministically returns the sorted
  list (existential form: `quicksort_correct_spec`). Proved two further
  independent ways — `quicksort_correct_spec_of_branch_spec` (route A,
  the per-branch specification collapse) and `quicksort_sorted` plus
  `quicksort_correct_spec_of_support` (route B, the support tier and
  the bridge) — to exhibit the three correctness routes the framework
  offers. Each re-derives the theorem above without appealing to it.
* `quicksort_cost_le_real`: For arbitrary lists (possibly with
  duplicates), bounds the expected cost by `C(n,2)`, tight on
  all-equal inputs. Its `ENNReal` core also supplies the finiteness
  fact needed by the exact-formula proof.
* `quicksort_cost_exact`: Quantifies the exact expected
  cost over any `LawfulRandMonad`: sorting a list of `n` distinct
  elements requires exactly `2(n+1)H(n) - 4n` comparisons.

## Notation

The expected runtime of a timed computation is written with the
`𝔼_{M}[cost e]` (or `𝔼ℝ_{M}[cost e]` for a real value) notation
from `AlgoLib.Infrastructure.Complexity.ExpectedCost`. For example:

  `𝔼ℝ_{M}[cost Quicksort L]`

reads as "the expected runtime of Quicksort on `L`, run over the random
monad `M`, as a real number". The `| M` fixes the monad the polymorphic
`Quicksort` is instantiated at (timed via `TimeMT ℕ M`); the
`instRandMonadTimeMT` / `instMonadCostTimeMT` instances are picked up
automatically. Statements phrase the pivot partition with
`pivotLT L i` / `pivotGE L i` from `AlgoLib.Helpers.Partition`.
-/

namespace AlgoLib

open AlgoLib
open Cslib.Algorithms.Lean
open List

variable {α : Type} [LinearOrder α]

/-!
## Algorithm definition

A single implementation parameterized by `MonadCost ℕ M`.
The `MonadCost.tick` call is a no-op when `M` doesn't track cost,
and accumulates cost when `M = TimeMT ℕ M'`.
-/

/-- The main Quicksort function, polymorphic in the random monad `M`
and the cost monad `MonadCost ℕ M`. -/
def Quicksort
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    List α → M (List α)
  | [] => return []
  | L@(_::_) => do
      let idx ← randIdx L
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let L1 := rest.filter (· < pivot)
      let L2 := rest.filter (· ≥ pivot)
      MonadCost.tick rest.length
      let S1 ← Quicksort L1
      let S2 ← Quicksort L2
      return (S1 ++ [pivot] ++ S2)
  termination_by L => L.length
  decreasing_by all_goals grind

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

-- IO version (executable, untimed; `RandMonad IO` comes from
-- `AlgoLib.Infrastructure.Randomness.LawfulRandMonad`)
def Quicksort_IO : List ℕ → IO (List ℕ) := Quicksort

#eval Quicksort_IO [8,4,1,2]

-- PMF reading (noncomputable specification; an `example` suffices,
-- theorems are stated about `Quicksort` itself)
noncomputable example : List ℕ → PMF (List ℕ) := Quicksort

-- ----------------------------------------
-- Monad transformer version (timed)
-- ----------------------------------------

-- IO timed version (executable; `RandMonad (TimeMT ℕ M)` comes from
-- `AlgoLib.Infrastructure.Complexity.ExpectedCost`)
def Quicksort_IO_Timed : List ℕ → TimeMT ℕ IO (List ℕ) := Quicksort

#eval (Quicksort_IO_Timed [5, 4, 2, 1, 3, 6, 2, 1, 24, 6]).run

-- PMF timed reading (noncomputable specification)
noncomputable example : List ℕ → TimeMT ℕ PMF (List ℕ) := Quicksort

-- ----------------------------------------
-- Generic Correctness proof
-- ----------------------------------------

/-!
### Abbreviations

Deterministic branch abstraction for the
partition-and-recurse step at a given pivot index.
-/

/-- Branch: partition around pivot `L[i]` and
recurse with `Quicksort`. Used for both correctness
and complexity proofs. -/
private abbrev qs_branch
    (M : Type → Type) [Monad M] [RandMonad M] [MonadCost ℕ M]
    (L : List α) (i : Fin L.length) :
    M (List α) := do
  let rest := L.eraseIdx i
  let pivot := L[i]
  MonadCost.tick rest.length
  let S1 ← Quicksort (rest.filter (· < pivot))
  let S2 ← Quicksort (rest.filter (· ≥ pivot))
  return (S1 ++ [pivot] ++ S2)

-- ### Structural decomposition

/-- `Quicksort L` on a nonempty list decomposes as
`randIdx L >>= qs_branch M L`. -/
private lemma quicksort_eq_bind
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (head : α) (tail : List α) :
    (Quicksort (head :: tail) : M (List α)) =
    randIdx (head :: tail) >>=
      fun idx => qs_branch M (head :: tail) idx := by
  rw [Quicksort.eq_2 head tail]

/-!
### Generic correctness theorem

The specification is `sortSpec L`, the sorted list of `L`: the unique
list that is sorted and permutes `L` (`AlgoLib.Helpers.Partition`).

Quicksort is proved correct three times, once by each collapse the
infrastructure offers, to show that the framework does not prescribe a
proof. The three differ in how much of the specification the induction
has to carry:

* The default recipe, immediately below: one `dirac_correct` call,
  which collapses with `toPMF_randIdx_bind_dirac`. Every branch must
  produce the same named value, so the specification `sortSpec L` is
  present at every step. Driven by the equational transport lemma
  `sortSpec_partition_cons`. One line, and what a new algorithm follows
  by default.

* Route A: `toPMF_randIdx_bind_dirac_spec`. Each branch produces some
  deterministic output meeting the specification, and the branches are
  not required to agree; `sortedPerm_unique` restores the agreement at
  the collapse. The induction carries a witness but never `sortSpec`.

* Route B: the support tier plus `eq_pure_of_support_subsingleton`. No
  value at all during the induction, because the support of the draw is
  a union and the branches are independent. Its branch obligation is
  literally the induction step of the textbook proof.

All three end at the same statement. `quicksort_correct_of_branch_spec`
and `quicksort_correct_of_support` close the loop by re-deriving the
first theorem from the other two, each without appealing to it.
-/

/-- Transport lemma for the default recipe: `sortSpec_partition`
restated in the `simp`-normal form a collapsed branch actually has
(`++ [x] ++` normalizes to `++ x :: ·`, `· ≥ p` to `p ≤ ·`), so
`dirac_finish` can fire it. -/
@[spec_transport]
private lemma sortSpec_partition_cons (L : List α) (i : ℕ) (h : i < L.length) :
    sortSpec ((L.eraseIdx i).filter (fun x => x < L[i])) ++ L[i] ::
      sortSpec ((L.eraseIdx i).filter (fun x => L[i] ≤ x)) =
      sortSpec L := by
  simpa [pivotLT, pivotGE] using sortSpec_partition L ⟨i, h⟩

/-- Correctness. For any lawful random monad and any lawful cost model,
`Quicksort` returns exactly the sorted list: its output distribution is
the Dirac mass at `sortSpec L`, independently of the random pivot
choices and of the ticks. -/
theorem quicksort_correct
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (L : List α) :
    𝒟_{M}[Quicksort L] = PMF.pure (sortSpec L) := by
  dirac_correct Quicksort

/-- The output is a sorted permutation of the input (existential
specification form of `quicksort_correct`). This is the textbook
statement, and it is equivalent to the Dirac form rather than weaker:
`sortedPerm_unique` turns the existential back into `sortSpec L`. -/
theorem quicksort_correct_spec
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (L : List α) :
    ∃ Output : List α,
      𝒟_{M}[Quicksort L] = pure Output ∧
      Output.SortedLE ∧ Output.Perm L :=
  ⟨sortSpec L, quicksort_correct L, sortedLE_sortSpec L, sortSpec_perm L⟩

-- ----------------------------------------
-- Route A: collapse from per-branch specifications
-- ----------------------------------------

/-!
### Route A

The same theorem with the specification value out of the induction but
a witness still in it. Each branch is shown to be deterministic and to
meet the specification — "sorted, and a permutation of the input" — and
the branches are not shown to agree. `toPMF_randIdx_bind_dirac_spec`
supplies the agreement from `sortedPerm_unique` at the moment of the
collapse.

Compared with the default recipe, this is what changes: the branch
obligation is `∃ Output, … = PMF.pure Output ∧ P Output` rather than an
equation against a named value, so the assembly step is
`sortedPerm_concat_pivot` (a property) instead of
`sortSpec_partition_cons` (an equation). Compared with route B, the
witness is still threaded through the induction; the pivot draw is
still a collapse rather than a union.
-/

/-- Correctness via the per-branch specification collapse: the output
is deterministic and is a sorted permutation of the input. -/
theorem quicksort_correct_spec_of_branch_spec
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (L : List α) :
    ∃ Output : List α,
      𝒟_{M}[Quicksort L] = PMF.pure Output ∧
      (Output.SortedLE ∧ Output.Perm L) := by
  induction L using Quicksort.induct with
  | case1 =>
    exact ⟨[], by rw [Quicksort.eq_1]; toPMF_step,
      by simp [sortedLE_iff_pairwise], Perm.refl []⟩
  | case2 head tail ih1 ih2 =>
    rw [quicksort_eq_bind head tail]
    -- The branches need not agree on a value; uniqueness of the
    -- specification is what lets the uniform draw collapse anyway.
    refine toPMF_randIdx_bind_dirac_spec sortedPerm_unique fun i => ?_
    obtain ⟨S1, h1, hs1, hp1⟩ := ih1 i
    obtain ⟨S2, h2, hs2, hp2⟩ := ih2 i
    refine ⟨S1 ++ [(head :: tail)[i]] ++ S2, ?_,
      sortedPerm_concat_pivot (head :: tail) i hs1 hp1 hs2 hp2⟩
    -- The branch is deterministic: peel the tick, then substitute the
    -- two recursive laws and let `pure` absorb the binds.
    toPMF_step qs_branch
    rw [h1, h2]
    toPMF_step

/-- Route A re-proves `quicksort_correct`, with no appeal to it and no
`@[spec_transport]` lemma: `eq_sortSpec` pins the witness down. -/
theorem quicksort_correct_of_branch_spec
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (L : List α) :
    𝒟_{M}[Quicksort L] = PMF.pure (sortSpec L) := by
  obtain ⟨Output, hOut, hs, hp⟩ :=
    quicksort_correct_spec_of_branch_spec (M := M) L
  rwa [eq_sortSpec hs hp] at hOut

-- ----------------------------------------
-- Route B: correctness via the support tier
-- ----------------------------------------

/-!
### Route B

The same theorem with no specification value in sight. The statement is
"every list `Quicksort` can output is a sorted permutation of the
input", a property of the support; the induction never carries a
witness, because the support of the pivot draw is the union of the
branch supports and the branches therefore never have to agree.

`support_step` does the framework's half: it peels the tick, pushes
`toPMF` through the two recursive calls, and turns the membership into
one binder per random choice and one per recursive call. What is left
is the mathematics, and it is exactly `sortedPerm_concat_pivot` —
the same lemma route A uses, before `eq_sortSpec` turns it into an
equation.
-/

-- The assembly step is Quicksort's `spec_preserve` lemma. It lives in
-- `Helpers` (Mathlib-only, no Infrastructure), so the tag is applied
-- here, where the framework consumes it. Forward, because its four
-- hypotheses arrive from the inductive hypotheses and its conclusion
-- is a conjunction.
attribute [spec_preserve →] sortedPerm_concat_pivot

/-- Correctness, support tier: every reachable output is a sorted
permutation of the input. -/
theorem quicksort_sorted
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (L : List α) (S : List α) (hS : S ∈ (𝒟_{M}[Quicksort L]).support) :
    S.SortedLE ∧ S.Perm L := by
  revert S
  induction L using Quicksort.induct with
  | case1 =>
    intro S hS
    rw [Quicksort.eq_1] at hS
    support_step at hS
    subst hS
    simp [sortedLE_iff_pairwise]
  | case2 head tail ih1 ih2 =>
    intro S hS
    rw [quicksort_eq_bind head tail] at hS
    -- `support_finish` unpacks the membership and then chains
    -- `sortedPerm_concat_pivot` forward against `ih1`/`ih2`. Written
    -- out it is: `obtain ⟨i, S1, h1, S2, h2, rfl⟩ := hS`, the two
    -- inductive hypotheses at `i`, and `exact sortedPerm_concat_pivot`.
    support_finish qs_branch at hS

/-- Route B's closing step: the support statement plus uniqueness of
the sorting specification gives determinism. The existential is the
theorem; no value was named to obtain it. -/
theorem quicksort_correct_spec_of_support
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (L : List α) :
    ∃ Output : List α,
      𝒟_{M}[Quicksort L] = PMF.pure Output ∧
      Output.SortedLE ∧ Output.Perm L :=
  eq_pure_of_support_subsingleton sortedPerm_unique (quicksort_sorted L)

/-- The routes meet: route B re-proves `quicksort_correct`, with no
appeal to it and no `@[spec_transport]` lemma. The witness produced by
the bridge is pinned down by `eq_sortSpec`, which is the same
uniqueness fact the default recipe hides inside the name `sortSpec`. -/
theorem quicksort_correct_of_support
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (L : List α) :
    𝒟_{M}[Quicksort L] = PMF.pure (sortSpec L) := by
  obtain ⟨Output, hOut, hs, hp⟩ := quicksort_correct_spec_of_support (M := M) L
  rwa [eq_sortSpec hs hp] at hOut

-- ----------------------------------------
-- Free Proof: Untimed Quicksort_PMF
-- ----------------------------------------

/-- Correctness at `M = PMF` (where `toPMF` is the identity). -/
theorem quicksort_correct_pmf (L : List α) :
    (Quicksort L : PMF (List α)) = PMF.pure (sortSpec L) :=
  quicksort_correct (M := PMF) L

/-- Timed PMF correctness for free: `TimeMT ℕ PMF` is itself a lawful
random monad (`instLawfulRandMonadTimeMT`), so the generic theorem
instantiates directly, since erasing the clock is its `toPMF`. -/
theorem quicksort_correct_timed_pmf (L : List α) :
    𝒟_{TimeMT ℕ PMF}[Quicksort L] = PMF.pure (sortSpec L) :=
  quicksort_correct (M := TimeMT ℕ PMF) L

-- ----------------------------------------
-- Generic Complexity Proof
-- ----------------------------------------

/-!
## Complexity

The expected cost obeys
`E[n] = (n-1) + (1/n) Σ_i (E[L1_i] + E[L2_i])`. Two results follow,
both by functional induction on `Quicksort`:

* bounding both recursive calls via discrete convexity of `C(·,2)`
  gives `E ≤ C(n,2)` for arbitrary lists (tight on all-equal inputs),
  which also yields finiteness of the expected cost;
* for distinct lists, rank reindexing turns the sum over pivots into
  the harmonic recurrence, which solves exactly to `2(n+1)H(n) − 4n`
  (`quicksort_cost_exact`).

The upper bound is stated in `ENNReal`, where no summability bookkeeping
is needed; the exact formula descends to `ℝ` via `toReal`, with
finiteness supplied by the `C(n,2)` bound.
-/

/-- The per-pivot step cost, named once so no proof ever restates
it: the deterministic partition work plus the two recursive calls. -/
private noncomputable def qsStepCost (M : Type → Type) [Monad M]
    [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (i : Fin L.length) : ENNReal :=
  ((L.eraseIdx i).length : ENNReal) +
    𝔼_{M}[cost Quicksort (pivotLT L i)] +
    𝔼_{M}[cost Quicksort (pivotGE L i)]

/-- The expected cost of `qs_branch` is
`|rest| + E[QS (pivotLT L i)] + E[QS (pivotGE L i)]`: peel the tick,
then the divide-and-conquer combinator does the rest. -/
private lemma expected_cost_qs_branch
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List α) (i : Fin L.length) :
    𝔼_{M}[cost qs_branch (TimeMT ℕ M) L i] = qsStepCost M L i := by
  unfold qs_branch qsStepCost
  cost_step
  rw [expected_cost_toPMF_seq₂, ← add_assoc]

/-- The empty list costs nothing. -/
lemma expected_cost_quicksort_nil
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] :
    𝔼_{M}[cost Quicksort ([] : List α)] = 0 := by
  rw [Quicksort.eq_1]; cost_step

/-- The expected cost of `Quicksort` on a nonempty list is the uniform
average of the branch costs:
`E[cost] = (1/n) * Σ_i (|rest_i| + E[L1_i] + E[L2_i])`. -/
lemma expected_cost_quicksort_step
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (head : α) (tail : List α) :
    𝔼_{M}[cost Quicksort (head :: tail)] =
    ((head :: tail).length : ENNReal)⁻¹ *
      ∑ i : Fin (head :: tail).length, qsStepCost M (head :: tail) i := by
  rw [quicksort_eq_bind head tail]
  exact expected_cost_uniform_step' (by simp)
    fun i => expected_cost_qs_branch (head :: tail) i

/-!
### The `C(n,2)` bound for arbitrary lists

The closed-form `2(n+1)H(n) − 4n` requires `L.Nodup` because duplicates
shift the partition distribution. For a list with repeated keys, the
worst case is all-equal inputs `L = [a, a, …, a]`:

  pivot = a, `L1 = []`, `L2 = rest` (length `n-1`, again all `a`)

so the recurrence degenerates to `T(n) = (n-1) + T(n-1)` and yields
`T(n) = n(n-1)/2 = C(n,2)` deterministically. This is the worst case
across all inputs and pivot sequences, so the expected cost on any list
is bounded by `C(n,2)`. Its `ENNReal` form also provides finiteness of
the expected cost for free. -/

/-- For an arbitrary list (possibly
with duplicates), the expected cost of `Quicksort` is bounded by
`L.length.choose 2`. Tight on the all-equal list `[a, a, …, a]`. -/
theorem quicksort_cost_le
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) :
    𝔼_{M}[cost Quicksort L] ≤
      (L.length.choose 2 : ENNReal) := by
  induction L using Quicksort.induct with
  | case1 =>
    rw [expected_cost_quicksort_nil]
    exact bot_le
  | case2 head tail ih1 ih2 =>
    rw [expected_cost_quicksort_step head tail]
    -- Every branch is bounded by Pascal + convexity of `C(·,2)`; the
    -- uniform average of the bounds closes the case.
    refine uniform_avg_le_of_forall fun i => ?_
    unfold qsStepCost
    have hrest := length_eraseIdx_cons head tail i
    have hsplit : (pivotLT (head :: tail) i).length +
        (pivotGE (head :: tail) i).length =
        tail.length := by
      rw [length_filter_lt_ge]
      exact hrest
    have hchoose : ((pivotLT (head :: tail) i).length).choose 2 +
        ((pivotGE (head :: tail) i).length).choose 2 ≤
        tail.length.choose 2 := by
      rw [← hsplit]
      exact choose_two_add_le _ _
    -- Pascal: `C(n,2) = tail.length + C(tail.length, 2)`.
    rw [show ((head :: tail).length.choose 2 : ENNReal) =
        (tail.length : ENNReal) + (tail.length.choose 2 : ENNReal) from by
      simp only [List.length_cons, choose_two_succ]; push_cast; ring]
    rw [add_assoc,
      show ((((head :: tail).eraseIdx i).length : ENNReal)) = (tail.length : ENNReal)
        from by rw [hrest]]
    refine add_le_add le_rfl (le_trans (add_le_add (ih1 i) (ih2 i)) ?_)
    rw [← Nat.cast_add]
    exact Nat.cast_le.mpr hchoose

/-- For an arbitrary list (possibly with duplicates), the expected cost of
`Quicksort` is at most `C(n,2)` comparisons. Real-valued corollary of
`quicksort_cost_le`. -/
theorem quicksort_cost_le_real
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) :
    𝔼ℝ_{M}[cost Quicksort L] ≤ L.length.choose 2 := by
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _)
    (quicksort_cost_le (M := M) L)
  simpa using this

/-- Runtime tail bound, for free: a Quicksort run exceeds `k`
comparisons with probability at most `C(n,2)/(k+1)`, by Markov's
inequality (`runtime_markov_gt`) applied to the `C(n,2)` bound. Any
expected-cost theorem upgrades this way. -/
theorem quicksort_runtime_tail
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) :
    ℙ_{M}[cost Quicksort L > k] ≤
      (L.length.choose 2 : ENNReal) / (k + 1) :=
  le_trans (runtime_markov_gt _ k)
    (ENNReal.div_le_div_right (quicksort_cost_le L) _)

/-- Finiteness of the expected cost, a free corollary of the `C(n,2)`
bound, no separate induction needed. Feeds the `toReal` steps of the
exact-formula theorem below. -/
lemma expected_cost_quicksort_ne_top
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] (L : List α) :
    𝔼_{M}[cost Quicksort L] ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
    (quicksort_cost_le L)

/-!
### The exact expected cost for distinct lists

We reuse Mathlib's harmonic number
`harmonic n = ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹`
(`Mathlib.NumberTheory.Harmonic.Defs`). The formula `2(n+1)H(n) − 4n`
requires `L.Nodup`: duplicates shift the partition distribution
(see the `C(n,2)` section above for the degenerate worst case).
-/

/-- The exact expected number of comparisons for
Quicksort on a list of `n` distinct elements:
`2(n+1)H(n) − 4n`. -/
def expected_qs_cost (n : ℕ) : ℚ :=
  2 * (n + 1) * harmonic n - 4 * n

@[simp] lemma expected_qs_cost_zero :
    expected_qs_cost 0 = 0 := by
  simp [expected_qs_cost, harmonic]

@[simp] lemma expected_qs_cost_one :
    expected_qs_cost 1 = 0 := by
  simp [expected_qs_cost, harmonic]; norm_num

/-- Summation identity for the recurrence:
`2 Σ_{i<n} C(i) = n·(C(n) − n + 1)`. -/
lemma expected_qs_sum_helper (n : ℕ) :
    (2 : ℚ) * ∑ i ∈ Finset.range n, expected_qs_cost i =
    (n : ℚ) * (expected_qs_cost n - (n : ℚ) + 1) := by
  induction n with
  | zero => simp [expected_qs_cost, harmonic]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    unfold expected_qs_cost
    rw [harmonic_succ]; push_cast
    have h_nz : (n : ℚ) + 1 ≠ 0 := by positivity
    field_simp; ring

/-- Exact expected complexity of Quicksort. Sorting a list of `n`
distinct elements costs exactly `2(n+1)H(n) − 4n` comparisons in
expectation. -/
theorem quicksort_cost_exact
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List α) (hnd : L.Nodup) :
    𝔼ℝ_{M}[cost Quicksort L] =
    (expected_qs_cost L.length : ℚ) := by
  revert hnd
  induction L using Quicksort.induct with
  | case1 =>
    intro _
    rw [expected_cost_quicksort_nil]
    simp
  | case2 head tail ih1 ih2 =>
    intro hnd
    rw [expected_cost_quicksort_step head tail]
    -- Each summand is finite (from the `C(n,2)` bound), so `toReal`
    -- distributes through the average.
    have hne : ∀ i : Fin (head :: tail).length,
        qsStepCost M (head :: tail) i ≠ ⊤ := fun i =>
      natCast_add_add_ne_top _ (expected_cost_quicksort_ne_top _)
        (expected_cost_quicksort_ne_top _)
    rw [toReal_uniform_avg hne]
    -- Rewrite each summand with the IH (in `ℝ`).
    have hterm : ∀ i : Fin (head :: tail).length,
        (qsStepCost M (head :: tail) i).toReal =
        (tail.length : ℝ) +
          ((expected_qs_cost
            ((pivotLT (head :: tail) i).length) : ℚ) : ℝ) +
          ((expected_qs_cost
            ((pivotGE (head :: tail) i).length) : ℚ) : ℝ) := by
      intro i
      unfold qsStepCost
      rw [toReal_natCast_add_add _ (expected_cost_quicksort_ne_top _)
          (expected_cost_quicksort_ne_top _),
        length_eraseIdx_cons head tail i,
        ih1 i ((hnd.eraseIdx _).filter _), ih2 i ((hnd.eraseIdx _).filter _)]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    -- Reindex by rank (`|L1_i| = rank i` for nodup lists).
    rw [nodup_partition_sum₂ (head :: tail) hnd
      (fun a b => (tail.length : ℝ) + ((expected_qs_cost a : ℚ) : ℝ) +
        ((expected_qs_cost b : ℚ) : ℝ))]
    simp only [List.length_cons]
    -- Split the sum; the reflected second cost sum equals the first.
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul,
      Finset.sum_range_reflect
        (fun r => ((expected_qs_cost r : ℚ) : ℝ)) (tail.length + 1),
      show (∑ r ∈ Finset.range (tail.length + 1),
          ((expected_qs_cost r : ℚ) : ℝ)) =
        ((∑ r ∈ Finset.range (tail.length + 1),
          expected_qs_cost r : ℚ) : ℝ) from by push_cast; rfl]
    -- Apply the summation identity and close with field arithmetic.
    have hsum : (∑ r ∈ Finset.range (tail.length + 1), expected_qs_cost r) =
        ((tail.length + 1) *
          (expected_qs_cost (tail.length + 1) - (tail.length + 1) + 1)) / 2 := by
      have h := expected_qs_sum_helper (tail.length + 1)
      push_cast at h
      linarith
    rw [hsum]
    have hn1 : ((tail.length : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-!
## Named corollaries at `M = PMF`
-/

/-- Expected number of comparisons performed by `Quicksort L`: the
expected runtime of the instrumented algorithm interpreted in `PMF`,
one tick per pivot comparison. -/
noncomputable def quicksortComparisons (L : List α) : ENNReal :=
  𝔼_{PMF}[cost Quicksort L]

/-- Expected cost is at most quadratic on arbitrary lists
(possibly with duplicates). -/
theorem quicksort_cost_le_pmf (L : List α) :
    quicksortComparisons L ≤ (L.length.choose 2 : ENNReal) :=
  quicksort_cost_le L

/-- Exact expected cost: sorting `n` distinct elements takes
exactly `2(n+1)·H(n) − 4n` comparisons in expectation. -/
theorem quicksort_cost_exact_pmf (L : List α) (hnd : L.Nodup) :
    (quicksortComparisons L).toReal = (expected_qs_cost L.length : ℚ) :=
  quicksort_cost_exact (M := PMF) L hnd

end AlgoLib
