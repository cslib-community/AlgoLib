/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import AlgoLib.Theory.Randomized.Complexity.TimedSemantics
import AlgoLib.Theory.Randomized.Randomness.Prob

/-!
# Expected Cost

This module defines the expected cost of a randomized computation
described by a `PMF` over `TimeM ℕ α` outcomes, and provides the
bridge lemmas that connect operational `TimeMT` code to
combinatorial cost analysis.

## Design

The expected cost is defined directly over `PMF (TimeM ℕ α)`,
using the `.time` field of `TimeM`. This avoids any intermediate
types or isomorphisms. `TimeM ℕ α` is the single canonical
representation of a timed result.

## Main declarations

* `expected_cost`: expected time cost of a `PMF (TimeM ℕ α)`
* Linearity lemmas for `expected_cost` through `bind` and uniform
  distributions
* Bridge lemmas connecting `TimeMT` combinators (`tick`, `lift`,
  `pure`, `bind`) composed with `LawfulRandMonad.toPMF` to
  `expected_cost` arithmetic
* `costPMF`: the cost distribution itself, the third reading of a
  cost analysis, with `costPMF_eq_pure_zero` / `costPMF_tick_bind`
  for deterministic-cost claims
* `𝔼[cost ·]` / `𝔼ℝ[cost ·]` notation and the `cost_step` /
  `runtime_simp` tactics
* the uniform-pivot recipes (`expected_cost_uniform_step`, the
  `uniform_avg_*` closing lemmas)

The generic probability functionals this file builds on (`expVal`,
`prob`, the `ℙ[·]` notation) live one layer down, in
`AlgoLib.Infrastructure.Randomness.Prob`; the semantics of the timed
transformer (erasure, the `TimeMT` lawful instances,
`LawfulMonadCost`) in `AlgoLib.Infrastructure.Complexity.TimedSemantics`.
-/

namespace AlgoLib

open Cslib.Algorithms.Lean
open ENNReal

/-!
## Core definition
-/

/-- Expected time cost of a computation described by a PMF over
`TimeM ℕ α` outcomes. Using `ENNReal` avoids all summability
concerns. -/
noncomputable def expected_cost {α : Type} (p : PMF (TimeM ℕ α)) : ENNReal :=
  ∑' (res : TimeM ℕ α), p res * (res.time : ENNReal)

/-!
## Basic lemmas
-/

@[simp, expected_cost_simp] lemma expected_cost_pure_zero {α : Type} (a : α) :
    expected_cost (PMF.pure ⟨a, 0⟩) = 0 := by
  unfold expected_cost; aesop

@[simp, expected_cost_simp] lemma expected_cost_pure_val {α : Type} (a : α) (t : ℕ) :
    expected_cost (PMF.pure ⟨a, t⟩ : PMF (TimeM ℕ α)) = (t : ENNReal) := by
  simp [expected_cost]

/-!
## Linearity
-/

/-- Linearity of expected cost through a PMF bind. -/
lemma expected_cost_bind {A : Type} {β : Type} (d : PMF A) (f : A → PMF (TimeM ℕ β)) :
    expected_cost (d >>= f) = ∑' a, d a * expected_cost (f a) := by
  unfold expected_cost
  have h_bind : ∀ res : TimeM ℕ β, (d >>= f) res = ∑' a : A, d a * (f a) res := by aesop
  simp +decide only [h_bind, ← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_comm]
  simp +decide only [← mul_assoc, ENNReal.tsum_mul_right]

/-- Expected cost under uniform pivot selection. -/
lemma expected_cost_uniform_bind {n : ℕ} [NeZero n] {β : Type}
    (f : Fin n → PMF (TimeM ℕ β)) :
    expected_cost (PMF.uniformOfFintype (Fin n) >>= fun i => f i) =
    (n : ENNReal)⁻¹ * ∑ i : Fin n, expected_cost (f i) := by
  rw [expected_cost_bind]
  simp +decide [Finset.mul_sum _ _ _, PMF.uniformOfFintype_apply, mul_comm]

/-- Averaging bound: if a total of `n` branch costs is at most `n * c`,
then the uniform average over the `n` branches is at most `c`.
This is the standard closing step of a uniform-pivot cost analysis.

Stated with `le_trans` in mind rather than `calc`: unifying against a
concrete sum `S` is a cheap metavariable assignment. The `n ≠ 0` side
condition is an autoparam (`by simp`), so call sites never spell it. -/
lemma uniform_avg_le {n : ℕ} {S c : ENNReal}
    (h : S ≤ n * c) (hn : n ≠ 0 := by simp) :
    (n : ENNReal)⁻¹ * S ≤ c := by
  refine le_trans (mul_le_mul' le_rfl h) ?_
  rw [← mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n),
    one_mul]

/-- The uniform average of `n` copies of the same value is that value,
the closing step of a cost analysis whose branches all cost the same. -/
lemma uniform_avg_const {n : ℕ} (c : ENNReal) (hn : n ≠ 0 := by simp) :
    (n : ENNReal)⁻¹ * ∑ _i : Fin n, c = c := by
  rw [Fin.sum_const, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n),
    one_mul]

/-- Closing average, `≤` form. Branches individually bounded by `c`
average to at most `c`. This is `uniform_avg_le` with the
`Finset.sum_le_sum`/`Fin.sum_const` bridge built in, so no call site
ever spells it. -/
lemma uniform_avg_le_of_forall {n : ℕ} {f : Fin n → ENNReal} {c : ENNReal}
    (h : ∀ i, f i ≤ c) (hn : n ≠ 0 := by simp) :
    (n : ENNReal)⁻¹ * ∑ i : Fin n, f i ≤ c := by
  refine uniform_avg_le (le_trans (Finset.sum_le_sum fun i _ => h i) ?_) hn
  rw [Fin.sum_const, nsmul_eq_mul]

/-- Closing average, `=` form. Branches that individually cost `c`
average to exactly `c`. This is `uniform_avg_const` with the
`Finset.sum_congr` rewrite-under-a-binder built in. -/
lemma uniform_avg_eq_of_forall {n : ℕ} {f : Fin n → ENNReal} {c : ENNReal}
    (h : ∀ i, f i = c) (hn : n ≠ 0 := by simp) :
    (n : ENNReal)⁻¹ * ∑ i : Fin n, f i = c := by
  rw [Finset.sum_congr rfl fun i _ => h i]
  exact uniform_avg_const c hn

/-!
## Bridge lemmas: `toPMF`-composed helpers

These lemmas decompose `expected_cost (toPMF (… : TimeMT).run)`
through the various `TimeMT` combinators.
-/

/-- `expected_cost` of a `TimeMT.lift` is `0` (no ticks). -/
@[expected_cost_simp] lemma expected_cost_lift
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α : Type} (m : M α) :
    expected_cost
      (inst.toPMF (TimeMT.lift m : TimeMT ℕ M α).run) =
      0 := by
  rw [expected_cost]
  have h_zero : ∀ res : TimeM ℕ α,
      (inst.toPMF (TimeMT.lift m).run) res * (res.time : ENNReal) = 0 := by
    intro res
    by_cases h : res.time = 0 <;> simp_all +decide [TimeMT.lift]
    rw [inst.toPMF_map]; erw [PMF.map_apply]; aesop
  aesop

/-- `expected_cost` of `TimeMT.tick t` is `t`. -/
@[expected_cost_simp] lemma expected_cost_tick
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] (t : ℕ) :
    expected_cost
      (inst.toPMF (TimeMT.tick t : TimeMT ℕ M Unit).run) =
      (t : ENNReal) := by
  convert expected_cost_pure_val () t
  exact inst.toPMF_pure _

/-- Shifting all time values by a constant `c` shifts the
expected cost by `c`. -/
lemma expected_cost_shift
    {β : Type} (p : PMF (TimeM ℕ β)) (c : ℕ) :
    expected_cost
      (p >>= fun tm => PMF.pure ⟨tm.ret, c + tm.time⟩) =
      (c : ENNReal) + expected_cost p := by
  convert expected_cost_bind p _
  simp +decide [expected_cost]
  simp +decide [mul_add, Summable.tsum_add]
  simp +decide [mul_comm, ENNReal.tsum_mul_left]

/-- Core decomposition: expected cost through a `TimeMT ℕ M`
bind equals the cost of the first part plus the continuation
cost, weighted by the distribution of the first part. -/
lemma expected_cost_toPMF_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type}
    (m : TimeMT ℕ M α) (f : α → TimeMT ℕ M β) :
    expected_cost (inst.toPMF (m >>= f).run) =
      expected_cost (inst.toPMF m.run) +
        ∑' (tm : TimeM ℕ α),
          (inst.toPMF m.run) tm *
            expected_cost
              (inst.toPMF (f tm.ret).run) := by
  have h1 : inst.toPMF (m >>= f).run =
      (inst.toPMF m.run) >>= fun tm1 =>
        (inst.toPMF (f tm1.ret).run) >>= fun tm2 =>
          PMF.pure ⟨tm2.ret, tm1.time + tm2.time⟩ := by
    simp only [TimeMT.run_bind, inst.toPMF_bind, inst.toPMF_pure]
    rfl
  convert expected_cost_bind (inst.toPMF m.run)
    (fun tm1 =>
      (inst.toPMF (f tm1.ret).run) >>= fun tm2 =>
        PMF.pure ⟨tm2.ret, tm1.time + tm2.time⟩) using 1
  · grind
  · have h2 : ∀ tm1 : TimeM ℕ α,
        expected_cost
          (inst.toPMF (f tm1.ret).run >>= fun tm2 =>
            PMF.pure ⟨tm2.ret, tm1.time + tm2.time⟩) =
          tm1.time +
            expected_cost (inst.toPMF (f tm1.ret).run) := by
      intro tm1; apply expected_cost_shift
    simp +decide only [h2]
    simp +decide [mul_add, ENNReal.tsum_add, expected_cost]

/-- `expected_cost_toPMF_bind` when every continuation costs the
same: `E[m >>= f] = E[m] + c`. -/
lemma expected_cost_toPMF_bind_const
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (m : TimeMT ℕ M α) (f : α → TimeMT ℕ M β) {c : ENNReal}
    (h : ∀ a, expected_cost (inst.toPMF (f a).run) = c) :
    expected_cost (inst.toPMF (m >>= f).run) =
      expected_cost (inst.toPMF m.run) + c := by
  rw [expected_cost_toPMF_bind]
  simp only [h]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- `expected_cost` of `pure a` in `TimeMT` is `0`. -/
@[expected_cost_simp] lemma expected_cost_toPMF_pure
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α : Type} (a : α) :
    expected_cost
      (inst.toPMF (pure a : TimeMT ℕ M α).run) = 0 := by
  rw [TimeMT.run_pure, inst.toPMF_pure]
  exact expected_cost_pure_zero a

/-- When the first computation is a `lift m` (zero cost),
the expected cost of the bind is the weighted sum over the
return distribution of `m`. -/
@[expected_cost_simp] lemma expected_cost_toPMF_lift_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (m : M α) (f : α → TimeMT ℕ M β) :
    expected_cost
      (inst.toPMF (TimeMT.lift m >>= f).run) =
      ∑' (a : α), (inst.toPMF m) a *
        expected_cost (inst.toPMF (f a).run) := by
  simp +zetaDelta at *
  grind +suggestions

/-- When the first computation is `tick t`, the expected cost
is `t` plus the expected cost of the continuation. -/
@[expected_cost_simp] lemma expected_cost_toPMF_tick_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {β : Type} (t : ℕ) (f : Unit → TimeMT ℕ M β) :
    expected_cost
      (inst.toPMF (TimeMT.tick t >>= f).run) =
      (t : ENNReal) +
        expected_cost (inst.toPMF (f ()).run) := by
  have := @expected_cost_toPMF_bind
  specialize @this M ‹_› ‹_› ‹_› Unit β (TimeMT.tick t)
  convert this f using 1
  rw [show (inst.toPMF (TimeMT.tick t).run) =
    PMF.pure (⟨(), t⟩ : TimeM ℕ Unit) from ?_]
  · simp +decide [expected_cost, PMF.pure_apply]
  · exact inst.toPMF_pure _

/-- When the first computation is `pure a`, the expected cost
of the bind is the expected cost of `f a`. -/
@[expected_cost_simp] lemma expected_cost_toPMF_pure_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (a : α) (f : α → TimeMT ℕ M β) :
    expected_cost
      (inst.toPMF
        ((pure a : TimeMT ℕ M α) >>= f).run) =
      expected_cost (inst.toPMF (f a).run) := by
  simp +zetaDelta at *

/-- Re-labelling the returned value (keeping the clock) costs nothing:
`E[f <$> m] = E[m]`. `TimeMT`'s `Functor` maps only the `.ret` field,
so the time marginal is untouched. -/
@[expected_cost_simp] lemma expected_cost_toPMF_map
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (f : α → β) (m : TimeMT ℕ M α) :
    expected_cost (inst.toPMF ((f <$> m).run)) =
      expected_cost (inst.toPMF m.run) := by
  rw [TimeMT.run_map, inst.toPMF_map]
  show expected_cost ((inst.toPMF m.run).map _) = _
  rw [PMF.map, ← pmf_bind_eq, expected_cost_bind]
  unfold expected_cost
  exact tsum_congr fun tm => by
    rcases tm with ⟨a, t⟩
    simp [Function.comp]

/-- Pure post-processing costs nothing: `E[m >>= (pure ∘ g)] = E[m]`.
Lets `cost_step` erase the trailing `return (f x)` of a branch. -/
@[expected_cost_simp] lemma expected_cost_toPMF_bind_pure
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (m : TimeMT ℕ M α) (g : α → β) :
    expected_cost
      (inst.toPMF (m >>= fun a => (pure (g a) : TimeMT ℕ M β)).run) =
      expected_cost (inst.toPMF m.run) := by
  rw [expected_cost_toPMF_bind]
  simp only [expected_cost_toPMF_pure, mul_zero, tsum_zero, add_zero]

/-- Support-aware continuation bound: if every continuation reachable
from the support costs at most `c`, the bind costs at most the head
plus `c`, the recursive-call step of a cost analysis whose bound
depends on run invariants. -/
lemma expected_cost_toPMF_bind_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α β : Type} {m : TimeMT ℕ M α} {f : α → TimeMT ℕ M β} {c : ENNReal}
    (h : ∀ tm ∈ (inst.toPMF m.run).support,
      expected_cost (inst.toPMF (f tm.ret).run) ≤ c) :
    expected_cost (inst.toPMF (m >>= f).run) ≤
      expected_cost (inst.toPMF m.run) + c := by
  rw [expected_cost_toPMF_bind]
  refine add_le_add le_rfl ?_
  calc (∑' tm, (inst.toPMF m.run) tm *
        expected_cost (inst.toPMF (f tm.ret).run))
      ≤ ∑' tm, (inst.toPMF m.run) tm * c := by
        refine ENNReal.tsum_le_tsum fun tm => ?_
        by_cases hs : tm ∈ (inst.toPMF m.run).support
        · exact mul_le_mul' le_rfl (h tm hs)
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hs]
          simp
    _ = c := pmf_tsum_mul_const _ c

/-- Divide-and-conquer cost: two computations run in sequence and
combined by a pure function cost the sum of their costs, the cost
sibling of `mem_support_toPMF_seq₂` and `expVal_toPMF_seq₂`. -/
lemma expected_cost_toPMF_seq₂
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β γ : Type} (m₁ : TimeMT ℕ M α) (m₂ : TimeMT ℕ M β)
    (g : α → β → γ) :
    expected_cost (inst.toPMF (m₁ >>= fun a => m₂ >>= fun b =>
        (pure (g a b) : TimeMT ℕ M γ)).run) =
      expected_cost (inst.toPMF m₁.run) +
        expected_cost (inst.toPMF m₂.run) := by
  rw [expected_cost_toPMF_bind]
  simp only [expected_cost_toPMF_bind_pure, pmf_tsum_mul_const]

/-!
## Notation for expected runtime

* `TimedPMF m`:      distribution over `(value, time)` pairs obtained
  by interpreting `m : TimeMT ℕ M α` via a `LawfulRandMonad`.
* `𝔼[cost m]`:      `expected_cost (TimedPMF m) : ENNReal`, for an
  already-timed `m`. `cost` marks that the averaged quantity is the
  running time; expands to the underlying form so `simp`/`rw` match
  the bridge lemmas without unfolding hints.
* `𝔼ℝ[cost m]`    , the same as a real number, for closed-form
  bounds like `2(n+1)H(n) − 4n`.
* `𝔼_{M}[cost e]` / `𝔼ℝ_{M}[cost e]`: the forms to use with a
  monad-polymorphic algorithm `e` (the typical case): the expectation
  `𝔼_{M}` of the running-time random variable `cost e`, instantiating
  `e` at `TimeMT ℕ M`, where `instRandMonadTimeMT` and
  `instMonadCostTimeMT` are picked up automatically. -/

/-- The distribution over `(value, time)` pairs obtained by interpreting
a timed computation `m : TimeMT ℕ M α` via a `LawfulRandMonad` instance.
This is the object whose expected cost we analyze. -/
noncomputable abbrev TimedPMF
    {M : Type → Type} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] {α : Type}
    (m : TimeMT ℕ M α) : PMF (TimeM ℕ α) :=
  inst.toPMF m.run

/-- `𝔼[cost m]` ≡ `expected_cost (TimedPMF m)`, the expected runtime
of an already-timed `m` as `ENNReal`. `cost` marks that the quantity
averaged is the running time; expands to the underlying form so
`simp`/`rw` can match bridge lemmas like `expected_cost_toPMF_bind`. -/
scoped macro "𝔼[cost " m:term "]" : term =>
  `(expected_cost (TimedPMF $m))

/-- `𝔼ℝ[cost m]` ≡ `(𝔼[cost m]).toReal`, the expected runtime of `m`
as `ℝ`. Use type ascription `(f L : TimeMT ℕ M _)` when `f` is polymorphic. -/
scoped macro "𝔼ℝ[cost " m:term "]" : term =>
  `((expected_cost (TimedPMF $m)).toReal)

/-- `𝔼_{M}[cost e]`: expected runtime (`ENNReal`) of the
monad-polymorphic algorithm `e`, instantiated at the random monad `M`
and timed via `TimeMT ℕ M`: the expectation `𝔼_{M}` of the
running-time random variable `cost e`; elaborates to
`expected_cost (TimedPMF (e : TimeMT ℕ M _))`. -/
scoped macro "𝔼_{" M:term "}[cost " e:term "]" : term =>
  `(expected_cost (TimedPMF ($e : TimeMT ℕ $M _)))

/-- `𝔼ℝ_{M}[cost e]`: real-valued expected runtime of the
monad-polymorphic algorithm `e` at the random monad `M`. -/
scoped macro "𝔼ℝ_{" M:term "}[cost " e:term "]" : term =>
  `((expected_cost (TimedPMF ($e : TimeMT ℕ $M _))).toReal)

/-!
### Arithmetic cleanups in `expected_cost_simp`

After peeling a `pure` reduces a continuation to `0`, the surrounding
`mul_zero / tsum_zero / add_zero` should collapse automatically so
that `cost_step` produces a clean form.
-/

attribute [expected_cost_simp] mul_zero zero_mul add_zero zero_add
attribute [expected_cost_simp] tsum_zero
attribute [expected_cost_simp] Nat.cast_one Nat.cast_zero

/-!
## Automation tactics

These tactics chain the bridge lemmas (`expected_cost_toPMF_pure`,
`…_pure_bind`, `…_tick_bind`, `…_lift_bind`, `expected_cost_tick`,
`expected_cost_lift`) tagged with `@[expected_cost_simp]`. They peel
off `TimeMT` combinators from the head of a computation until either
the cost is fully computed or only an opaque recursive call remains
(to be handled by induction).

### Example

```
lemma my_algo_cost : 𝔼[cost (myAlgo n : TimeMT ℕ M _)] = ... := by
  rw [myAlgo.eq_def]   -- unfold the algorithm
  cost_step            -- peel `tick`/`lift`/`pure`/`bind` away
  ...                  -- handle the recursive part
```
-/

/-- `cost_step` peels one or more `TimeMT` combinators off the head of
an `𝔼[cost ·]` expression by chaining the `expected_cost_simp` set.

This rewrites:
* `𝔼[cost tick t >>= f]`  ↦  `t + 𝔼[cost f ()]`
* `𝔼[cost lift m >>= f]`  ↦  `∑' a, toPMF m a * 𝔼[cost f a]`
* `𝔼[cost pure a >>= f]`  ↦  `𝔼[cost f a]`
* `𝔼[cost pure a]`        ↦  `0`
* `𝔼[cost tick t]`        ↦  `t`
* `𝔼[cost lift m]`        ↦  `0`

When an extra rewrite is needed (e.g. unfolding a recursive call),
combine with `simp only [expected_cost_simp, my_lemma]` directly.

The leading `dsimp` clears the `have`/`let` redexes that do-notation
`let`s desugar to, so `unfold my_branch; cost_step` works on branches
written with local `let`s.

Accepts a location (`cost_step at h`), and an algorithm name:
`cost_step myAlgo` first unfolds one layer of `myAlgo` via its
equation lemmas, so a non-recursive case's cost proof is the single
call `cost_step myAlgo` with no `myAlgo.eq_1` spelled anywhere. -/
scoped syntax "cost_step" (Lean.Parser.Tactic.location)? : tactic

@[inherit_doc tacticCost_step_] scoped syntax "cost_step " colGt ident
    (Lean.Parser.Tactic.location)? : tactic

scoped macro_rules
  | `(tactic| cost_step) =>
    `(tactic| ((try dsimp only []); simp only [expected_cost_simp]))
  | `(tactic| cost_step $loc:location) =>
    `(tactic| ((try dsimp only [] $loc:location); simp only [expected_cost_simp] $loc:location))
  | `(tactic| cost_step $f:ident) =>
    `(tactic| (simp only [$f:ident]; cost_step))
  | `(tactic| cost_step $f:ident $loc:location) =>
    `(tactic| (simp only [$f:ident] $loc:location; cost_step $loc:location))

/-- `runtime_simp` is the combined normalizer: peels `TimeMT` combinators
with `expected_cost_simp`, then cleans up arithmetic/`PMF` weights via
`pmf_simp_attr`. Intended for fully-closed cost computations.
Accepts a location (`runtime_simp at h`). -/
scoped syntax "runtime_simp" (Lean.Parser.Tactic.location)? : tactic

scoped macro_rules
  | `(tactic| runtime_simp) =>
    `(tactic| ((try dsimp only []); simp only [expected_cost_simp, pmf_simp_attr]; try norm_num))
  | `(tactic| runtime_simp $loc:location) =>
    `(tactic|
      ((try dsimp only [] $loc:location);
       simp only [expected_cost_simp, pmf_simp_attr] $loc:location;
       try norm_num))

/-!
## Uniform-pivot recipes

The two lemmas below package the algorithm-independent steps of a
uniform-pivot cost analysis, so that a new algorithm's step lemma is
one `rw` plus its branch decomposition:

```
lemma expected_cost_myAlgo_step ... :
    𝔼[cost (myAlgo (x :: xs) : TimeMT ℕ M _)] =
    ((x :: xs).length : ENNReal)⁻¹ * ∑ i, (branch cost i) := by
  rw [myAlgo_timed_eq_bind, expected_cost_uniform_step]
  congr 1
  exact Finset.sum_congr rfl fun i _ => expected_cost_myAlgo_branch ..
```
-/

/-- Uniform-pivot step. The expected cost of
`randIdx L >>= branch` is the uniform average of the branch
costs: the one-step recurrence `E = (1/n) · Σᵢ E[branch i]`.

Stated on the instance form `(randIdx L hL : TimeMT ℕ M _)`, exactly
the term a goal contains after `rw [myAlgo.eq_def]`, so no `show` or
re-association lemma is ever needed. -/
lemma expected_cost_uniform_step
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} (hL : 0 < L.length)
    (f : Fin L.length → TimeMT ℕ M β) :
    𝔼[cost (randIdx L hL : TimeMT ℕ M _) >>= f] =
    (L.length : ENNReal)⁻¹ * ∑ i : Fin L.length, 𝔼[cost f i] := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  show expected_cost (inst.toPMF
    (TimeMT.lift (randIdx L hL : M _) >>= f).run) = _
  cost_step
  rw [inst.toPMF_randIdx, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]

/-- `expected_cost_uniform_step` in hypothesis form: supply the branch
costs and get the recurrence. An algorithm's entire step lemma becomes
`rw [algo_eq_bind]; exact expected_cost_uniform_step' _ branch_lemma`. -/
lemma expected_cost_uniform_step'
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} (hL : 0 < L.length)
    {f : Fin L.length → TimeMT ℕ M β} {c : Fin L.length → ENNReal}
    (h : ∀ i, 𝔼[cost f i] = c i) :
    𝔼[cost (randIdx L hL : TimeMT ℕ M _) >>= f] =
    (L.length : ENNReal)⁻¹ * ∑ i : Fin L.length, c i := by
  rw [expected_cost_uniform_step hL f]
  congr 1
  exact Finset.sum_congr rfl fun i _ => h i

/-- `randFin` variant of `expected_cost_uniform_step`, for algorithms
that draw from `Fin n` directly (e.g. reservoir sampling's
`1/(seen+1)` coin). Stated on the instance form, like
`expected_cost_uniform_step`. -/
lemma expected_cost_uniform_step_fin
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {β : Type} (n : ℕ) [NeZero n] (f : Fin n → TimeMT ℕ M β) :
    𝔼[cost (RandMonad.randFin n : TimeMT ℕ M _) >>= f] =
    (n : ENNReal)⁻¹ * ∑ i : Fin n, 𝔼[cost f i] := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  show expected_cost (inst.toPMF
    (TimeMT.lift (RandMonad.randFin n : M _) >>= f).run) = _
  cost_step
  rw [inst.toPMF_randFin, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]

/-- Distribute `toReal` through a uniform average of finite branch
costs. Feed the `≠ ⊤` side conditions from the algorithm's ENNReal
upper bound. -/
lemma toReal_uniform_avg {n : ℕ} {S : Fin n → ENNReal}
    (h : ∀ i, S i ≠ ⊤) :
    ((n : ENNReal)⁻¹ * ∑ i, S i).toReal = (n : ℝ)⁻¹ * ∑ i, (S i).toReal := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun i _ => h i]

/-!
### Descending to `ℝ`

The generic apparatus for the final `toReal` step of an exact-cost
proof: finiteness of the standard branch-cost shape `n + a + b`,
`toReal` distributed through it, and the one-line descent of an
ENNReal bound to a real bound.
-/

/-- The standard branch cost `n + a + b` (deterministic work plus
recursive calls) is finite when the recursive costs are. -/
lemma natCast_add_add_ne_top {a b : ENNReal} (n : ℕ)
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (n : ENNReal) + a + b ≠ ⊤ := by
  simp [ha, hb]

/-- Distribute `toReal` through the standard branch cost `n + a + b`. -/
lemma toReal_natCast_add_add {a b : ENNReal} (n : ℕ)
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    ((n : ENNReal) + a + b).toReal = n + a.toReal + b.toReal := by
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ha⟩) hb,
    ENNReal.toReal_add (ENNReal.natCast_ne_top n) ha, ENNReal.toReal_natCast]

/-- Descent. An `ENNReal` runtime bound becomes a real bound in one
step; the finiteness certificate is the bound itself. -/
lemma runtime_toReal_le
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] {α : Type}
    {m : TimeMT ℕ M α} {c : ENNReal}
    (h : 𝔼[cost m] ≤ c) (hc : c ≠ ⊤) :
    𝔼ℝ[cost m] ≤ c.toReal :=
  ENNReal.toReal_mono hc h

/-!
## The cost distribution

Beyond its expectation (`𝔼[cost ·]`) and its tail bounds
(`ℙ_runtime`), the running time of a computation has a law:
`costPMF m`, the third reading of a cost analysis. It is what a
determinism claim needs. `schwartzZippel_costPMF` and
`costPMF_shuffle` state that those algorithms cost `1` and `0` on
every run, not merely on average, which an expectation cannot
say. `CouponCollector` studies the same tier from the other side: it
builds a cost law directly (geometric stages composed by `bind`),
being a process whose program form awaits the sub-probability layer.
-/

/-- The cost distribution of a timed computation: the law of its
running time. -/
noncomputable def costPMF {M : Type → Type} [Monad M] [LawfulMonad M]
    [LawfulRandMonad M] {α : Type} (m : TimeMT ℕ M α) : PMF ℕ :=
  (TimedPMF m).map TimeM.time

/-- A vanishing mean forces a Dirac law at `0`. Costs are
`ℕ`-valued, so "free in expectation" and "free on every run" coincide:
this upgrades any `𝔼[cost …] = 0` theorem (every sampler has one)
to a statement about the cost law. -/
lemma costPMF_eq_pure_zero {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] {β : Type} {m : TimeMT ℕ M β}
    (h : 𝔼[cost m] = 0) : costPMF m = PMF.pure 0 := by
  have hzero : ∀ tm : TimeM ℕ β, tm.time ≠ 0 → TimedPMF m tm = 0 := by
    intro tm hne
    rcases mul_eq_zero.mp (ENNReal.tsum_eq_zero.mp h tm) with h1 | h2
    · exact h1
    · exact absurd (by exact_mod_cast h2 : tm.time = 0) hne
  ext k
  rw [costPMF, PMF.map_apply, PMF.pure_apply]
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    refine Eq.trans (tsum_congr fun tm => ?_) (PMF.tsum_coe (TimedPMF m))
    by_cases ht : tm.time = 0
    · rw [if_pos ht.symm]
    · rw [if_neg fun hc => ht hc.symm, hzero tm ht]
  · rw [if_neg hk]
    refine ENNReal.tsum_eq_zero.mpr fun tm => ?_
    by_cases ht : k = tm.time
    · rw [if_pos ht, hzero tm (by omega)]
    · rw [if_neg ht]

/-- Prefixing a `tick t` shifts the whole cost law by `t`. -/
lemma costPMF_tick_bind {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] {β : Type} (t : ℕ) (f : Unit → TimeMT ℕ M β) :
    costPMF ((TimeMT.tick t : TimeMT ℕ M Unit) >>= f) =
      (costPMF (f ())).map (t + ·) := by
  have h1 : TimedPMF ((TimeMT.tick t : TimeMT ℕ M Unit) >>= f) =
      (TimedPMF (f ())).bind fun tm => PMF.pure ⟨tm.ret, t + tm.time⟩ := by
    show inst.toPMF _ = _
    simp only [TimeMT.run_bind, TimeMT.run_tick, inst.toPMF_bind, inst.toPMF_pure,
      pmf_bind_eq, pmf_pure_eq, PMF.pure_bind]
  rw [costPMF, costPMF, h1, PMF.map_bind]
  simp only [PMF.pure_map]
  rw [PMF.map_comp]
  rfl

/-- A zero-cost draw whose continuation's cost law does not depend
on the drawn value leaves the law unchanged, the `randFin`/`randIdx`
step of a deterministic-cost analysis (use `randFin_timeMT` /
`randIdx_timeMT` to reach the `lift` form). -/
lemma costPMF_lift_bind_const {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] {α β : Type}
    (m : M α) (f : α → TimeMT ℕ M β) {q : PMF ℕ}
    (h : ∀ a, costPMF (f a) = q) :
    costPMF (TimeMT.lift m >>= f) = q := by
  have h1 : TimedPMF (TimeMT.lift m >>= f) =
      (inst.toPMF m).bind fun a => TimedPMF (f a) := by
    show inst.toPMF _ = _
    rw [TimeMT.run_bind, TimeMT.run_lift, map_eq_bind_pure_comp, bind_assoc,
      inst.toPMF_bind, pmf_bind_eq]
    refine congrArg _ (funext fun a => ?_)
    simp only [Function.comp_apply, pure_bind, inst.toPMF_bind, pmf_bind_eq,
      inst.toPMF_pure, pmf_pure_eq, zero_add]
    -- `⟨tm.ret, tm.time⟩ = tm` by structure eta, so this is `bind pure`.
    exact PMF.bind_pure _
  rw [costPMF, h1, PMF.map_bind]
  simp only [show ∀ a, (TimedPMF (f a)).map TimeM.time = costPMF (f a)
    from fun a => rfl, h]
  exact PMF.bind_const _ q

/-- Pure post-processing is invisible to the cost law, the `costPMF`
sibling of `expected_cost_toPMF_bind_pure`. -/
lemma costPMF_bind_pure {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] {α β : Type}
    (m : TimeMT ℕ M α) (g : α → β) :
    costPMF (m >>= fun a => (pure (g a) : TimeMT ℕ M β)) = costPMF m := by
  have h1 : TimedPMF (m >>= fun a => (pure (g a) : TimeMT ℕ M β)) =
      (TimedPMF m).bind fun tm => PMF.pure ⟨g tm.ret, tm.time⟩ := by
    show inst.toPMF _ = _
    rw [TimeMT.run_bind, inst.toPMF_bind, pmf_bind_eq]
    refine congrArg _ (funext fun tm => ?_)
    simp only [TimeMT.run_pure, pure_bind, inst.toPMF_pure, pmf_pure_eq,
      add_zero]
  rw [costPMF, costPMF, h1, PMF.map_bind]
  simp only [PMF.pure_map]
  rfl

/-- The expected cost is the mean of the cost distribution. -/
lemma expected_cost_eq_expVal_costPMF {M} [Monad M] [LawfulMonad M]
    [LawfulRandMonad M] {α : Type} (m : TimeMT ℕ M α) :
    𝔼[cost m] = expVal (costPMF m) (fun t => (t : ENNReal)) := by
  rw [costPMF, expVal_map]
  rfl

end AlgoLib
