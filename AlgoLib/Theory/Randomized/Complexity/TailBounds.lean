/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Complexity.ExpectedCost
import AlgoLib.Theory.Randomized.Complexity.Variance

/-!
# Tail bounds

Markov's inequality for randomized computations: the probability that
the cost exceeds `k` is at most the expected cost divided by `k`.
This is the third analysis tier, next to correctness and expected
cost, an expected-cost theorem upgrades to a tail bound for free:

```
ℙ[cost m > k] ≤ 𝔼[cost m] / (k + 1)
```

## Main declarations

* `expected_cost_eq_expVal`: the bridge making every `expVal`
  estimate (Markov, Chebyshev) apply to running times
* `ℙ[cost m ≥ k]` / `ℙ[cost m > k]` notation
* `runtime_markov`, `runtime_markov_gt`, the first-moment cost tail
  bounds
* `runtime_chebyshev`: the second-moment cost tail bound

The event algebra (`prob`, singletons, complements, `bind`) and
Markov's inequality on `expVal` itself live one layer down in
`AlgoLib.Infrastructure.Randomness.Prob`, together with the
output-probability notation `ℙ_{M}[e = v]`.

Since costs are `ℕ`-valued, the strict form `runtime_markov_gt`
divides by `k + 1` (via `P(cost > k) = P(cost ≥ k + 1)`): it is both
sharper than the classical `E/k` and free of any `k ≠ 0` hypothesis.
-/

namespace AlgoLib

open Cslib.Algorithms.Lean
open ENNReal

/-- `expected_cost` is the `expVal` of the running time, the bridge
that lets every `expVal` estimate apply to costs. -/
lemma expected_cost_eq_expVal {α : Type} (p : PMF (TimeM ℕ α)) :
    expected_cost p = expVal p fun tm => (tm.time : ENNReal) := rfl

/-!
## Runtime tail bounds

`ℙ[cost m > k]` is the probability that the running time of `m`
exceeds `k`, mirroring the `𝔼[cost m]` notation. Like it, the
notation expands to the underlying `prob (TimedPMF m) {…}` form so
`simp`/`rw` can match lemmas without unfolding hints.
-/

/-- `ℙ[cost m ≥ k]`: probability that the running time of an
already-timed `m` is at least `k : ℕ`. -/
scoped macro "ℙ[cost " m:term:51 " ≥ " k:term "]" : term =>
  `(prob (TimedPMF $m) {tm | $k ≤ tm.time})

/-- `ℙ[cost m > k]`: probability that the running time of `m`
exceeds `k : ℕ`. -/
scoped macro "ℙ[cost " m:term:51 " > " k:term "]" : term =>
  `(prob (TimedPMF $m) {tm | $k < tm.time})

/-- `ℙ_{M}[cost e ≥ k]`: tail probability of the running time of the
monad-polymorphic algorithm `e`, instantiated at the random monad
`M`: the event `cost e ≥ k` under `ℙ_{M}`. -/
scoped macro "ℙ_{" M:term "}[cost " e:term:51 " ≥ " k:term:51 "]" : term =>
  `(prob (TimedPMF ($e : TimeMT ℕ $M _)) {tm | $k ≤ tm.time})

/-- `ℙ_{M}[cost e > k]`: strict-tail variant of
`ℙ_{M}[cost e ≥ k]`. -/
scoped macro "ℙ_{" M:term "}[cost " e:term:51 " > " k:term:51 "]" : term =>
  `(prob (TimedPMF ($e : TimeMT ℕ $M _)) {tm | $k < tm.time})

/-- Markov tail bound for runtimes: `P(cost ≥ k) ≤ E[cost] / k`.
Any expected-cost theorem yields a tail bound for free. -/
theorem runtime_markov
    {M : Type → Type} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {β : Type} (m : TimeMT ℕ M β) {k : ℕ} (hk : k ≠ 0) :
    ℙ[cost m ≥ k] ≤ 𝔼[cost m] / (k : ENNReal) := by
  have h := prob_ge_le_expVal_div (TimedPMF m)
    (fun tm => (tm.time : ENNReal)) (k := (k : ENNReal))
    (by exact_mod_cast hk) (ENNReal.natCast_ne_top k)
  rw [← expected_cost_eq_expVal] at h
  convert h using 2
  ext tm
  simp

/-- Strict Markov tail bound: `P(cost > k) ≤ E[cost] / (k + 1)`.
Since costs are `ℕ`-valued this is sharper than the classical `E/k`
and needs no `k ≠ 0` hypothesis. -/
theorem runtime_markov_gt
    {M : Type → Type} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {β : Type} (m : TimeMT ℕ M β) (k : ℕ) :
    ℙ[cost m > k] ≤ 𝔼[cost m] / (k + 1 : ENNReal) := by
  have h := runtime_markov m (k := k + 1) k.succ_ne_zero
  have hset : {tm : TimeM ℕ β | k < tm.time} =
      {tm : TimeM ℕ β | k + 1 ≤ tm.time} := by
    ext tm; exact Nat.lt_iff_add_one_le
  rw [hset]
  simpa using h

/-- Chebyshev tail bound for runtimes: the running time deviates
from its mean by `k` or more with probability at most `Var/k²`, the
second-moment sharpening of `runtime_markov`, and the entry point of
the variance tier for cost analyses. -/
theorem runtime_chebyshev
    {M : Type → Type} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {β : Type} (m : TimeMT ℕ M β) {k : ENNReal} (hk0 : k ≠ 0) (hktop : k ≠ ⊤) :
    prob (TimedPMF m) {tm | k ≤ (tm.time : ENNReal) ⊖ 𝔼[cost m]} ≤
      variance (TimedPMF m) (fun tm => (tm.time : ENNReal)) / k ^ 2 := by
  have h := chebyshev (TimedPMF m) (fun tm => (tm.time : ENNReal)) hk0 hktop
  rwa [← expected_cost_eq_expVal] at h

-- Smoke test: the notation elaborates and a tail bound is one line.
example {M : Type → Type} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (m : TimeMT ℕ M Unit) :
    ℙ[cost m > 9] ≤ 𝔼[cost m] / 10 := by
  have h := runtime_markov_gt m 9
  norm_num at h
  exact h

-- Smoke test: the second-moment bound instantiates just as cheaply.
example {M : Type → Type} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (m : TimeMT ℕ M Unit) :
    prob (TimedPMF m) {tm | 3 ≤ (tm.time : ENNReal) ⊖ 𝔼[cost m]} ≤
      variance (TimedPMF m) (fun tm => (tm.time : ENNReal)) / 9 := by
  have h := runtime_chebyshev m (k := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h

end AlgoLib
