/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-! Register the custom simp attributes for the randomized-algorithms
framework.
These must be in a separate file from where they are used, per Lean 4
constraints.

* `pmf_simp_attr`: concrete probability computations
  (`tsum`, `bind_apply`, `uniformOfFintype_apply`, …).
* `expected_cost_simp`: bridge lemmas that decompose `expected_cost` /
  `runtime` through `TimeMT` combinators (`pure`, `bind`, `tick`, `lift`).
* `toPMF_simp`: lemmas that push `toPMF` through an algorithm branch
  (`toPMF_bind`, `toPMF_pure`, lawful `tick`, monad laws); the engine
  of the `toPMF_step` tactic in `AlgoLib.Infrastructure.Correctness.Correctness`.
  Tier-agnostic: the same set drives Dirac, distributional and
  support proofs.
* `spec_transport`: per-algorithm lemmas stating how a specification
  commutes with one branch of the algorithm (e.g. `orderStat_lt_branch`).
  Consumed by `dirac_finish`; the only lemmas a new algorithm must
  provide for its Dirac-correctness proof.
* `support_simp`: lemmas that unpack a support membership through an
  algorithm branch, turning `out ∈ (𝒟[…]).support` into existentials
  over the branch supports. The engine of `support_step`. Kept separate
  from `toPMF_simp` on purpose: `toPMF_simp` pushes `toPMF` inwards and
  leaves the membership intact, which is what pointwise and Dirac proofs
  want, while `support_simp` destructures it, which only support proofs
  want.
* `spec_preserve`: per-algorithm lemmas stating that a specification
  property survives one branch (e.g. "a sorted `<`-side and a sorted
  `≥`-side concatenate to a sorted whole"). The support-tier twin of
  `spec_transport`, and a `grind` set rather than a `simp` set, because
  these are implications and `simp` rewrites with equations. Consumed by
  `support_finish`. Tag with the forward modifier, `@[spec_preserve →]`:
  such a lemma has several hypotheses that arrive from the inductive
  hypotheses and a conclusion that is usually a conjunction, so its
  E-matching pattern must be built from the hypotheses. A backward
  (`apply`-style) rule is dead as soon as the conjunction is split or
  the goal sits under an `∃`.

  This is the same forward/equational split `Tactics.lean` already
  makes with `@[grind →]` for side conditions and `@[grind =]` for
  domain bridges; `spec_preserve` is the named, `only`-scoped version
  of the former.
-/

register_simp_attr pmf_simp_attr
register_simp_attr expected_cost_simp
register_simp_attr toPMF_simp
register_simp_attr spec_transport
register_simp_attr support_simp

register_grind_attr spec_preserve
