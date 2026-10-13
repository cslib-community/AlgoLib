/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Randomness.Prob

/-!
# Sub-probability and Las Vegas retry: `SPMF`

`PMF` forces total mass `1`, so a genuine retry-until-success loop was
not a program the framework could express (objective 2g; the design
comparison lives in `archive/notes/spmf-design.md`. This file
implements its recommendation).

* The carrier is `SPMF := OptionT PMF`: total mass stays `1`, with
  `none` carrying the divergence probability, so the monad and
  its laws are free (`OptionT` of a lawful monad), and the type is
  equivalent to the textbook sub-probability monad
  `{f : α → ENNReal // ∑' f ≤ 1}` (missing mass ↦ `none`).
* `retry good p` is conditioning, not domain theory: the loop
  re-runs exactly the retryable failures (`some a` with `¬ good a`),
  so its law is `p` conditioned on `retryEvent good` = "success or
  divergence" (`PMF.filter`); the geometric series `∑ₖ rᵏ = (1−r)⁻¹`
  is absorbed by the normalization. When nothing can succeed or
  diverge the loop runs forever: `pure none`.
* `RetryMonad` makes `retry` a program primitive with one definition
  and two readings: under `IO` it is an actual loop (`retryIO`), under
  `SPMF` it is the conditional law.

## Main declarations / results

* `SPMF`, `SPMF.mass`, the carrier and its termination probability.
* `RandMonad (OptionT M)`: any polymorphic algorithm runs inside.
* `RetryMonad` with instances for `IO` and `SPMF`.
* `retry_run_some_of_good` / `retry_run_some_of_not_good`: the output
  law: good outcomes keep their probability, renormalized by
  `prob … (retryEvent good)`; non-good outcomes are impossible
  (one-sided correctness of the loop).
* `mass_retry_eq_one`: the Las Vegas theorem: retrying a total
  program with positive success probability terminates almost surely.

The cost reading (`TimeMT ℕ SPMF`, expected trials `1/p` via
`geometricTrials`) and the program-level coupon collector are the
intended next clients; the lawfulness bridge for an `M`-level `retry`
(`LawfulRetryMonad`) waits for them.
-/

namespace AlgoLib

open scoped ENNReal

/-- Sub-probability distributions: `PMF` over `Option α`, with `none`
the divergence event. The monad structure and laws are `OptionT`'s. -/
abbrev SPMF (α : Type) : Type := OptionT PMF α

/-- Any random monad lifts through `OptionT`; in particular every
`{M} [RandMonad M]` algorithm can be read in `SPMF` (and in
`OptionT IO`). -/
instance {M : Type → Type} [Monad M] [RandMonad M] : RandMonad (OptionT M) where
  randFin n := OptionT.lift (RandMonad.randFin n)

/-- The retry primitive: repeat `p` until the output satisfies
`good`. One definition, two readings: a genuine loop under `IO`, the
conditional law under `SPMF`. -/
class RetryMonad (M : Type → Type) where
  /-- Repeat `p` until its output satisfies `good`. -/
  retry {α : Type} (good : α → Bool) (p : M α) : M α

export RetryMonad (retry)

/-- The executable reading: an actual retry loop. (`partial` is honest here:
termination is a probabilistic statement, `mass_retry_eq_one`.) -/
partial def retryIO {α : Type} (good : α → Bool) (p : IO α) : IO α := do
  let a ← p
  if good a then pure a else retryIO good p

instance : RetryMonad IO := ⟨retryIO⟩

-- Executable smoke test: sample `[0, 100)` until the draw is ≥ 90.
#eval retryIO (fun n => n ≥ 90) (IO.rand 0 99)

namespace SPMF

variable {α : Type}

/-- The termination probability of a sub-probability program:
everything not on `none`. -/
noncomputable def mass (p : SPMF α) : ENNReal := 1 - p.run none

/-- Lifted programs never diverge. -/
@[simp] lemma run_lift_none (p : PMF α) :
    (OptionT.lift p : SPMF α).run none = 0 := by
  show (p >>= fun a => PMF.pure (some a)) none = 0
  rw [pmf_bind_eq, PMF.bind_apply]
  exact ENNReal.tsum_eq_zero.mpr fun a => by
    rw [PMF.pure_apply, if_neg (by simp), mul_zero]

/-- A lifted program keeps its law on the live outcomes. -/
@[simp] lemma run_lift_some (p : PMF α) (a : α) :
    (OptionT.lift p : SPMF α).run (some a) = p a := by
  show (p >>= fun a => PMF.pure (some a)) (some a) = p a
  rw [pmf_bind_eq, PMF.bind_apply, tsum_eq_single a fun b hb => by
    rw [PMF.pure_apply, if_neg (by simpa using Ne.symm hb), mul_zero]]
  rw [PMF.pure_apply, if_pos rfl, mul_one]

/-- Lifted programs are total. -/
@[simp] lemma mass_lift (p : PMF α) : mass (OptionT.lift p : SPMF α) = 1 := by
  rw [mass, run_lift_none]
  simp

/-- The event a retry loop conditions on: the run is not a retryable
failure: it either succeeded (`some a` with `good a`) or diverged
(`none`). -/
def retryEvent (good : α → Bool) : Set (Option α) :=
  {x | ∀ a, x = some a → good a}

@[simp] lemma none_mem_retryEvent (good : α → Bool) :
    none ∈ retryEvent good := fun a h => by cases h

@[simp] lemma some_mem_retryEvent {good : α → Bool} {a : α} :
    some a ∈ retryEvent good ↔ good a := by
  constructor
  · intro h
    exact h a rfl
  · intro h b hb
    cases hb
    exact h

open scoped Classical in
/-- Retry as conditioning. Re-running exactly the retryable
failures means the final law is `p` conditioned on `retryEvent good`;
if that event has no mass (the loop can neither succeed nor diverge)
the loop runs forever. -/
noncomputable def retry (good : α → Bool) (p : SPMF α) : SPMF α :=
  if h : ∃ x ∈ retryEvent good, p.run x ≠ 0 then
    OptionT.mk ((p.run).filter (retryEvent good) h)
  else
    OptionT.mk (PMF.pure none)

noncomputable instance : RetryMonad SPMF := ⟨retry⟩

/-- The output law on good outcomes: the attempt's probability,
renormalized by the probability of "success or divergence". -/
theorem retry_run_some_of_good {good : α → Bool} {p : SPMF α}
    (h : ∃ x ∈ retryEvent good, p.run x ≠ 0) {a : α} (ha : good a) :
    (retry good p).run (some a) =
      p.run (some a) / prob p.run (retryEvent good) := by
  rw [retry, dif_pos h]
  show (p.run.filter (retryEvent good) h) (some a) = _
  rw [PMF.filter_apply, Set.indicator_of_mem (some_mem_retryEvent.mpr ha),
    div_eq_mul_inv]
  rfl

/-- One-sided correctness of the loop: a non-good outcome is
impossible. -/
theorem retry_run_some_of_not_good {good : α → Bool} (p : SPMF α)
    {a : α} (ha : ¬ good a) :
    (retry good p).run (some a) = 0 := by
  rw [retry]
  split_ifs with h
  · show (p.run.filter (retryEvent good) h) (some a) = 0
    rw [PMF.filter_apply,
      Set.indicator_of_notMem (fun hc => ha (some_mem_retryEvent.mp hc)),
      zero_mul]
  · show (PMF.pure (none : Option α)) (some a) = 0
    rw [PMF.pure_apply, if_neg (by simp)]

/-- The Las Vegas theorem. Retrying a total program (`none` has
no mass) whose success has positive probability terminates almost
surely. -/
theorem mass_retry_eq_one {good : α → Bool} {p : SPMF α}
    (htotal : p.run none = 0)
    (hpos : ∃ a, good a ∧ p.run (some a) ≠ 0) :
    mass (retry good p) = 1 := by
  obtain ⟨a, ha, hane⟩ := hpos
  have h : ∃ x ∈ retryEvent good, p.run x ≠ 0 :=
    ⟨some a, some_mem_retryEvent.mpr ha, hane⟩
  rw [mass, retry, dif_pos h]
  have hnone : (p.run.filter (retryEvent good) h) none = 0 := by
    rw [PMF.filter_apply, Set.indicator_of_mem (none_mem_retryEvent good),
      htotal, zero_mul]
  show (1 : ENNReal) - (p.run.filter (retryEvent good) h) none = 1
  rw [hnone]
  simp

-- Smoke test: rejection sampling, draw from `Fin 6` until the draw
-- is nonzero; the loop terminates almost surely.
example : mass (retry (fun i : Fin 6 => decide (i ≠ 0))
    (RandMonad.randFin 6 : SPMF (Fin 6))) = 1 := by
  refine mass_retry_eq_one (run_lift_none _) ⟨1, by decide, ?_⟩
  show (OptionT.lift (RandMonad.randFin 6 : PMF (Fin 6)) :
    SPMF (Fin 6)).run (some 1) ≠ 0
  rw [run_lift_some]
  show (PMF.uniformOfFintype (Fin 6)) 1 ≠ 0
  rw [PMF.uniformOfFintype_apply]
  simp

end SPMF

end AlgoLib
