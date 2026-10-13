/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Randomness.RandMonad
import AlgoLib.Theory.Randomized.Complexity.MonadCost

/-!
# Timed semantics

The meaning of a `TimeMT`-timed computation, that is what it outputs as
opposed to what it costs. Split out of `ExpectedCost` because none of
it mentions an expected value; it sits between the cost transformer
(`TimeMT`, `MonadCost`) and the cost analysis (`ExpectedCost`), which
is why it lives in `Complexity/` even though what it delivers is
correctness:

* `RandMonad (TimeMT ℕ M)`: timed programs can flip coins;
* the clock-erasure lemmas: `TimeM.ret <$> ·` distributes through
  the combinators;
* `LawfulRandMonad (TimeMT ℕ M)`: the output distribution of a
  timed program is its clock erasure, so every generic correctness
  theorem instantiates at `TimeMT ℕ PMF` for free;
* `LawfulMonadCost`: cost models whose `tick` is invisible to the
  output distribution (`toPMF_tick_bind` peels a lawful tick in one
  rewrite): one correctness statement covers every cost reading.

The payoff: timed correctness is never a separate proof obligation.
-/

namespace AlgoLib

open Cslib.Algorithms.Lean
open ENNReal

/-- RandMonad lifts through `TimeMT` via `monadLift`, so any
randomized algorithm can be run in timed mode. -/
instance instRandMonadTimeMT {M} [Monad M] [RandMonad M] :
    RandMonad (TimeMT ℕ M) where
  randFin n := TimeMT.lift (RandMonad.randFin n)

/-- In `TimeMT`, `randIdx` is a lifted `randIdx` of the base monad.
Stated at the term level (not on `.run`): this is the form a user's
goal actually contains, so `cost_step` can expose the `TimeMT.lift`
with no `show` desugaring. -/
@[expected_cost_simp] lemma randIdx_timeMT
    {M} [Monad M] [RandMonad M] {α : Type*}
    (L : List α) (h : 0 < L.length) :
    (randIdx L h : TimeMT ℕ M (Fin L.length)) =
    TimeMT.lift (randIdx L h : M (Fin L.length)) := rfl

/-- Term-level form for `randFin`, likewise. -/
@[expected_cost_simp] lemma randFin_timeMT
    {M} [Monad M] [RandMonad M] (n : ℕ) [NeZero n] :
    (RandMonad.randFin n : TimeMT ℕ M (Fin n)) =
    TimeMT.lift (RandMonad.randFin n : M (Fin n)) := rfl

-- `cost_step` must see the `TimeMT.tick` behind the abstract
-- `MonadCost.tick` a user writes.
attribute [expected_cost_simp] MonadCost.tick_timeMT

/-!
## Generic `TimeMT` erasure lemmas

Erasing time (`TimeM.ret <$> ·`) distributes through
`bind`, `pure`, `tick`, and `lift`. These four are exactly the proof
obligations of the `LawfulRandMonad (TimeMT ℕ M)` instance below and
are used there by name; they carry no `@[simp]` attribute, since
their `TimeM.ret <$> (…).run` head never occurs in a user's goal.
-/

lemma TimeMT_erase_bind
    {M} [Monad M] [LawfulMonad M] {α β}
    (m : TimeMT ℕ M α) (f : α → TimeMT ℕ M β) :
    TimeM.ret <$> (m >>= f).run =
      (TimeM.ret <$> m.run) >>=
        fun a => TimeM.ret <$> (f a).run := by
  simp only [TimeMT.run_bind, map_bind]
  simp_all only [map_pure, bind_pure_comp, bind_map_left]

lemma TimeMT_erase_pure
    {M} [Monad M] [LawfulMonad M] {α} (a : α) :
    TimeM.ret <$> (pure a : TimeMT ℕ M α).run =
      pure a := by
  simp only [TimeMT.run_pure, map_pure]

lemma TimeMT_erase_tick
    {M} [Monad M] [LawfulMonad M] (t : ℕ) :
    TimeM.ret <$>
      (TimeMT.tick t : TimeMT ℕ M Unit).run =
      pure () := by
  simp only [TimeMT.run_tick, map_pure]

lemma TimeMT_erase_lift
    {M} [Monad M] [LawfulMonad M] {α} (m : M α) :
    TimeM.ret <$>
      (TimeMT.lift m : TimeMT ℕ M α).run = m := by
  rw [TimeMT.run_lift, ← Functor.map_map]
  simp_all only [Functor.map_map, id_map']

/-- `TimeMT ℕ M` is itself a lawful random monad: interpret a timed
computation by erasing the clock (`TimeM.ret <$> ·.run`) and
interpreting the result in `M`. The erasure lemmas above are exactly
the three laws. Consequence: every generic correctness theorem
instantiates at `M := TimeMT ℕ PMF` for free, so correctness of the
timed program is never a separate proof obligation. -/
noncomputable instance instLawfulRandMonadTimeMT
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    LawfulRandMonad (TimeMT ℕ M) where
  toRandMonad := instRandMonadTimeMT
  toPMF m := inst.toPMF (TimeM.ret <$> m.run)
  toPMF_pure a := by rw [TimeMT_erase_pure, inst.toPMF_pure]
  toPMF_bind m f := by rw [TimeMT_erase_bind, inst.toPMF_bind]
  toPMF_randFin n := by
    intro hn
    rw [randFin_timeMT, TimeMT_erase_lift, inst.toPMF_randFin]

/-- A cost model is lawful when ticking is invisible to the output
distribution. Both canonical instances qualify: the no-op default and
the accumulating `TimeMT` one. A correctness theorem stated with
`[MonadCost C M] [LawfulMonadCost C M]` therefore covers every cost
reading of the algorithm at once. In particular it instantiates at
`M := TimeMT ℕ PMF` with real ticks, so timed correctness is free. -/
class LawfulMonadCost (C : Type) (M : Type → Type)
    [Monad M] [LawfulMonad M] [LawfulRandMonad M] [MonadCost C M] :
    Prop where
  /-- `tick` maps to the Dirac mass at `()`. -/
  toPMF_tick (c : C) :
    LawfulRandMonad.toPMF (MonadCost.tick c : M Unit) = PMF.pure ()

-- With an abstract lawful tick, the `PMF.pure ()` it maps to is
-- collapsed at the `PMF` level, so `PMF.pure_bind` joins the set.
attribute [toPMF_simp] LawfulMonadCost.toPMF_tick PMF.pure_bind

/-- The no-op default cost model is lawful. -/
instance instLawfulMonadCostDefault {C : Type} {M : Type → Type}
    [m : Monad M] [lm : LawfulMonad M] [lr : LawfulRandMonad M] :
    @LawfulMonadCost C M m lm lr instMonadCostDefault :=
  ⟨fun _ => lr.toPMF_pure ()⟩

/-- The accumulating `TimeMT` cost model is lawful: erasing the clock
kills the tick. -/
instance instLawfulMonadCostTimeMT {M : Type → Type}
    [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    LawfulMonadCost ℕ (TimeMT ℕ M) :=
  ⟨fun c => by
    show inst.toPMF
      (TimeM.ret <$> (TimeMT.tick c : TimeMT ℕ M Unit).run) = PMF.pure ()
    rw [TimeMT_erase_tick, inst.toPMF_pure]; rfl⟩

/-- A lawful `tick` is invisible to the output distribution even
mid-computation: peel it in one rewrite. -/
lemma toPMF_tick_bind {C : Type} {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] [MonadCost C M] [LawfulMonadCost C M]
    {β : Type} (c : C) (f : Unit → M β) :
    inst.toPMF (MonadCost.tick c >>= f) = inst.toPMF (f ()) := by
  rw [inst.toPMF_bind, LawfulMonadCost.toPMF_tick, pmf_bind_eq, PMF.pure_bind]

/-- Support facts transfer to timed runs: an outcome reachable with
its clock is reachable without it. Lets a support invariant proved at
any lawful `M` feed the cost analysis of the `TimeMT ℕ M` reading. -/
lemma mem_support_timedPMF
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {β : Type} {m : TimeMT ℕ M β} {tm : TimeM ℕ β}
    (h : tm ∈ (inst.toPMF m.run).support) :
    tm.ret ∈ (𝒟[m]).support := by
  show tm.ret ∈ (inst.toPMF (TimeM.ret <$> m.run)).support
  rw [inst.toPMF_map, pmf_map_eq, PMF.support_map]
  exact ⟨tm, h, rfl⟩

end AlgoLib
