/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Randomness.RandMonad
import AlgoLib.Theory.Randomized.Complexity.MonadCost
import AlgoLib.Theory.Randomized.Complexity.TimedSemantics

/-!
# Correctness recipes for randomized algorithms

This module packages the generic, algorithm-independent part of a
correctness proof, so that verifying a new uniform-pivot algorithm
reduces to its mathematical content: how the specification interacts
with one branch of the algorithm.

## Dirac correctness (Las Vegas algorithms)

An algorithm is Dirac-correct when its output distribution is a
point mass at the specification value. The recipe for proving
`toPMF (myAlgo args) = PMF.pure (spec args)`:

1. Spec-transport lemmas, the mathematics. For each branch, prove
   how the specification commutes with it (e.g. `orderStat_lt_branch`:
   "if the rank falls in the `<`-side, the order statistic of `L` is
   the order statistic of that side"). Tag them `@[spec_transport]`.
2. Induct. `induction args using myAlgo.induct`, then expose the pivot
   choice with the algorithm's `_eq_bind` decomposition lemma.
3. Collapse. `refine toPMF_randIdx_bind_dirac fun i => ?_` reduces
   the goal to a single branch at a fixed pivot `i`.
4. Discharge the branch. `toPMF_step` pushes `toPMF` through the
   monadic structure (lawful `tick`s vanish, `bind`/`pure`
   distribute). Close each case with the inductive hypotheses and the
   transport lemmas, or try `dirac_finish`, which attempts all of
   step 4 at once and leaves open exactly the missing mathematics.

## Distributional correctness (Monte Carlo algorithms)

When the output is genuinely random (e.g. `Karger`), correctness is a
property of the distribution: typically a support statement
(one-sided error) plus a success-probability bound, and for the exact
tier the full output law. The recipe mirrors the Dirac one. Unfold,
peel (`toPMF_step` / `toPMF_tick_bind`), uniform-average the pivot,
discharge each branch and count, with these generic primitives:

* `toPMF_randIdx_bind_apply`: the output probability is the uniform
  average of the branch probabilities (probabilistic analogue of
  `expected_cost_uniform_step`);
* `le_toPMF_randIdx_bind`: lower-bound the success probability by a
  single good pivot;
* `support_toPMF_randIdx_bind`: the support is the union of the
  branch supports;
* `toPMF_bind_pure_apply` / `toPMF_map_apply` (+ their `_eq_zero`
  off-range forms): pure post-processing along an injective function
  just transports probabilities;
* `mem_support_toPMF_bind_pure`: the support of a post-processed
  computation is the image of the support.
-/

namespace AlgoLib

-- The `>>=`/`pure`/`<$>`-vs-`PMF.bind`/`PMF.pure`/`PMF.map` bridges
-- (`pmf_bind_eq`, `pmf_pure_eq`, `pmf_map_eq`) live in `AlgoLib.Infrastructure.Tactics`;
-- register them for `toPMF_step` too.
attribute [toPMF_simp] pmf_bind_eq pmf_pure_eq pmf_map_eq

/-! ### Dirac correctness -/

/-- Dirac collapse. If every pivot branch produces the same point
mass, the uniform pivot choice is invisible: the whole computation is
that point mass. This is the generic closing step of a Las Vegas
correctness proof. -/
theorem toPMF_randIdx_bind_dirac
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} {hL : 0 < L.length}
    {f : Fin L.length → M β} {out : β}
    (h : ∀ i, inst.toPMF (f i) = PMF.pure out) :
    inst.toPMF (randIdx L hL >>= f) = PMF.pure out := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  rw [inst.toPMF_bind, inst.toPMF_randIdx]
  simp only [h]
  exact PMF.bind_const _ _

/-!
### Dirac correctness without a named specification value

`toPMF_randIdx_bind_dirac` asks the caller to name the output. Often
the specification is more naturally a property that happens to have
exactly one solution — "the sorted list", "the `k`-th smallest element"
— and naming a value up front is then working against the grain.

The two constructions below let a proof work with the property and
recover the value at the end. They are alternatives, not stages of one
recipe:

* Route A (`toPMF_randIdx_bind_dirac_spec`) keeps the collapse at
  the uniform draw, but weakens what each branch must supply: any
  deterministic output meeting the specification, rather than one
  agreed value. Uniqueness of the specification restores the agreement.
  Use it when the branch reasoning is naturally equational, so that the
  existing `@[spec_transport]` machinery still applies.
* Route B (support tier, then `eq_pure_of_support_subsingleton`)
  drops the value entirely for the duration of the induction and
  restores it once at the end. Use it when the branch reasoning is
  naturally a property.

Route B is the one that inducts most cleanly, and the reason is
structural rather than aesthetic: the support of a uniform draw is the
union of the branch supports (`support_toPMF_randIdx_bind`), so the
branches never have to agree on anything and each is discharged in
isolation. Route A and the plain Dirac collapse both require every
branch to produce the same value, which is a genuine extra obligation.

Both are provided because the framework is not meant to prescribe one
proof. An algorithm may use either; `Quicksort` carries both, once as
each, precisely to show that the choice is free.
-/

/-- Dirac collapse, specification form (route A). Each branch is known
to be deterministic and to meet the specification `P`, but the
branches are not known to agree on a value; uniqueness of
`P`-solutions supplies the agreement.

Generalizes `toPMF_randIdx_bind_dirac`, which is the special case
`P := (· = out)`. -/
theorem toPMF_randIdx_bind_dirac_spec
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} {hL : 0 < L.length}
    {f : Fin L.length → M β} {P : β → Prop}
    (huniq : ∀ x y, P x → P y → x = y)
    (h : ∀ i, ∃ out, inst.toPMF (f i) = PMF.pure out ∧ P out) :
    ∃ out, inst.toPMF (randIdx L hL >>= f) = PMF.pure out ∧ P out := by
  obtain ⟨out, hout, hP⟩ := h ⟨0, hL⟩
  refine ⟨out, toPMF_randIdx_bind_dirac fun i => ?_, hP⟩
  obtain ⟨out', hout', hP'⟩ := h i
  rwa [huniq out' out hP' hP] at hout'

/-- Support-to-Dirac bridge (route B, closing step). If every reachable
output satisfies `P` and `P` has at most one solution, the computation
is deterministic and its value is that solution.

This is the edge between the two correctness tiers of the framework:
Dirac correctness is support correctness plus uniqueness of the
specification. Tier 1 is therefore not an independent notion, it is
tier 3 with an extra hypothesis about the specification — which is also
why a Las Vegas algorithm and a Monte Carlo algorithm with a
single-valued answer are proved by the same induction.

`huniq` is the mathematics that a named specification value hides. For
sorting it is `sortedPerm_unique`: two sorted permutations of the same
list are equal. -/
theorem eq_pure_of_support_subsingleton
    {β : Type} {p : PMF β} {P : β → Prop}
    (huniq : ∀ x y, P x → P y → x = y)
    (hP : ∀ x ∈ p.support, P x) :
    ∃ out, p = PMF.pure out ∧ P out := by
  obtain ⟨a, ha⟩ := p.support_nonempty
  refine ⟨a, ?_, hP a ha⟩
  have hsupp : p.support = {a} :=
    Set.eq_singleton_iff_unique_mem.mpr
      ⟨ha, fun b hb => huniq b a (hP b hb) (hP a ha)⟩
  refine PMF.ext fun b => ?_
  rcases eq_or_ne b a with rfl | hb
  · rw [(PMF.apply_eq_one_iff p b).mpr hsupp, PMF.pure_apply_self]
  · rw [(PMF.apply_eq_zero_iff p b).mpr (by rw [hsupp]; simpa using hb),
      PMF.pure_apply_of_ne _ _ hb]

/-! ### Distributional correctness -/

/-- The output probability of a uniform-pivot algorithm is the uniform
average of the branch probabilities. -/
theorem toPMF_randIdx_bind_apply
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} (hL : 0 < L.length)
    (f : Fin L.length → M β) (b : β) :
    inst.toPMF (randIdx L hL >>= f) b =
      (L.length : ENNReal)⁻¹ * ∑ i : Fin L.length, inst.toPMF (f i) b := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  have : NeZero L.length := ⟨hL.ne'⟩
  rw [inst.toPMF_bind, inst.toPMF_randIdx, pmf_bind_eq]
  exact pmf_uniform_fin_bind_apply _ b

/-- A single good pivot lower-bounds the success probability by its
branch probability divided by the number of pivots. -/
theorem le_toPMF_randIdx_bind
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} (hL : 0 < L.length)
    (f : Fin L.length → M β) (b : β) (i₀ : Fin L.length) :
    (L.length : ENNReal)⁻¹ * inst.toPMF (f i₀) b ≤
      inst.toPMF (randIdx L hL >>= f) b := by
  rw [toPMF_randIdx_bind_apply hL f b]
  exact mul_le_mul' le_rfl
    (Finset.single_le_sum (f := fun i => inst.toPMF (f i) b)
      (fun i _ => zero_le) (Finset.mem_univ i₀))

/-- The support of a uniform-pivot algorithm is the union of the branch
supports: every pivot occurs with positive probability. This is the
shape of one-sided-error ("the output is always a valid answer")
correctness statements. -/
theorem support_toPMF_randIdx_bind
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} (hL : 0 < L.length)
    (f : Fin L.length → M β) :
    (inst.toPMF (randIdx L hL >>= f)).support =
      ⋃ i, (inst.toPMF (f i)).support := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  rw [inst.toPMF_bind, inst.toPMF_randIdx, pmf_bind_eq, PMF.support_bind]
  simp [PMF.support_uniformOfFintype]

/-- The same fact as a membership, which seems to be the form a
one-sided-error proof actually meets: an output is reachable exactly
when some branch reaches it. Completes the `mem_support_toPMF_*`
family of `LawfulRandMonad` with its uniform-draw member, so that a
proof need not unfold the union by hand. Use with an `⟨i, hi⟩`
pattern. -/
lemma mem_support_toPMF_randIdx_bind
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} {hL : 0 < L.length}
    {f : Fin L.length → M β} {b : β} :
    b ∈ (inst.toPMF (randIdx L hL >>= f)).support ↔
      ∃ i, b ∈ (inst.toPMF (f i)).support := by
  rw [support_toPMF_randIdx_bind hL f, Set.mem_iUnion]

/-- Every index is reachable: the uniform draw has full support. The
one fact about `randIdx` a support proof needs, in the form `simp` can
use, so that `support_step` handles the pivot draw like any other
monadic step instead of requiring a dedicated collapse lemma. -/
@[simp, support_simp] lemma mem_support_toPMF_randIdx
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {L : List α} {hL : 0 < L.length} {i : Fin L.length} :
    i ∈ (inst.toPMF (randIdx L hL)).support := by
  have : NeZero L.length := ⟨hL.ne'⟩
  rw [inst.toPMF_randIdx]
  simp

-- Because the draw's membership rewrites to `True`, `support_step`
-- needs the propositional cleanup to keep the existential it produces
-- in the shape an `obtain` pattern expects.
attribute [support_simp] true_and and_true

/-! ### Automation -/

attribute [toPMF_simp] LawfulRandMonad.toPMF_pure
attribute [toPMF_simp] LawfulRandMonad.toPMF_bind
attribute [toPMF_simp] MonadCost.tick_default
attribute [toPMF_simp] pure_bind bind_pure map_pure

-- The support/pointwise tier: after `toPMF_pure`/`toPMF_bind` have
-- unfolded the subterms (simp works innermost-first), these finish a
-- membership or point-probability goal. Composite `toPMF`-level forms
-- (`mem_support_toPMF_pure`, `toPMF_pure_apply`, …) exist as named
-- API in `LawfulRandMonad` for `rw`-style use.
attribute [toPMF_simp] PMF.mem_support_pure_iff PMF.mem_support_bind_iff
attribute [toPMF_simp] PMF.pure_apply

/-- `toPMF_step` pushes `toPMF` through one algorithm branch: lawful
`tick`s vanish, `toPMF` distributes over `bind` and evaluates on
`pure`. What remains is the branch's case split plus the recursive
calls, to be closed by the inductive hypotheses and (for the Dirac
tier) the `@[spec_transport]` lemmas. Tier-agnostic: the same
normalizer drives Dirac, distributional and support proofs.

Accepts a location: `toPMF_step at h` normalizes a hypothesis, which
is the form support proofs (`h : out ∈ (…).support`) live on.

Accepts an algorithm name as well: `toPMF_step myAlgo` first unfolds
one layer of `myAlgo` via its equation lemmas, so no proof spells a
compiler-generated `myAlgo.eq_1`. This is the twin of `cost_step`'s
ident form. -/
scoped syntax "toPMF_step" (Lean.Parser.Tactic.location)? : tactic

scoped syntax "toPMF_step " colGt ident
    (Lean.Parser.Tactic.location)? : tactic

scoped macro_rules
  | `(tactic| toPMF_step $[$loc:location]?) =>
    `(tactic| simp only [toPMF_simp] $[$loc:location]?)
  | `(tactic| toPMF_step $f:ident) =>
    `(tactic| (simp only [$f:ident]; toPMF_step))
  | `(tactic| toPMF_step $f:ident $loc:location) =>
    `(tactic| (simp only [$f:ident] $loc:location; toPMF_step $loc:location))

/-- `dirac_finish` attempts to close a branch goal outright: push
`toPMF` through with `toPMF_step`, split the branch's `if`s (when
any), then finish each case from the hypotheses in context (inductive
hypotheses, guard conditions) and the `@[spec_transport]` lemmas.
Best-effort: any leftover goal is exactly the missing mathematics
(typically a guard that needs `omega` before a transport lemma
applies). -/
scoped macro "dirac_finish" : tactic =>
  `(tactic| (toPMF_step <;> (try split_ifs) <;>
      simp_all [spec_transport, toPMF_simp]))

/-- `dirac_correct f` attempts a Dirac-correctness goal
`toPMF (f … : M _) = PMF.pure (spec …)` in one shot: functional
induction on `f` (`fun_induction` unfolds each equation and quantifies
the IHs over the pivot), collapse of the uniform pivot choice
(`toPMF_randIdx_bind_dirac`), then `dirac_finish` per branch, with a
`rfl` fallback for base cases whose spec reduces definitionally.

Any goal it leaves open is exactly the missing mathematics. State
the `@[spec_transport]` lemma it needs and it will close. -/
scoped macro "dirac_correct" f:ident : tactic =>
  `(tactic| (fun_induction $f <;>
      first
        | (refine toPMF_randIdx_bind_dirac fun i => ?_) <;> dirac_finish
        | dirac_finish
        | (toPMF_step; rfl)
        | skip))

-- Smoke test: a branch with no case split collapses outright.
example {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (a : ℕ) :
    inst.toPMF (pure a >>= fun x => (pure x : M ℕ)) = PMF.pure a := by
  dirac_finish

-- Smoke test for route A: branches stated existentially against a
-- single-valued specification still collapse, with the agreement
-- supplied by uniqueness rather than by a named value.
example {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {L : List ℕ} {hL : 0 < L.length} (a : ℕ) :
    ∃ out, inst.toPMF (randIdx L hL >>= fun _ => (pure a : M ℕ)) =
      PMF.pure out ∧ out = a :=
  toPMF_randIdx_bind_dirac_spec (fun _ _ hx hy => hx.trans hy.symm)
    fun _ => ⟨a, inst.toPMF_pure a, rfl⟩

/-! ### Automation for the support tier

`toPMF_step` pushes `toPMF` inwards and leaves a membership standing,
which is what Dirac and pointwise proofs want. A support proof wants
the membership taken apart: `out ∈ (𝒟[…]).support` should become an
existential over the branch outputs, one binder per random choice and
one per recursive call, so that the inductive hypotheses apply directly
to the pieces.

`support_step` is that normalizer. It reuses `toPMF_simp` (so lawful
ticks still vanish and `bind`/`pure` still distribute) and adds
`support_simp`, which turns the surviving memberships into existentials
and discharges the uniform draw outright.

What it deliberately does not do is the mathematics. After
`support_step`, a Quicksort branch reads "`S1` is in the support of the
recursive call on the `<`-side, `S2` on the `≥`-side, and the output is
`S1 ++ pivot :: S2`" — the induction step of the textbook proof, with
the randomness gone. Closing it is the user's `@[spec_preserve]` lemma,
exactly as `@[spec_transport]` is for the Dirac tier. The difference in
kind is worth stating: `spec_transport` lemmas are equations, which is
why `simp` alone can chain them and why `dirac_correct` is one line;
`spec_preserve` lemmas are implications, which `simp` cannot chain, so
the support tier gets an unpacker rather than a one-shot tactic. -/
scoped syntax "support_step" (Lean.Parser.Tactic.location)? : tactic

scoped syntax "support_step " colGt ident
    (Lean.Parser.Tactic.location)? : tactic

scoped macro_rules
  | `(tactic| support_step $[$loc:location]?) =>
    `(tactic| simp only [toPMF_simp, support_simp] $[$loc:location]?)
  | `(tactic| support_step $f:ident) =>
    `(tactic| (simp only [$f:ident]; support_step))
  | `(tactic| support_step $f:ident $loc:location) =>
    `(tactic| (simp only [$f:ident] $loc:location; support_step $loc:location))

/-- `support_finish` closes a support-tier branch: unpack the
membership with `support_step`, then chain the `@[spec_preserve]` pool
forward against the inductive hypotheses with `grind`.

`grind`, not `simp`. This is the whole asymmetry between the two tiers.
A `@[spec_transport]` lemma is an equation, `simp` rewrites with
equations, and that is why `dirac_correct` is one line; a
`@[spec_preserve]` lemma is an implication, which `simp` cannot chain
at all. `grind`'s E-matching can, so the support tier does get a
one-shot closer — but by search rather than by rewriting, and the
difference is worth knowing:

* it costs more (a `grind` call is roughly an order of magnitude
  slower than the explicit `obtain`/`exact` script it replaces);
* it must stay `only`-scoped. Unrestricted `grind` on a support goal
  in this framework hits the heartbeat limit at `isDefEq`;
* a failure is a failed search, not a stuck rewrite, so it reports no
  trace of what it tried. If it does not close, write the branch out.

`support_finish f at h` first unfolds the branch abbreviation `f`, the
same ident form `support_step` and `toPMF_step` take. When a branch
needs a fact outside the algorithm's `spec_preserve` set, drop to
`grind only [spec_preserve, extra]` by hand. -/
scoped syntax "support_finish" (Lean.Parser.Tactic.location)? : tactic

scoped syntax "support_finish " colGt ident
    (Lean.Parser.Tactic.location)? : tactic

-- The grind-set name must be spliced with `mkIdent`: a bare
-- `spec_preserve` inside the macro body picks up macro hygiene and
-- elaborates as `spec_preserve✝`, which `grind` cannot resolve.
scoped macro_rules
  | `(tactic| support_finish $[$loc:location]?) =>
    `(tactic| (support_step $[$loc:location]?;
               grind only [$(Lean.mkIdent `spec_preserve):term]))
  | `(tactic| support_finish $f:ident) =>
    `(tactic| (support_step $f:ident;
               grind only [$(Lean.mkIdent `spec_preserve):term]))
  | `(tactic| support_finish $f:ident $loc:location) =>
    `(tactic| (support_step $f:ident $loc:location;
               grind only [$(Lean.mkIdent `spec_preserve):term]))

end AlgoLib
