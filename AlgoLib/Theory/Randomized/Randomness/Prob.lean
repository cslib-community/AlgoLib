/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import AlgoLib.Theory.Randomized.Randomness.RandMonad

/-!
# The probability core: expectations, events, and the `ℙ` notation

The generic probability functionals of a randomized computation,
independent of any cost model: what an algorithm outputs with what
probability, and the expected value of a functional of its output.
Everything here is about `PMF` and `toPMF` alone, so it sits below
both the correctness and the complexity layers, a pure-probability
case study (`Geometric`, `CouponCollector`) never has to import the
cost machinery to use it.

## Main declarations

* `expVal p g`: the expectation `Σ' a, p a * g a`, with the
  `pure`/`bind`/`map`/uniform decomposition API. Used both for
  structural output functionals (a random tree's height) and, one
  layer up, as the definition behind `expected_cost`.
* `prob p s`: the probability of an event, with the event algebra
  (singletons, complements, `bind`, `pure`).
* `mul_prob_ge_le_expVal` / `prob_ge_le_expVal_div`: Markov's
  inequality on `expVal`, the estimate every tail bound rests on.
* `ℙ_{M}[e = v]` / `ℙ_{M}[e ∈ S]`: the output-probability notation,
  correctness twin of `𝔼_{M}[cost e]`.
-/

namespace AlgoLib

open ENNReal

/-!
## Expected values of output functionals

For randomized algorithms whose interesting measure is a structural
functional of the output, the height of a random tree, the size of a
random cut, rather than a tick count, we provide the bare expectation
`expVal p g = Σ' a, p a * g a` with the same `bind`/`pure`/uniform
decomposition API as `expected_cost`.
-/

/-- Expected value of `g` under `p`. -/
noncomputable def expVal {α : Type*} (p : PMF α) (g : α → ENNReal) : ENNReal :=
  ∑' a, p a * g a

@[simp] lemma expVal_pure {α : Type*} (a : α) (g : α → ENNReal) :
    expVal (PMF.pure a) g = g a := by
  unfold expVal
  rw [tsum_eq_single a fun b hb => by
    rw [PMF.pure_apply, if_neg hb, zero_mul]]
  rw [PMF.pure_apply, if_pos rfl, one_mul]

/-- Tower rule: the expected value through a bind is the expected
expected value. -/
lemma expVal_bind {α β : Type*} (p : PMF α) (f : α → PMF β)
    (g : β → ENNReal) :
    expVal (p.bind f) g = expVal p fun a => expVal (f a) g := by
  unfold expVal
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun a => tsum_congr fun b => by ring

/-- Averaging a constant. The `expVal_const` fact in the unfolded
form a cost proof actually meets: after the bind lemmas have peeled a
branch whose cost is a constant, the goal is literally `∑' a, p a * c`.
Tagged `@[expected_cost_simp]` so `cost_step` closes such a branch
outright instead of stopping one rewrite short. -/
@[expected_cost_simp] lemma pmf_tsum_mul_const {α : Type*} (p : PMF α)
    (c : ENNReal) : ∑' a, p a * c = c := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma expVal_const {α : Type*} (p : PMF α) (c : ENNReal) :
    expVal p (fun _ => c) = c :=
  pmf_tsum_mul_const p c

lemma expVal_mono {α : Type*} (p : PMF α) {g₁ g₂ : α → ENNReal}
    (h : ∀ a, g₁ a ≤ g₂ a) : expVal p g₁ ≤ expVal p g₂ :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)

lemma expVal_add {α : Type*} (p : PMF α) (g₁ g₂ : α → ENNReal) :
    expVal p (fun a => g₁ a + g₂ a) = expVal p g₁ + expVal p g₂ := by
  unfold expVal
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun a => mul_add _ _ _

lemma expVal_const_mul {α : Type*} (p : PMF α) (g : α → ENNReal)
    (c : ENNReal) :
    expVal p (fun a => c * g a) = c * expVal p g := by
  unfold expVal
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => by ring

lemma expVal_mul_right {α : Type*} (p : PMF α) (g : α → ENNReal)
    (c : ENNReal) :
    expVal p (fun a => g a * c) = expVal p g * c := by
  unfold expVal
  rw [← ENNReal.tsum_mul_right]
  exact tsum_congr fun a => (mul_assoc _ _ _).symm

/-- `expVal` through a `map`: relabelling then averaging is averaging
the composite. -/
lemma expVal_map {α β : Type*} (p : PMF α) (f : α → β) (g : β → ENNReal) :
    expVal (p.map f) g = expVal p (fun a => g (f a)) := by
  rw [PMF.map, expVal_bind]
  simp only [Function.comp_apply, expVal_pure]

/-- Uniform-pivot step for output functionals: the expected value
of `g` over `randIdx >>= branch` is the uniform average of the branch
expectations, the `expVal` analogue of `expected_cost_uniform_step`. -/
lemma expVal_toPMF_randIdx_bind
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} {hL : 0 < L.length}
    (f : Fin L.length → M β) (g : β → ENNReal) :
    expVal (inst.toPMF (randIdx L hL >>= f)) g =
      (L.length : ENNReal)⁻¹ * ∑ i : Fin L.length, expVal (inst.toPMF (f i)) g := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  rw [inst.toPMF_bind, inst.toPMF_randIdx, pmf_bind_eq, expVal_bind]
  unfold expVal
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]

/-- `expVal` of a `pure` program, the base case of every
output-functional induction. -/
lemma expVal_toPMF_pure
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type} (a : α) (g : α → ENNReal) :
    expVal (inst.toPMF (pure a : M α)) g = g a := by
  rw [inst.toPMF_pure, pmf_pure_eq, expVal_pure]

/-- Divide-and-conquer expectation: the expected value of a
functional of two computations run in sequence and combined by a pure
function is the iterated expectation, the `expVal` sibling of
`expected_cost_toPMF_seq₂` and `mem_support_toPMF_seq₂`. -/
lemma expVal_toPMF_seq₂
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α β γ : Type} (m₁ : M α) (m₂ : M β) (g : α → β → γ)
    (h : γ → ENNReal) :
    expVal (inst.toPMF (m₁ >>= fun a => m₂ >>= fun b =>
        pure (g a b))) h =
      expVal (inst.toPMF m₁) fun a =>
        expVal (inst.toPMF m₂) fun b => h (g a b) := by
  simp only [inst.toPMF_bind, pmf_bind_eq, expVal_bind, inst.toPMF_pure,
    pmf_pure_eq, expVal_pure]

/-!
## The mean of a `ℕ`-valued distribution

The special case of `expVal` that a cost law asks for. Naming it
lets a statement read as its mathematics does: `𝔼[couponCollector n]`
rather than `expVal (couponCollector n) (fun k => (k : ENNReal))`.
-/

/-- The mean of a distribution over `ℕ`. -/
noncomputable def mean (p : PMF ℕ) : ENNReal := expVal p (fun k => (k : ENNReal))

/-- `𝔼[p]`: the mean of the `ℕ`-valued distribution `p`. -/
scoped notation "𝔼[" p "]" => mean p

@[simp] lemma mean_pure (k : ℕ) : 𝔼[PMF.pure k] = (k : ENNReal) :=
  expVal_pure k _

/-- Linearity of expectation in the form a staged cost law uses
it: drawing `a`, then independently `b`, and reporting `a + b` costs
`𝔼[P] + 𝔼[Q]`. -/
lemma mean_bind_add (P Q : PMF ℕ) :
    𝔼[P.bind fun a => Q.bind fun b => PMF.pure (a + b)] = 𝔼[P] + 𝔼[Q] := by
  unfold mean
  rw [expVal_bind]
  have hinner : ∀ a : ℕ,
      expVal (Q.bind fun b => PMF.pure (a + b)) (fun k => (k : ENNReal)) =
        (a : ENNReal) + expVal Q (fun k => (k : ENNReal)) := by
    intro a
    rw [expVal_bind]
    simp only [expVal_pure]
    rw [show (fun b : ℕ => ((a + b : ℕ) : ENNReal)) =
        (fun b : ℕ => (a : ENNReal) + (b : ENNReal)) from funext fun b => by push_cast; ring,
      expVal_add, expVal_const]
  simp only [hinner]
  rw [expVal_add, expVal_const]

/-- The mean of a shifted law. -/
lemma mean_map_add_one (P : PMF ℕ) :
    𝔼[P.map (· + 1)] = 𝔼[P] + 1 := by
  unfold mean
  rw [expVal_map]
  rw [show (fun a : ℕ => (((a + 1 : ℕ)) : ENNReal)) =
      (fun a : ℕ => (a : ENNReal) + 1) from funext fun a => by push_cast; ring,
    expVal_add, expVal_const]

/-!
## Probability of an event
-/

/-- Probability of the event `s` under the distribution `p`. -/
noncomputable def prob {α : Type*} (p : PMF α) (s : Set α) : ENNReal :=
  ∑' a, s.indicator p a

/-- `prob` agrees with the outer measure induced by the `PMF`, giving
access to the Mathlib measure-theory API when needed. (Kept as the
escape hatch to measure theory; no in-repo client yet.) -/
lemma prob_eq_toOuterMeasure {α : Type*} (p : PMF α) (s : Set α) :
    prob p s = p.toOuterMeasure s :=
  (p.toOuterMeasure_apply s).symm

/-- A larger event is at least as probable. -/
lemma prob_mono {α : Type*} (p : PMF α) {s t : Set α} (h : s ⊆ t) :
    prob p s ≤ prob p t := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hs : a ∈ s
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (h hs)]
  · rw [Set.indicator_of_notMem hs]
    exact zero_le

@[simp] lemma prob_univ {α : Type*} (p : PMF α) :
    prob p Set.univ = 1 := by
  unfold prob
  rw [Set.indicator_univ]
  exact p.tsum_coe

/-- Probabilities are at most `1`. -/
lemma prob_le_one {α : Type*} (p : PMF α) (s : Set α) :
    prob p s ≤ 1 :=
  le_trans (prob_mono p (Set.subset_univ s)) (prob_univ p).le

/-!
### The event algebra

Singletons, complements, `bind` and `pure`: everything an event
computation needs.
-/

/-- The probability of a singleton event is the point probability. -/
@[simp] lemma prob_singleton {α : Type*} (p : PMF α) (a : α) :
    prob p {a} = p a := by
  unfold prob
  refine (tsum_eq_single a fun b hb => ?_).trans (Set.indicator_of_mem rfl ⇑p)
  exact Set.indicator_of_notMem (fun h : b ∈ ({a} : Set α) => hb h) ⇑p

/-- The probability of a finite event is the sum of its point
probabilities: `ℙ[m ∈ S] = ∑ s ∈ S, ℙ[m = s]`. -/
lemma prob_finset {α : Type*} (p : PMF α) (s : Finset α) :
    prob p ↑s = ∑ a ∈ s, p a := by
  rw [prob_eq_toOuterMeasure, PMF.toOuterMeasure_apply_finset]

/-- Disjoint events add. -/
lemma prob_union_of_disjoint {α : Type*} (p : PMF α) {s t : Set α}
    (h : Disjoint s t) : prob p (s ∪ t) = prob p s + prob p t := by
  unfold prob
  rw [Set.indicator_union_of_disjoint h]
  exact ENNReal.tsum_add

/-- An event and its complement split the total mass. -/
lemma prob_add_compl {α : Type*} (p : PMF α) (s : Set α) :
    prob p s + prob p sᶜ = 1 := by
  unfold prob
  rw [← ENNReal.tsum_add,
    show ∑' a, (s.indicator (⇑p) a + sᶜ.indicator (⇑p) a) = ∑' a, p a from
      tsum_congr fun a => by
        by_cases h : a ∈ s
        · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (by simpa using h),
            add_zero]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (by simpa using h),
            zero_add]]
  exact p.tsum_coe

/-- Success probability via the failure probability. -/
lemma prob_eq_one_sub_compl {α : Type*} (p : PMF α) (s : Set α) :
    prob p s = 1 - prob p sᶜ :=
  ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one p sᶜ))
    (prob_add_compl p s)

/-- Failure probability via the success probability. -/
lemma prob_compl_eq_one_sub {α : Type*} (p : PMF α) (s : Set α) :
    prob p sᶜ = 1 - prob p s :=
  ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one p s))
    (by rw [add_comm]; exact prob_add_compl p s)

/-- Total probability through a `bind`. -/
lemma prob_bind {α β : Type*} (p : PMF α) (f : α → PMF β) (s : Set β) :
    prob (p.bind f) s = ∑' a, p a * prob (f a) s := by
  unfold prob
  rw [show ∑' b, s.indicator (⇑(p.bind f)) b =
      ∑' b, ∑' a, p a * s.indicator (⇑(f a)) b from
    tsum_congr fun b => by
      by_cases hb : b ∈ s
      · rw [Set.indicator_of_mem hb, PMF.bind_apply]
        exact tsum_congr fun a => by rw [Set.indicator_of_mem hb]
      · rw [Set.indicator_of_notMem hb]
        symm
        simp only [Set.indicator_of_notMem hb, mul_zero, tsum_zero],
    ENNReal.tsum_comm]
  exact tsum_congr fun a => ENNReal.tsum_mul_left

/-- Uniform-pivot step for events: the probability of an event
over `randIdx >>= branch` is the uniform average of the branch
probabilities, the `prob` sibling of `expVal_toPMF_randIdx_bind` and
`toPMF_randIdx_bind_apply`. -/
lemma prob_toPMF_randIdx_bind
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {γ : Type*} {δ : Type} {L : List γ} (hL : 0 < L.length)
    (f : Fin L.length → M δ) (Ev : Set δ) :
    prob (inst.toPMF (randIdx L hL >>= f)) Ev =
      (L.length : ENNReal)⁻¹ *
        ∑ i : Fin L.length, prob (inst.toPMF (f i)) Ev := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  rw [inst.toPMF_bind, inst.toPMF_randIdx, pmf_bind_eq, prob_bind, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]

/-- Sequential success composition: to succeed after a bind it is
enough to land in a good set and then succeed from every good,
reachable outcome, the "survive, then recurse" step of a recursive
Monte-Carlo analysis (a recursive branch bound). -/
lemma le_prob_toPMF_bind
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {β γ : Type} {m : M β} {f : β → M γ} {Good : Set β} {Ev : Set γ}
    {p₁ p₂ : ENNReal}
    (h1 : p₁ ≤ prob (inst.toPMF m) Good)
    (h2 : ∀ b ∈ Good, b ∈ (inst.toPMF m).support →
      p₂ ≤ prob (inst.toPMF (f b)) Ev) :
    p₁ * p₂ ≤ prob (inst.toPMF (m >>= f)) Ev := by
  rw [inst.toPMF_bind, pmf_bind_eq, prob_bind]
  calc p₁ * p₂ ≤ prob (inst.toPMF m) Good * p₂ := mul_le_mul' h1 le_rfl
    _ = ∑' b, Good.indicator (inst.toPMF m) b * p₂ := by
        unfold prob
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∑' b, inst.toPMF m b * prob (inst.toPMF (f b)) Ev := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        by_cases hb : b ∈ Good
        · rw [Set.indicator_of_mem hb]
          by_cases hsupp : b ∈ (inst.toPMF m).support
          · exact mul_le_mul' le_rfl (h2 b hb hsupp)
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hsupp]
            simp
        · rw [Set.indicator_of_notMem hb]
          simp

/-- A point mass assigns probability `1` to any event containing it.
(Kept for symmetry with `prob_pure_of_notMem`, which the amplification
argument uses.) -/
lemma prob_pure_of_mem {α : Type*} {a : α} {s : Set α} (h : a ∈ s) :
    prob (PMF.pure a) s = 1 := by
  unfold prob
  rw [tsum_eq_single a fun b hb => ?_, Set.indicator_of_mem h,
    PMF.pure_apply, if_pos rfl]
  by_cases hb' : b ∈ s
  · rw [Set.indicator_of_mem hb', PMF.pure_apply, if_neg hb]
  · exact Set.indicator_of_notMem hb' _

/-- A point mass assigns probability `0` to any event avoiding it. -/
lemma prob_pure_of_notMem {α : Type*} {a : α} {s : Set α} (h : a ∉ s) :
    prob (PMF.pure a) s = 0 := by
  unfold prob
  rw [ENNReal.tsum_eq_zero]
  intro b
  by_cases hb : b ∈ s
  · rw [Set.indicator_of_mem hb, PMF.pure_apply,
      if_neg (fun hba : b = a => h (hba ▸ hb))]
  · exact Set.indicator_of_notMem hb _

/-!
## Markov's inequality for `expVal`
-/

/-- Markov's inequality, product form: `k · P(g ≥ k) ≤ E[g]`.
No side conditions. This is the fundamental estimate. -/
theorem mul_prob_ge_le_expVal {α : Type*} (p : PMF α)
    (g : α → ENNReal) (k : ENNReal) :
    k * prob p {a | k ≤ g a} ≤ expVal p g := by
  unfold prob expVal
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases h : k ≤ g a
  · rw [Set.indicator_of_mem (show a ∈ {a | k ≤ g a} from h), mul_comm]
    exact mul_le_mul' le_rfl h
  · rw [Set.indicator_of_notMem (show a ∉ {a | k ≤ g a} from h), mul_zero]
    exact zero_le

/-- Markov's inequality, division form: `P(g ≥ k) ≤ E[g] / k`. -/
theorem prob_ge_le_expVal_div {α : Type*} (p : PMF α)
    (g : α → ENNReal) {k : ENNReal} (hk0 : k ≠ 0) (hktop : k ≠ ⊤) :
    prob p {a | k ≤ g a} ≤ expVal p g / k := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop), mul_comm]
  exact mul_prob_ge_le_expVal p g k

/-!
## Post-processing transfer

An algorithm often has two legitimate read-outs of the same run: the
witness it computes and the number the analysis bounds (Karger
returns a cut; the analysis bounds the cut's value). `prob_map` and
`prob_congr_of_support` let a probability statement proved for one
read-out be reused verbatim for the other, with no re-induction: the
only obligation is that the two read-outs agree on the run's support.
-/

/-- Event monotonicity up to the support: an event that implies
another on the support is at most as probable. The `≤`-sibling of
`prob_congr_of_support`, for strengthening an event along an invariant
(`karger_finds_min` upgrades a value event to a cut event with it). -/
lemma prob_mono_of_support {α : Type*} {p : PMF α} {s t : Set α}
    (h : ∀ a ∈ p.support, a ∈ s → a ∈ t) :
    prob p s ≤ prob p t := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hs : a ∈ s
  · by_cases hsup : a ∈ p.support
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (h a hsup hs)]
    · rw [Set.indicator_apply_eq_zero.mpr
        fun _ => (PMF.apply_eq_zero_iff p a).mpr hsup]
      exact zero_le
  · rw [Set.indicator_of_notMem hs]
    exact zero_le

/-- Probability of an event under a pushforward is the probability of
its preimage. -/
lemma prob_map {α β : Type*} (p : PMF α) (f : α → β) (s : Set β) :
    prob (p.map f) s = prob p (f ⁻¹' s) := by
  rw [prob_eq_toOuterMeasure, prob_eq_toOuterMeasure,
    PMF.toOuterMeasure_map_apply]

/-- Post-processing transfer. Two read-outs of the same
computation (possibly into different types) that succeed together
on the support have the same success probability. -/
lemma prob_congr_of_support {α β γ : Type*} (p : PMF α)
    {f : α → β} {h : α → γ} {s : Set β} {t : Set γ}
    (hfh : ∀ a ∈ p.support, (f a ∈ s ↔ h a ∈ t)) :
    prob (p.map f) s = prob (p.map h) t := by
  rw [prob_map, prob_map]
  unfold prob
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · by_cases hf : f a ∈ s
    · rw [Set.indicator_of_mem (show a ∈ f ⁻¹' s from hf),
        Set.indicator_of_mem (show a ∈ h ⁻¹' t from (hfh a ha).mp hf)]
    · rw [Set.indicator_of_notMem (show a ∉ f ⁻¹' s from hf),
        Set.indicator_of_notMem
          (show a ∉ h ⁻¹' t from fun hc => hf ((hfh a ha).mpr hc))]
  · have h0 : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr ha
    have hz : ∀ u : Set α, u.indicator (⇑p) a = 0 := by
      intro u
      by_cases hu : a ∈ u
      · rw [Set.indicator_of_mem hu, h0]
      · rw [Set.indicator_of_notMem hu]
    rw [hz, hz]

/-- `prob_congr_of_support` at the level of a random monad: transfer a
success probability from one read-out of an algorithm to another. -/
lemma prob_map_congr_of_support
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {β γ δ : Type} (m : M β) {f : β → γ} {h : β → δ}
    {s : Set γ} {t : Set δ}
    (hfh : ∀ b ∈ (LawfulRandMonad.toPMF m).support, (f b ∈ s ↔ h b ∈ t)) :
    prob (LawfulRandMonad.toPMF (f <$> m : M γ)) s
      = prob (LawfulRandMonad.toPMF (h <$> m : M δ)) t := by
  rw [LawfulRandMonad.toPMF_map, LawfulRandMonad.toPMF_map]
  exact prob_congr_of_support _ hfh

/-!
## Success probability of outputs

`ℙ_{M}[e = v]` / `ℙ_{M}[e ∈ S]` are the correctness twins of
`ℙ_{M}[cost e > k]`: the probability that the algorithm `e`, run
at the random monad `M`, outputs exactly `v` (resp. lands in the
event `S`). A Monte-Carlo statement then reads as English:
`2 / (n(n−1)) ≤ ℙ_{M}[Karger g = g.minCutValue]`. Both expand to the
underlying `toPMF`/`prob` form so `simp`/`rw` match lemmas without
unfolding hints; `prob_singleton` mediates between the two.
-/

/-- `ℙ_{M}[e = v]`: probability that the algorithm `e`, run at the
random monad `M`, outputs exactly `v`. -/
scoped macro "ℙ_{" M:term "}[" e:term:51 " = " v:term:51 "]" : term =>
  `(LawfulRandMonad.toPMF ($e : $M _) $v)

/-- `ℙ[m = v]`: output probability of an already-typed
computation (no monad index needed). -/
scoped macro "ℙ[" m:term:51 " = " v:term "]" : term =>
  `(LawfulRandMonad.toPMF $m $v)

/-- `ℙ_{M}[e ∈ S]`: probability that the algorithm `e`, run at the
random monad `M`, outputs a value in the event `S`. -/
scoped macro "ℙ_{" M:term "}[" e:term:51 " ∈ " S:term:51 "]" : term =>
  `(prob (LawfulRandMonad.toPMF ($e : $M _)) $S)

/-- `ℙ[m ∈ S]`: event probability of an already-typed
computation (no monad index needed). -/
scoped macro "ℙ[" m:term:51 " ∈ " S:term "]" : term =>
  `(prob (LawfulRandMonad.toPMF $m) $S)

-- Smoke test: at the notation level, a finite event is the sum of its
-- point probabilities.
example {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] {β : Type}
    (e : M β) (S : Finset β) :
    ℙ_{M}[e ∈ (↑S : Set β)] = ∑ b ∈ S, ℙ_{M}[e = b] :=
  prob_finset _ S

end AlgoLib
