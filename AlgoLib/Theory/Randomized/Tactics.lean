/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.SimpAttr

/-!
  Tactic infrastructure for PMF proofs.

  Organized in layers:
  - A: grind/simp tags to bridge PMF into arithmetic
  - B: the `pmf_simp_attr` simp set for computing concrete
    probabilities (consumed by `runtime_simp` in `ExpectedCost`)
  - C: reusable derived lemmas

  ## Custom simp attribute

  We use a registered `@[pmf_simp_attr]` attribute (declared in
  `AlgoLib.Infrastructure.SimpAttr`). Downstream files can locally tag domain-specific
  lemmas with `@[pmf_simp_attr]` to extend the automation organically.
-/

universe u

namespace AlgoLib

open ENNReal PMF
open scoped NNRat

/-! ================================================================
    LAYER A: simp/grind tags
    ================================================================

  - @[simp] for monad laws (safe, always normalize in the right direction)
  - @[grind =] for domain-bridge lemmas (bind_apply, uniformOfFintype_apply, etc.)
    grind's e-matching picks these up when the goal already mentions the terms
  - @[grind →] for forward side conditions (ne_zero, ne_top)
-/

/-! ##### A.1  ENNReal Arithmetic -/

@[grind =]
lemma ennreal_natCast_inv_mul_self {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ * (n : ENNReal) = 1 :=
  ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

@[grind =]
lemma ennreal_natCast_mul_inv_self {n : ℕ} [NeZero n] :
    (n : ENNReal) * (n : ENNReal)⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

@[grind →]
lemma ennreal_natCast_inv_ne_zero {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ ≠ 0 :=
  ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)

@[grind →]
lemma ennreal_natCast_inv_ne_top {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne n)

attribute [grind =] ENNReal.div_add_div_same

-- summing n copies of n⁻¹ * t over Fin n gives t
lemma ennreal_inv_nsmul_cancel {n : ℕ} [NeZero n] (t : ENNReal) :
    ∑ _i : Fin n, (n : ENNReal)⁻¹ * t = t := by
  rw [Finset.sum_const]; simp [Fintype.card_fin]
  rw [← mul_assoc, ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast NeZero.ne n
  · exact ENNReal.natCast_ne_top n

/-! ##### A.2  PMF Monad Laws (@[simp], safe normalization) -/

attribute [simp] PMF.pure_bind    -- `pure a >>= f = f a`
attribute [simp] PMF.bind_pure    -- `p >>= pure = p`
attribute [simp] PMF.bind_const   -- `p >>= (fun _ => q) = q`
attribute [simp] PMF.bind_bind    -- `(p >>= f) >>= g = p >>= (fun a => f a >>= g)`
attribute [simp] PMF.pure_map     -- `f <$> pure a = pure (f a)`
attribute [simp] PMF.map_id       -- `id <$> p = p`

-- also register for grind (the two engines are independent)
attribute [grind =] PMF.pure_bind
attribute [grind =] PMF.bind_pure
attribute [grind =] PMF.bind_bind

/-! ##### A.3  PMF Pointwise Application & Distribution Weights (@[grind =]) -/

-- not safe as @[simp] (introducing tsum/ite can blow up), but fine for grind's e-matching
attribute [grind =] PMF.pure_apply
attribute [grind =] PMF.bind_apply
attribute [grind =] PMF.map_apply
attribute [grind =] PMF.uniformOfFintype_apply
attribute [grind =] PMF.uniformOfFinset_apply
attribute [grind =] PMF.bernoulli_apply
attribute [grind =] Fintype.card_fin
attribute [grind =] Fintype.card_bool

-- also register for grind
attribute [grind =] PMF.map_comp
attribute [grind =] PMF.bind_map
attribute [grind =] PMF.map_bind
attribute [grind =] PMF.bind_pure_comp

/-! ##### A.4  Support & bindOnSupport -/

attribute [grind =] PMF.support_uniformOfFintype
attribute [grind =] PMF.support_uniformOfFinset
attribute [grind =] PMF.support_pure
attribute [grind =] PMF.mem_support_iff
attribute [grind =] PMF.support_bind
attribute [grind =] PMF.mem_support_uniformOfFinset_iff
attribute [grind =] PMF.pure_bindOnSupport
attribute [grind =] PMF.bindOnSupport_apply

/-! ================================================================
    LAYER B: pmf_simp_attr, concrete probability computation
    ================================================================

  The simp set for computing things like P(X = 3) = 1/12: it collapses
  tsum to finite sums, applies distribution weights, and cleans up
  arithmetic. Its consumer is `runtime_simp` (in `ExpectedCost`, the
  combined cost normalizer); downstream files can extend the set by
  tagging their lemmas with `@[pmf_simp_attr]`.

  The attribute itself is declared in `AlgoLib.Infrastructure.SimpAttr`
  (Lean requires the declaration in a separate file).
-/

-- Tag key lemmas with the custom attribute
attribute [pmf_simp_attr] tsum_fintype
attribute [pmf_simp_attr] Fin.sum_univ_one Fin.sum_univ_two Fin.sum_univ_three
attribute [pmf_simp_attr] Fin.sum_univ_four Fin.sum_univ_five Fin.sum_univ_six
attribute [pmf_simp_attr] Fin.sum_univ_seven Fin.sum_univ_eight
attribute [pmf_simp_attr] Fintype.sum_bool
attribute [pmf_simp_attr] tsum_ite_eq
attribute [pmf_simp_attr] PMF.tsum_coe
attribute [pmf_simp_attr] PMF.pure_bind PMF.bind_pure PMF.pure_apply
attribute [pmf_simp_attr] PMF.bind_apply PMF.bind_const
attribute [pmf_simp_attr] PMF.pure_map PMF.map_apply PMF.map_id
attribute [pmf_simp_attr] PMF.bind_pure_comp
attribute [pmf_simp_attr] PMF.uniformOfFintype_apply PMF.uniformOfFinset_apply
attribute [pmf_simp_attr] PMF.bernoulli_apply
attribute [pmf_simp_attr] PMF.bindOnSupport_eq_bind PMF.pure_bindOnSupport
attribute [pmf_simp_attr] PMF.bindOnSupport_apply
attribute [pmf_simp_attr] Fintype.card_fin Fintype.card_bool
attribute [pmf_simp_attr] ite_mul mul_ite
attribute [pmf_simp_attr] Finset.sum_ite_eq Finset.sum_ite_eq'
attribute [pmf_simp_attr] mul_one one_mul mul_zero zero_mul add_zero zero_add
attribute [pmf_simp_attr] ENNReal.inv_two_add_inv_two
attribute [pmf_simp_attr] if_true if_false ite_self dite_true dite_false
attribute [pmf_simp_attr] eq_self_iff_true ne_eq
attribute [pmf_simp_attr] Finset.mem_univ Finset.mem_singleton Finset.mem_insert

/-! ================================================================
    LAYER C: Reusable Derived Lemmas
    ================================================================ -/

/-!
#### `Monad`-vs-`PMF` syntactic bridges

`do`-notation produces `>>=`/`pure`/`<$>`, while Mathlib's `PMF` lemmas
are stated for `PMF.bind`/`PMF.pure`/`PMF.map`. The two are
definitionally equal; these rfl-bridges let `simp`/`rw` cross the gap
syntactically.
-/

@[pmf_simp_attr]
lemma pmf_bind_eq {α β : Type u} (p : PMF α) (f : α → PMF β) :
    p >>= f = p.bind f := rfl

@[pmf_simp_attr]
lemma pmf_pure_eq {α : Type*} (a : α) :
    (Pure.pure a : PMF α) = PMF.pure a := rfl

@[pmf_simp_attr]
lemma pmf_map_eq {α β : Type u} (f : α → β) (p : PMF α) :
    f <$> p = p.map f := rfl

/-- `map some` hits `some a` with the original probability. -/
lemma pmf_map_some_apply {α : Type*} (p : PMF α) (a : α) :
    (p.map some) (some a) = p a := by
  rw [PMF.map_apply]
  exact (tsum_eq_single a fun y hy =>
    if_neg fun h => hy (Option.some_inj.mp h).symm).trans (if_pos rfl)

/-- `map some` never hits `none`. -/
lemma pmf_map_some_none {α : Type*} (p : PMF α) : (p.map some) none = 0 := by
  rw [PMF.map_apply]
  simp

/-- uniformOfFintype (Fin 1) = pure 0, useful as a base case -/
lemma pmf_uniformOfFintype_fin_one :
    PMF.uniformOfFintype (Fin 1) = PMF.pure (0 : Fin 1) := by
  ext a
  have ha : a = 0 := Fin.ext (by omega)
  subst ha; simp [PMF.uniformOfFintype_apply]

/-- bind over a fintype PMF as a Finset.sum (helper for the next lemma) -/
lemma pmf_bind_apply_fintype {α β : Type*} [Fintype α] (p : PMF α)
    (f : α → PMF β) (b : β) :
    (p.bind f) b = ∑ a : α, p a * (f a) b := by
  rw [PMF.bind_apply, tsum_fintype]

/-- uniform bind over Fin n expressed as n⁻¹ * ∑ i, … -/
lemma pmf_uniform_fin_bind_apply {β : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → PMF β) (b : β) :
    ((PMF.uniformOfFintype (Fin n)).bind f) b =
    (n : ENNReal)⁻¹ * ∑ i : Fin n, (f i) b := by
  rw [pmf_bind_apply_fintype]
  simp [PMF.uniformOfFintype_apply, Fintype.card_fin, Finset.mul_sum]

/-- when all branches of a uniform bind over Fin n give the same probability v,
    the result is v -/
lemma pmf_uniform_fin_bind_const_prob {β : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → PMF β) (b : β) (v : ENNReal)
    (hv : ∀ i, (f i) b = v) :
    ((PMF.uniformOfFintype (Fin n)).bind f) b = v := by
  rw [pmf_uniform_fin_bind_apply]
  simp only [hv, Finset.mul_sum]
  exact ennreal_inv_nsmul_cancel v

/-- Inverting a ratio of naturals: `(a/b)⁻¹ = b/a`. -/
lemma ennreal_natCast_div_inv {a b : ℕ} (ha : a ≠ 0) :
    ((a : ENNReal) / (b : ENNReal))⁻¹ = (b : ENNReal) / (a : ENNReal) := by
  rw [div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (by exact_mod_cast ha))
      (Or.inl (ENNReal.natCast_ne_top _)),
    inv_inv, mul_comm, ← div_eq_mul_inv]

/-- Division comparison in `ENNReal` for natural fractions, by
cross-multiplication in `ℕ`. -/
lemma ennreal_div_le_div_nat {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) :
    (a : ENNReal) / (b : ENNReal) ≤ (c : ENNReal) / (d : ENNReal) := by
  rw [ENNReal.div_le_iff (by exact_mod_cast hb.ne' : (b : ENNReal) ≠ 0)
    (ENNReal.natCast_ne_top b)]
  rw [show (c : ENNReal) / (d : ENNReal) * (b : ENNReal) =
      (c : ENNReal) * (b : ENNReal) / (d : ENNReal) by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hd.ne'))
    (Or.inl (ENNReal.natCast_ne_top d))]
  exact_mod_cast h

/-- The ℚ≥0 → ENNReal bridge for probability bounds: a comparison of
natural fractions proved in `ℚ≥0`, where Mathlib's counting results
(e.g. Schwartz–Zippel) live, transfers directly to the `ENNReal` the
framework's probabilities live in. One call replaces the
cross-multiplication ceremony. -/
lemma ennreal_div_le_div_of_nnrat {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : (a : ℚ≥0) / (b : ℚ≥0) ≤ (c : ℚ≥0) / (d : ℚ≥0)) :
    (a : ENNReal) / (b : ENNReal) ≤ (c : ENNReal) / (d : ENNReal) := by
  refine ennreal_div_le_div_nat hb hd ?_
  have h2 := (div_le_div_iff₀
    (by exact_mod_cast hb : (0 : ℚ≥0) < b)
    (by exact_mod_cast hd : (0 : ℚ≥0) < d)).mp h
  exact_mod_cast h2

end AlgoLib
