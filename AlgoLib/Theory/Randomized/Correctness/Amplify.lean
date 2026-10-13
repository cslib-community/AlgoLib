/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import AlgoLib.Theory.Randomized.Complexity.ExpectedCost
import AlgoLib.Theory.Randomized.Correctness.Correctness

/-!
# Amplification

Success amplification for Monte-Carlo algorithms: `amplify best k m`
runs `m` `k` times independently and combines the answers with `best`.
If a single run succeeds with probability at least `p`, and `best`
keeps a success when it sees one, the amplified run succeeds with
probability at least

```
1 − (1 − p) ^ k
```

so the failure probability decays geometrically in the number of runs
This is the "repeat and keep the best" argument, proved once and inherited by
every Monte-Carlo algorithm (`karger_amplified` is the first client).

The hypotheses are phrased on an invariant set `V` containing the
support of one run, typically supplied by the algorithm's one-sided
correctness theorem ("every output is at least the minimum cut"):

* `hclosed`: `best` does not leave `V`;
* `hkeep`: on `V`, `best` returns a success as soon as either
  argument is one.

## Main declarations

* `amplify`: `k` independent runs combined with `best`
* `support_amplify_subset`: one-sided correctness survives
  amplification
* `prob_amplify_compl_le`: the failure product `q ^ k`
* `amplify_success`: the amplification theorem `1 − (1 − p) ^ k`
* `amplify_min_success` / `amplify_max_success`: the ready-made form
  for one-sided algorithms on a linear order: the hypotheses are
  exactly the support and success theorems such an algorithm already
  provides
* `expected_cost_amplify`: `k + 1` runs cost `k + 1` times one run

Statements are phrased with the `ℙ[m ∈ S]` / `ℙ[m = v]` notation from
`AlgoLib.Infrastructure.Complexity.TailBounds`.
-/

namespace AlgoLib

open Cslib.Algorithms.Lean
open scoped ENNReal

/-! ## The combinator -/

/-- `amplify best k m`: run `m` `k` times independently and combine
the answers with `best`. `k = 0` degenerates to a single run: a
probabilistic computation cannot produce "no output". -/
def amplify {M} [Monad M] {β : Type} (best : β → β → β) : ℕ → M β → M β
  | 0, m => m
  | 1, m => m
  | k + 2, m => do
      let a ← m
      let b ← amplify best (k + 1) m
      return best a b

@[simp] lemma amplify_zero {M} [Monad M] {β : Type} (best : β → β → β)
    (m : M β) : amplify best 0 m = m := rfl

@[simp] lemma amplify_one {M} [Monad M] {β : Type} (best : β → β → β)
    (m : M β) : amplify best 1 m = m := rfl

/-- Unfolding equation for the inductive step, stated in the
`k + 1 + 1` shape that `induction`/`cases` produce. -/
lemma amplify_succ_succ {M} [Monad M] {β : Type} (best : β → β → β)
    (k : ℕ) (m : M β) :
    amplify best (k + 1 + 1) m =
      m >>= fun a => amplify best (k + 1) m >>= fun b => pure (best a b) :=
  rfl

/-! ## The failure product -/

/-- Two-run failure bound. If (on the supports) a failure of the
combined answer `best a b` forces both runs to have failed, the failure
probability of the combined run is at most the product of the
individual failure probabilities. -/
lemma prob_bind_best_le {α β γ : Type*} (p : PMF α) (r : PMF β)
    (best : α → β → γ) {A : Set α} {B : Set β} {F : Set γ}
    (h : ∀ a ∈ p.support, ∀ b ∈ r.support, best a b ∈ F → a ∈ A ∧ b ∈ B) :
    prob (p.bind fun a => r.bind fun b => PMF.pure (best a b)) F ≤
      prob p A * prob r B := by
  rw [prob_bind]
  have hpt : ∀ a, p a * prob (r.bind fun b => PMF.pure (best a b)) F ≤
      A.indicator (⇑p) a * prob r B := by
    intro a
    by_cases ha : a ∈ p.support
    · rw [prob_bind]
      by_cases hA : a ∈ A
      · rw [Set.indicator_of_mem hA]
        refine mul_le_mul' le_rfl ?_
        show _ ≤ ∑' b, B.indicator (⇑r) b
        refine ENNReal.tsum_le_tsum fun b => ?_
        by_cases hb : b ∈ r.support
        · by_cases hB : b ∈ B
          · rw [Set.indicator_of_mem hB]
            exact le_trans (mul_le_mul' le_rfl (prob_le_one _ _))
              (le_of_eq (mul_one _))
          · rw [Set.indicator_of_notMem hB,
              prob_pure_of_notMem fun hF => hB (h a ha b hb hF).2, mul_zero]
        · rw [(PMF.apply_eq_zero_iff r b).mpr hb, zero_mul]
          exact zero_le
      · rw [Set.indicator_of_notMem hA, zero_mul,
          show (∑' b, r b * prob (PMF.pure (best a b)) F) = 0 from
            ENNReal.tsum_eq_zero.mpr fun b => by
              by_cases hb : b ∈ r.support
              · rw [prob_pure_of_notMem fun hF => hA (h a ha b hb hF).1, mul_zero]
              · rw [(PMF.apply_eq_zero_iff r b).mpr hb, zero_mul],
          mul_zero]
    · rw [(PMF.apply_eq_zero_iff p a).mpr ha, zero_mul]
      exact zero_le
  refine le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right]
  rfl

/-- One-sided correctness survives amplification: if every single-run
output lies in `V` and `best` does not leave `V`, every amplified
output lies in `V`. -/
lemma support_amplify_subset
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] {β : Type}
    {best : β → β → β} {m : M β} {V : Set β}
    (hsupp : (𝒟[m]).support ⊆ V)
    (hclosed : ∀ a ∈ V, ∀ b ∈ V, best a b ∈ V) (k : ℕ) :
    (𝒟[amplify best k m]).support ⊆ V := by
  induction k with
  | zero => exact hsupp
  | succ k ih =>
    cases k with
    | zero => exact hsupp
    | succ k =>
      intro c hc
      rw [amplify_succ_succ, inst.toPMF_bind, pmf_bind_eq] at hc
      obtain ⟨a, ha, hc'⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
      obtain ⟨b, hb, rfl⟩ := mem_support_toPMF_bind_pure.mp hc'
      exact hclosed a (hsupp ha) b (ih hb)

/-- Failure product. All `k` runs must fail for the amplified run
to fail, so the failure probability is at most the `k`-th power of the
single-run failure probability. -/
theorem prob_amplify_compl_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] {β : Type}
    {best : β → β → β} {m : M β} {S V : Set β}
    (hsupp : (𝒟[m]).support ⊆ V)
    (hclosed : ∀ a ∈ V, ∀ b ∈ V, best a b ∈ V)
    (hkeep : ∀ a ∈ V, ∀ b ∈ V, a ∈ S ∨ b ∈ S → best a b ∈ S) (k : ℕ) :
    ℙ[amplify best k m ∈ Sᶜ] ≤ ℙ[m ∈ Sᶜ] ^ k := by
  induction k with
  | zero => rw [pow_zero]; exact prob_le_one _ _
  | succ k ih =>
    cases k with
    | zero => rw [zero_add, pow_one, amplify_one]
    | succ k =>
      rw [amplify_succ_succ]
      simp only [inst.toPMF_bind, inst.toPMF_pure, pmf_bind_eq, pmf_pure_eq]
      refine le_trans (prob_bind_best_le (𝒟[m]) (𝒟[amplify best (k + 1) m]) best
        (A := Sᶜ) (B := Sᶜ) (F := Sᶜ)
        fun a ha b hb hab =>
          ⟨fun haS => hab (hkeep a (hsupp ha) b
              (support_amplify_subset hsupp hclosed (k + 1) hb) (Or.inl haS)),
           fun hbS => hab (hkeep a (hsupp ha) b
              (support_amplify_subset hsupp hclosed (k + 1) hb) (Or.inr hbS))⟩)
        ?_
      exact le_trans (mul_le_mul' le_rfl ih) (le_of_eq (by ring))

/-- The amplification theorem. If one run of `m` succeeds, that is
lands in `S`, with probability at least `p`, then `k` independent runs
combined with a success-keeping `best` succeed with probability at
least `1 − (1 − p) ^ k`. -/
theorem amplify_success
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] {β : Type}
    {best : β → β → β} {m : M β} {S V : Set β} {p : ENNReal}
    (hsupp : (𝒟[m]).support ⊆ V)
    (hclosed : ∀ a ∈ V, ∀ b ∈ V, best a b ∈ V)
    (hkeep : ∀ a ∈ V, ∀ b ∈ V, a ∈ S ∨ b ∈ S → best a b ∈ S)
    (hp : p ≤ ℙ[m ∈ S]) (k : ℕ) :
    1 - (1 - p) ^ k ≤ ℙ[amplify best k m ∈ S] := by
  have hq : prob (𝒟[m]) Sᶜ ≤ 1 - p := by
    rw [prob_compl_eq_one_sub]
    exact tsub_le_tsub_left hp 1
  have hfail : prob (𝒟[amplify best k m]) Sᶜ ≤ (1 - p) ^ k :=
    le_trans (prob_amplify_compl_le hsupp hclosed hkeep k)
      (pow_le_pow_left' hq k)
  calc 1 - (1 - p) ^ k
      ≤ 1 - prob (𝒟[amplify best k m]) Sᶜ := tsub_le_tsub_left hfail 1
    _ = prob (𝒟[amplify best k m]) S := (prob_eq_one_sub_compl _ _).symm

/-- `amplify_success` for a Boolean one-sided test. If one run of
`m` answers `true` with probability at least `p`, then `k` independent
runs combined with `||` answer `true` with probability at least
`1 − (1 − p) ^ k`.

No support hypothesis is needed: `||` keeps a `true` wherever it finds
one, so the invariant set is everything. This is the combiner of a
test that never says `true` in error, which seems to be the commonest
Monte-Carlo shape. -/
theorem amplify_or_success
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {m : M Bool} {p : ENNReal} (hp : p ≤ ℙ[m = true]) (k : ℕ) :
    1 - (1 - p) ^ k ≤ ℙ[amplify (· || ·) k m = true] := by
  have h := amplify_success (M := M) (best := (· || ·))
    (m := m) (S := {true}) (V := Set.univ) (p := p)
    (Set.subset_univ _)
    (fun a _ b _ => Set.mem_univ _)
    (fun a _ b _ hor => by
      simp only [Set.mem_singleton_iff] at hor ⊢
      rcases hor with h1 | h1 <;> subst h1 <;> simp)
    (by rw [prob_singleton]; exact hp) k
  rwa [prob_singleton] at h

/-- Keep whichever answer has the smaller measure `f`. -/
def argmin {β γ : Type} [LinearOrder γ] (f : β → γ) (a b : β) : β :=
  if f a ≤ f b then a else b

/-- `amplify_success` for one-sided algorithms that return a
witness. If every output of `m` has measure at least `c` and `m`
attains `c` with probability at least `p`, then keeping the
smallest-measure answer over `k` independent runs attains `c` with
probability at least `1 − (1 − p) ^ k`.

This is the shape a Monte-Carlo algorithm that returns a witness
(Karger returns a cut, not a number) needs; `amplify_min_success` is
the special case `f = id`, where the witness is its own measure. -/
theorem amplify_argmin_success
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {β γ : Type} [LinearOrder γ] {f : β → γ} {m : M β} {c : γ} {p : ENNReal}
    (hsupp : ∀ b ∈ (𝒟[m]).support, c ≤ f b)
    (hp : p ≤ ℙ[m ∈ {b | f b = c}]) (k : ℕ) :
    1 - (1 - p) ^ k ≤ ℙ[amplify (argmin f) k m ∈ {b | f b = c}] :=
  amplify_success (best := argmin f) (S := {b | f b = c}) (V := {b | c ≤ f b})
    hsupp
    (fun a ha b hb => by
      unfold argmin; split_ifs with h
      · exact ha
      · exact hb)
    (fun a ha b hb hor => by
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      unfold argmin
      rcases hor with h1 | h1 <;> simp only [Set.mem_setOf_eq] at h1
      · rw [if_pos (h1 ▸ hb)]; exact h1
      · split_ifs with h
        · exact le_antisymm (h1 ▸ h) ha
        · exact h1)
    hp k

/-- `amplify_success` for the ubiquitous "keep the smallest answer"
case: if every output of `m` is at least `v` (one-sided error) and
`m` hits `v` with probability at least `p`, the minimum over `k`
independent runs is exactly `v` with probability at least
`1 − (1 − p) ^ k`. The two hypotheses are exactly the support and
success theorems a one-sided algorithm already provides. -/
theorem amplify_min_success
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {β : Type} [LinearOrder β] {m : M β} {v : β} {p : ENNReal}
    (hsupp : ∀ b ∈ (𝒟[m]).support, v ≤ b)
    (hp : p ≤ ℙ[m = v]) (k : ℕ) :
    1 - (1 - p) ^ k ≤ ℙ[amplify min k m = v] := by
  have hmin : (min : β → β → β) = argmin id := by
    funext a b; simp [argmin, min_def]
  have h := amplify_argmin_success (f := id) (c := v) hsupp
    (by simpa [Set.setOf_eq_eq_singleton, prob_singleton] using hp) k
  rw [hmin]
  simpa [Set.setOf_eq_eq_singleton, prob_singleton] using h

/-- Dual of `amplify_min_success`: keep the largest answer of a
never-overshooting algorithm. -/
theorem amplify_max_success
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {β : Type} [LinearOrder β] {m : M β} {v : β} {p : ENNReal}
    (hsupp : ∀ b ∈ (𝒟[m]).support, b ≤ v)
    (hp : p ≤ ℙ[m = v]) (k : ℕ) :
    1 - (1 - p) ^ k ≤ ℙ[amplify max k m = v] := by
  have h := amplify_success (best := max) (S := {v}) (V := Set.Iic v) (p := p)
    hsupp
    (fun a ha b hb => Set.mem_Iic.mpr (max_le (Set.mem_Iic.mp ha) (Set.mem_Iic.mp hb)))
    (fun a ha b hb hor => by
      rw [Set.mem_Iic] at ha hb
      rw [Set.mem_singleton_iff]
      rcases hor with h1 | h1 <;> rw [Set.mem_singleton_iff] at h1 <;> subst h1
      · exact max_eq_left hb
      · exact max_eq_right ha)
    (by rw [prob_singleton]; exact hp) k
  rwa [prob_singleton] at h

/-! ## Cost: amplification is linear -/

/-- `k + 1` runs cost `k + 1` times one run. -/
theorem expected_cost_amplify
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] {β : Type}
    (best : β → β → β) (k : ℕ) (m : TimeMT ℕ M β) :
    𝔼[cost amplify best (k + 1) m] = (k + 1 : ENNReal) * 𝔼[cost m] := by
  induction k with
  | zero => simp only [zero_add, Nat.cast_zero, amplify_one, one_mul]
  | succ k ih =>
    rw [amplify_succ_succ,
      expected_cost_toPMF_bind_const _ _ fun a => expected_cost_toPMF_bind_pure _ _,
      ih]
    push_cast
    ring

end AlgoLib
