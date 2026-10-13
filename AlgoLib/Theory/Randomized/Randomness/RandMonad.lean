/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Tactics

/-!
# LawfulRandMonad

A typeclass for monads with lawful randomness:
a monad `M` equipped with a `RandMonad` instance and an
interpretation into `PMF` that respects `pure`, `bind`,
and maps `randFin` to the uniform distribution.

## Architectural note

The primitive draw is `randFin n`, a choice among `n`
alternatives, decoupled from any particular data structure.
Derived helpers like `randIdx` for lists are provided as
convenience functions.

## Main declarations

* `RandMonad`: typeclass with primitive `randFin`
* `randIdx`: derived helper for random list indexing
* `LawfulRandMonad`: the lawful typeclass with `toPMF`
* `LawfulRandMonad PMF`: canonical instance for `PMF`
-/

namespace AlgoLib

/-!
### `RandMonad`: primitive "entropy" source
-/

/-- A random monad: a monad `M` with one function `randFin`, its source
of randomness. -/
class RandMonad (M : Type → Type) [Monad M] where
  /-- An element of `M (Fin n)`. -/
  randFin (n : ℕ) [NeZero n] : M (Fin n)

/-- `randFin` at the length of a nonempty list. -/
def randIdx {M} [Monad M] [RandMonad M] {α}
    (L : List α) (h : 0 < L.length := by grind) : M (Fin L.length) :=
  have : NeZero L.length := ⟨h.ne'⟩
  RandMonad.randFin L.length

/-!
### Mathematical Specification
-/

/-- A `LawfulRandMonad` is a lawful monad with an
interpretation `toPMF` into `PMF` satisfying three axioms:
1. `pure` maps to `PMF.pure`
2. `bind` distributes
3. `randFin` maps to the uniform distribution -/
class LawfulRandMonad
    (M : Type → Type) [Monad M] [LawfulMonad M]
    extends RandMonad M where
  /-- Interpret an `M`-computation as a probability distribution. -/
  toPMF : ∀ {α}, M α → PMF α
  /-- `pure a` maps to the Dirac mass at `a`. -/
  toPMF_pure : ∀ {α} (a : α), toPMF (pure a) = pure a
  /-- `bind` distributes through `toPMF`. -/
  toPMF_bind : ∀ {α β} (x : M α) (f : α → M β),
    toPMF (x >>= f) =
      (toPMF x) >>= (fun a => toPMF (f a))
  /-- `randFin n` maps to the uniform distribution on `Fin n`
  (`Nonempty (Fin n)` is synthesized from `[NeZero n]`). -/
  toPMF_randFin :
    ∀ (n : ℕ) [NeZero n],
      toPMF (randFin n) = PMF.uniformOfFintype (Fin n)

/-- Derived: `toPMF` maps `randIdx` to the uniform distribution. -/
lemma LawfulRandMonad.toPMF_randIdx
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} (L : List α) (hne : 0 < L.length) :
    inst.toPMF (randIdx L hne) =
      haveI : NeZero L.length := ⟨hne.ne'⟩
      PMF.uniformOfFintype (Fin L.length) := by
  unfold randIdx
  have : NeZero L.length := ⟨hne.ne'⟩
  exact inst.toPMF_randFin L.length

/-- Derived: `toPMF` respects `Functor.map`. -/
lemma LawfulRandMonad.toPMF_map
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {α β} (f : α → β) (x : M α) :
    LawfulRandMonad.toPMF (f <$> x) =
      f <$> LawfulRandMonad.toPMF x := by
  rw [map_eq_bind_pure_comp, LawfulRandMonad.toPMF_bind]
  simp [LawfulRandMonad.toPMF_pure, map_eq_bind_pure_comp]

/-!
### Pure post-processing

Generic consequences of the three laws: a trailing `return (f x)`
transports probabilities along `f`.
-/

/-- Pure post-processing along an injective function transports
probabilities pointwise: the probability of `f a` is the probability
of `a`. Generic form of "the trailing `return (f x)` is invisible". -/
lemma toPMF_bind_pure_apply
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α β : Type} (m : M α) {f : α → β} (hf : Function.Injective f) (a : α) :
    inst.toPMF (m >>= fun x => pure (f x)) (f a) = inst.toPMF m a := by
  rw [inst.toPMF_bind, pmf_bind_eq]
  simp only [inst.toPMF_pure, pmf_pure_eq]
  rw [PMF.bind_apply, tsum_eq_single a fun x hx => ?_]
  · rw [PMF.pure_apply, if_pos rfl, mul_one]
  · rw [PMF.pure_apply, if_neg fun hc => hx (hf hc).symm, mul_zero]

/-- Off the range of `f`, the post-processed computation has
probability zero. -/
lemma toPMF_bind_pure_apply_eq_zero
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α β : Type} (m : M α) {f : α → β} {b : β} (hb : b ∉ Set.range f) :
    inst.toPMF (m >>= fun x => pure (f x)) b = 0 := by
  rw [inst.toPMF_bind, pmf_bind_eq]
  simp only [inst.toPMF_pure, pmf_pure_eq]
  rw [PMF.bind_apply]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  rw [PMF.pure_apply, if_neg fun hc => hb ⟨x, hc.symm⟩, mul_zero]

/-- `toPMF_bind_pure_apply` in the `<$>` spelling. -/
lemma toPMF_map_apply
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α β : Type} (m : M α) {f : α → β} (hf : Function.Injective f) (a : α) :
    inst.toPMF (f <$> m) (f a) = inst.toPMF m a := by
  rw [map_eq_bind_pure_comp]
  exact toPMF_bind_pure_apply m hf a

/-- `toPMF_bind_pure_apply_eq_zero` in the `<$>` spelling. -/
lemma toPMF_map_apply_eq_zero
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α β : Type} (m : M α) {f : α → β} {b : β} (hb : b ∉ Set.range f) :
    inst.toPMF (f <$> m) b = 0 := by
  rw [map_eq_bind_pure_comp]
  exact toPMF_bind_pure_apply_eq_zero m hb

/-- The support of a post-processed computation is the image of the
support: one lemma for the
`mem_support_bind_iff`/`support_pure`/`subst` unpacking dance. Use
with an `⟨a, ha, rfl⟩` pattern. -/
lemma mem_support_toPMF_bind_pure
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α β : Type} {m : M α} {f : α → β} {b : β} :
    b ∈ (inst.toPMF (m >>= fun a => pure (f a))).support ↔
      ∃ a ∈ (inst.toPMF m).support, b = f a := by
  rw [inst.toPMF_bind, pmf_bind_eq]
  simp only [inst.toPMF_pure, pmf_pure_eq]
  rw [PMF.mem_support_bind_iff]
  exact exists_congr fun a => and_congr_right fun _ => by
    rw [PMF.support_pure, Set.mem_singleton_iff]

open scoped Classical in
/-- Distribution of a `pure` program at a point, the
`toPMF_pure`/`pmf_pure_eq`/`PMF.pure_apply` triple in one step: the
base case of every distributional induction. -/
lemma toPMF_pure_apply
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type} (a b : α) :
    inst.toPMF (pure a : M α) b = if b = a then 1 else 0 := by
  rw [inst.toPMF_pure, pmf_pure_eq, PMF.pure_apply]

/-- The support of a `pure` program is the singleton, the base case
of every support induction. -/
lemma mem_support_toPMF_pure
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type} {a b : α} :
    b ∈ (inst.toPMF (pure a : M α)).support ↔ b = a := by
  rw [inst.toPMF_pure, pmf_pure_eq, PMF.mem_support_pure_iff]

/-- The support of a bind: everything reachable through a support
element of the first computation followed by a support element of its
continuation. -/
lemma mem_support_toPMF_bind
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α β : Type} {m : M α} {f : α → M β} {b : β} :
    b ∈ (inst.toPMF (m >>= f)).support ↔
      ∃ a ∈ (inst.toPMF m).support, b ∈ (inst.toPMF (f a)).support := by
  rw [inst.toPMF_bind, pmf_bind_eq, PMF.mem_support_bind_iff]

/-- Divide-and-conquer support: the support of two computations
run in sequence and combined by a pure function is the image of the
two supports. Use with an `⟨a, ha, b, hb, rfl⟩` pattern. -/
lemma mem_support_toPMF_seq₂
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α β γ : Type} {m₁ : M α} {m₂ : M β} {g : α → β → γ} {c : γ} :
    c ∈ (inst.toPMF (m₁ >>= fun a => m₂ >>= fun b =>
        pure (g a b))).support ↔
      ∃ a ∈ (inst.toPMF m₁).support, ∃ b ∈ (inst.toPMF m₂).support,
        c = g a b := by
  rw [mem_support_toPMF_bind]
  exact exists_congr fun a => and_congr_right fun _ =>
    mem_support_toPMF_bind_pure

/-!
### Notation

`𝒟_{M}[e]` is the correctness twin of `𝔼_{M}[cost e]`: the output
distribution of a monad-polymorphic algorithm, read at the random
monad `M`. A Dirac-correctness theorem then reads as English:
`𝒟_{M}[RandMax L] = PMF.pure (listMax L)`, that is "the distribution of
`RandMax` over `M` is a point mass at the maximum".
-/

/-- `𝒟_{M}[e]` ≡ `LawfulRandMonad.toPMF (e : M _)`: the output
distribution ("law") of the algorithm `e` at the random monad `M`.
Expands to the underlying form so `simp`/`rw` match the `toPMF` lemmas. -/
scoped macro "𝒟_{" M:term "}[" e:term "]" : term =>
  `(LawfulRandMonad.toPMF ($e : $M _))

/-- `𝒟[m]` ≡ `LawfulRandMonad.toPMF m`, for an already-typed
computation (no monad index needed). -/
scoped macro "𝒟[" m:term "]" : term =>
  `(LawfulRandMonad.toPMF $m)

/-!
### Canonical instances
-/

/-- `IO` has real computable (pseudo-)randomness. -/
instance : RandMonad IO where
  randFin n := do
    let i ← IO.rand 0 (n - 1)
    return ⟨i % n, Nat.mod_lt i (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/-- `PMF` is trivially a `LawfulRandMonad` via the identity. -/
noncomputable instance : RandMonad PMF where
  randFin n :=
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
    PMF.uniformOfFintype (Fin n)

noncomputable instance : LawfulRandMonad PMF where
  toPMF := id
  toPMF_pure _ := rfl
  toPMF_bind _ _ := rfl
  toPMF_randFin _ := rfl

end AlgoLib
