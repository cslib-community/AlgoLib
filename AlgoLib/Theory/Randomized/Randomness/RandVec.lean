/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import AlgoLib.Theory.Randomized.Randomness.Prob
import AlgoLib.Util.Partition
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Random vectors: `0/1` bits and uniform grid samples

The generic entropy sources for Monte-Carlo algorithms, with one
counting principle per tier: "any test accepts with probability
`#accepting / #choices`":

* the list tier, a uniform index into a list (`randIdx`) and
  `toPMF_randIdx_bind_countP`: a branch that decides a predicate at a
  uniform index accepts with probability `L.countP P / |L|`.
* the `0/1` tier, a uniform random bit (`randBit`), a uniform random
  bit vector (`randVec`), and `toPMF_randVec_true` /
  `toPMF_randVec_true_card`: testing any predicate on a random
  `0/1` vector accepts with probability
  `#{accepting bit choices} / 2^n`. Only `Zero R` and `One R` are
  assumed; `Freivalds` is the client.
* the grid tier, a uniformly random element of an arbitrary
  nonempty `Finset` (`randElem`, law `uniformOfFinset`), a vector of
  independent such draws (`randVecOn`, law: uniform on the grid
  `piFinset (fun _ => s)`), and the counting principle
  `toPMF_randVecOn_true`: any test on a uniform grid sample accepts
  with probability `#accepting / #s ^ n`. `SchwartzZippel` is the
  client.

None of the samplers ticks; the cost-tier facts live in
`Complexity/SamplerCosts.lean` (`expected_cost_randVec` and friends),
keeping `Randomness/` strictly below `Complexity/`.
-/

namespace AlgoLib

variable {R : Type} [Zero R] [One R] {n : ℕ}

/-- Sample a single uniform `0/1` entry of `R`. -/
def randBit {M} [Monad M] [RandMonad M] : M R := do
  let b ← RandMonad.randFin 2
  return if b = 0 then 0 else 1

/-- Sample a uniformly random `0/1` vector `r : Fin n → R`. -/
def randVec {M} [Monad M] [RandMonad M] : (n : ℕ) → M (Fin n → R)
  | 0 => return fun i => i.elim0
  | n + 1 => do
      let b ← (randBit : M R)
      let rest ← randVec n
      return Fin.cons b rest

/-- Interpret a bit choice as a `0/1` vector of `R`. -/
def bitVec (v : Fin n → Fin 2) : Fin n → R :=
  fun i => if v i = 0 then 0 else 1

lemma bitVec_cons (i : Fin 2) (v : Fin n → Fin 2) :
    (bitVec (Fin.cons i v) : Fin (n + 1) → R) =
      Fin.cons (if i = 0 then (0 : R) else 1) (bitVec v) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [bitVec, Fin.cons_zero]
  · simp [bitVec, Fin.cons_succ]

/-!
## The list counting principle

The simplest Monte-Carlo shape there is: draw a uniform index into a
list, accept iff the element satisfies a predicate.
-/

/-- The list counting principle. If every branch of a uniform-index
draw deterministically decides the predicate `P` at its own element,
the algorithm accepts with probability `#{i | P L[i]} / |L|`, the
list sibling of `toPMF_randVec_true` and `toPMF_randVecOn_true`.

Stated on the branch function `f`, so ticks and other lawful-invisible
work inside the branch are discharged by `toPMF_step` in the
hypothesis (`by intro i; toPMF_step`).

`L`, `hL` and `f` all occur in the conclusion, so all three are
implicit: unification should recover them from the goal, and a call
site then need not respell the branch. Only `P` is explicit, because
`P L[i]` applies `P` to `L[i]` rather than to the bound `i`. That is
not a Miller pattern, so no unifier can solve for it. The two
siblings below seem to need no argument at all for the dual reason:
their predicate sits on the bound variable. -/
theorem toPMF_randIdx_bind_countP
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type} {L : List α} {hL : 0 < L.length}
    {f : Fin L.length → M Bool} (P : α → Bool)
    (hf : ∀ i, 𝒟[f i] = PMF.pure (P L[i])) :
    ℙ[(randIdx L hL >>= f : M Bool) = true]
      = (L.countP P : ENNReal) / (L.length : ENNReal) := by
  haveI : NeZero L.length := ⟨hL.ne'⟩
  rw [inst.toPMF_bind, inst.toPMF_randIdx, pmf_bind_eq,
    pmf_uniform_fin_bind_apply]
  simp only [hf, PMF.pure_apply, eq_comm (a := true)]
  rw [sum_ite_getElem_eq_countP, ENNReal.div_eq_inv_mul]

/-- Acceptance probability as a count. Testing any predicate on a
random `0/1` vector accepts with probability
`#{accepting bit choices} / 2^n`. -/
lemma toPMF_randVec_true
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    ∀ (n : ℕ) (p : (Fin n → R) → Bool),
    ℙ[((randVec n : M (Fin n → R)) >>= fun r => pure (p r)) = true] =
      (∑ v : Fin n → Fin 2, if p (bitVec v) then (1 : ENNReal) else 0) /
        2 ^ n := by
  intro n
  induction n with
  | zero =>
    intro p
    haveI : Subsingleton (Fin 0 → R) := ⟨fun a b => funext fun i => i.elim0⟩
    rw [randVec, pure_bind, inst.toPMF_pure, pmf_pure_eq, PMF.pure_apply,
      Fintype.sum_eq_single (fun i : Fin 0 => i.elim0)
        (fun b hb => absurd (Subsingleton.elim b _) hb),
      pow_zero, div_one,
      show (bitVec (fun i : Fin 0 => i.elim0) : Fin 0 → R) = fun i => i.elim0 from
        Subsingleton.elim _ _]
    split_ifs with ha hb <;> simp_all
  | succ n ih =>
    intro p
    rw [randVec, randBit]
    simp only [bind_assoc, pure_bind]
    rw [inst.toPMF_bind, inst.toPMF_randFin, pmf_bind_eq, PMF.bind_apply,
      tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
    rw [← Finset.mul_sum]
    simp only [ih]
    -- Reindex the `2^(n+1)` bit choices by first bit × rest.
    rw [show (∑ w : Fin (n + 1) → Fin 2,
          if p (bitVec w) then (1 : ENNReal) else 0) =
        ∑ i : Fin 2, ∑ v : Fin n → Fin 2,
          if p (Fin.cons (if i = 0 then (0 : R) else 1) (bitVec v)) then
            (1 : ENNReal) else 0 from by
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ => Fin 2)
        (fun w => if p (bitVec w) then (1 : ENNReal) else 0),
        Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => by
        rw [show (Fin.consEquiv fun _ => Fin 2) (i, v) = Fin.cons i v from rfl,
          bitVec_cons]]
    -- `2⁻¹ · Σᵢ (Tᵢ / 2ⁿ) = (Σᵢ Tᵢ) / 2^(n+1)`.
    have h2 : ((2 : ENNReal) ^ (n + 1))⁻¹ = (2 ^ n)⁻¹ * 2⁻¹ := by
      rw [pow_succ, ENNReal.mul_inv (Or.inl (by positivity))
        (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))]
    simp only [ENNReal.div_eq_inv_mul]
    rw [← Finset.mul_sum, h2]
    ring_nf

/-- `toPMF_randVec_true` with the count as a `Finset.card`, the form
that lets a client count accepting bit choices in ℕ and descend once,
as `toPMF_randVecOn_true` already does for grids. -/
lemma toPMF_randVec_true_card
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (n : ℕ) (p : (Fin n → R) → Bool) :
    ℙ[((randVec n : M (Fin n → R)) >>= fun r => pure (p r)) = true] =
      ((Finset.univ.filter fun v : Fin n → Fin 2 => p (bitVec v)).card :
        ENNReal) / 2 ^ n := by
  rw [toPMF_randVec_true]
  congr 1
  rw [Finset.sum_boole]

/-!
## Uniform sampling from a finite set

`randElem s` draws a uniformly random element of a nonempty `Finset`;
`randVecOn s n` draws a vector of `n` independent such samples.
-/

/-- Sample a uniformly random element of a nonempty finite set.
(`noncomputable`: enumerating an abstract `Finset` requires choice;
an executable variant needs a canonical enumeration, e.g. a sorted
one.) -/
noncomputable def randElem {M} [Monad M] [RandMonad M] {α : Type} (s : Finset α)
    (hs : s.Nonempty) : M α := do
  let i ← randIdx s.toList (by simpa using hs.card_pos)
  pure s.toList[i]

/-- `randElem` draws uniformly: its law is `uniformOfFinset`. -/
lemma toPMF_randElem {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] {α : Type} (s : Finset α) (hs : s.Nonempty) :
    𝒟_{M}[randElem s hs] = PMF.uniformOfFinset s hs := by
  haveI : NeZero s.toList.length := ⟨(by simpa using hs.card_pos : 0 < s.toList.length).ne'⟩
  ext a
  rw [PMF.uniformOfFinset_apply, randElem, inst.toPMF_bind, inst.toPMF_randIdx,
    pmf_bind_eq, pmf_uniform_fin_bind_apply]
  simp only [inst.toPMF_pure, pmf_pure_eq, PMF.pure_apply]
  by_cases ha : a ∈ s
  · obtain ⟨j, hj, hja⟩ := List.getElem_of_mem (Finset.mem_toList.mpr ha)
    rw [if_pos ha,
      Fintype.sum_eq_single (⟨j, hj⟩ : Fin s.toList.length)
        (fun i hne => by
          refine if_neg fun hc => hne ?_
          have hc2 : a = s.toList[(i : ℕ)]'i.isLt := hc
          exact Fin.ext (s.nodup_toList.getElem_inj_iff.mp (hc2.symm.trans hja.symm))),
      if_pos (show a = s.toList[(⟨j, hj⟩ : Fin s.toList.length)] from hja.symm),
      mul_one, Finset.length_toList]
  · rw [if_neg ha,
      Finset.sum_eq_zero fun i _ => if_neg fun hc => ha (Finset.mem_toList.mp (by
        rw [hc]; exact List.getElem_mem _)),
      mul_zero]

/-- Sample a vector of `n` independent uniform draws from `s`. -/
noncomputable def randVecOn {M} [Monad M] [RandMonad M] {α : Type} (s : Finset α)
    (hs : s.Nonempty) : (n : ℕ) → M (Fin n → α)
  | 0 => return fun i => i.elim0
  | n + 1 => do
      let b ← randElem s hs
      let rest ← randVecOn s hs n
      return Fin.cons b rest

/-- Evaluate a `Fin.cons`-postprocessed draw at a vector via its
head/tail split, the Fin-tuple helper that hides the dependent-motive
friction of `Fin.cons` (the head must match; the tail carries the
recursion). -/
lemma toPMF_bind_pure_finCons
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {γ : Type} [DecidableEq γ] {n : ℕ} (m : M (Fin n → γ)) (b : γ)
    (f : Fin (n + 1) → γ) :
    inst.toPMF (m >>= fun rest => pure (Fin.cons b rest)) f =
      if f 0 = b then inst.toPMF m (Fin.tail f) else 0 := by
  by_cases hb : f 0 = b
  · rw [if_pos hb, ← hb]
    have h := toPMF_bind_pure_apply m
      (Fin.cons_right_injective (α := fun _ : Fin (n + 1) => γ) (f 0))
      (Fin.tail f)
    rwa [Fin.cons_self_tail] at h
  · rw [if_neg hb]
    exact toPMF_bind_pure_apply_eq_zero _ fun ⟨rest, hrest⟩ => hb (by
      rw [← hrest, Fin.cons_zero])

/-- Pointwise law of `randVecOn`: each grid point of `sⁿ` has
probability `(#s ^ n)⁻¹`, everything else `0`. -/
lemma toPMF_randVecOn_apply {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] {α : Type} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) :
    ∀ (n : ℕ) (f : Fin n → α),
      𝒟_{M}[randVecOn s hs n] f =
        if f ∈ Fintype.piFinset (fun _ : Fin n => s)
        then ((s.card : ENNReal) ^ n)⁻¹ else 0 := by
  intro n
  induction n with
  | zero =>
    intro f
    haveI : Subsingleton (Fin 0 → α) := ⟨fun a b => funext fun i => i.elim0⟩
    rw [randVecOn, inst.toPMF_pure, pmf_pure_eq, PMF.pure_apply,
      if_pos (Subsingleton.elim _ _),
      if_pos (Fintype.mem_piFinset.mpr fun i => Fin.elim0 i), pow_zero, inv_one]
  | succ n ih =>
    intro f
    have hc0 : (s.card : ENNReal) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    rw [randVecOn, inst.toPMF_bind, toPMF_randElem, pmf_bind_eq, PMF.bind_apply]
    have hinner : ∀ b, inst.toPMF ((randVecOn s hs n : M (Fin n → α)) >>=
        fun rest => pure (Fin.cons b rest)) f =
        if f 0 = b then 𝒟_{M}[randVecOn s hs n] (Fin.tail f) else 0 :=
      fun b => toPMF_bind_pure_finCons (randVecOn s hs n) b f
    rw [tsum_eq_single (f 0) (fun b hb => by
        rw [hinner b, if_neg fun h => hb h.symm, mul_zero]),
      hinner (f 0), if_pos rfl, ih (Fin.tail f), PMF.uniformOfFinset_apply]
    by_cases h0 : f 0 ∈ s
    · by_cases htl : Fin.tail f ∈ Fintype.piFinset (fun _ : Fin n => s)
      · rw [if_pos h0, if_pos htl,
          if_pos (Fin.mem_piFinset_iff_zero_tail.mpr ⟨h0, htl⟩), pow_succ,
          ENNReal.mul_inv (Or.inl (pow_ne_zero n hc0))
            (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]
        exact mul_comm _ _
      · rw [if_pos h0, if_neg htl, mul_zero,
          if_neg fun hmem : f ∈ Fintype.piFinset (fun _ : Fin (n + 1) => s) =>
            htl (Fin.mem_piFinset_iff_zero_tail.mp hmem).2]
    · rw [if_neg h0, zero_mul,
        if_neg fun hmem : f ∈ Fintype.piFinset (fun _ : Fin (n + 1) => s) =>
          h0 (Fin.mem_piFinset_iff_zero_tail.mp hmem).1]

/-- `randVecOn` samples uniformly from the grid: its law is the
uniform distribution on `piFinset (fun _ => s) = sⁿ`. -/
lemma toPMF_randVecOn {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] {α : Type}
    (s : Finset α) (hs : s.Nonempty) (n : ℕ) :
    𝒟_{M}[randVecOn s hs n] =
      PMF.uniformOfFinset (Fintype.piFinset fun _ : Fin n => s)
        ⟨fun _ => hs.choose, Fintype.mem_piFinset.mpr fun _ => hs.choose_spec⟩ := by
  classical
  ext f
  rw [toPMF_randVecOn_apply]
  by_cases hf : f ∈ Fintype.piFinset (fun _ : Fin n => s)
  · rw [if_pos hf, PMF.uniformOfFinset_apply, if_pos hf,
      Fintype.card_piFinset_const, Nat.cast_pow]
  · rw [if_neg hf, PMF.uniformOfFinset_apply, if_neg hf]

/-- Acceptance of a boolean test under a uniform draw from a finite
set: `#accepting / #t`. The `PMF`-level core of the grid counting
principle below (its `toPMF` sibling of `toPMF_randVec_true`). -/
lemma pmf_uniformOfFinset_bind_pure_true {α : Type*} (t : Finset α)
    (ht : t.Nonempty) (pred : α → Bool) :
    ((PMF.uniformOfFinset t ht).bind fun x => PMF.pure (pred x)) true =
      ((t.filter fun x => pred x).card : ENNReal) / (t.card : ENNReal) := by
  rw [PMF.bind_apply,
    tsum_eq_sum (s := t) fun x hx => by
      rw [PMF.uniformOfFinset_apply, if_neg hx, zero_mul]]
  have hstep : ∀ x ∈ t, (PMF.uniformOfFinset t ht) x * (PMF.pure (pred x)) true
      = (t.card : ENNReal)⁻¹ * if pred x = true then 1 else 0 := by
    intro x hx
    rw [PMF.uniformOfFinset_apply, if_pos hx, PMF.pure_apply]
    cases pred x <;> simp
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, Finset.sum_boole,
    ENNReal.div_eq_inv_mul]

/-- Acceptance probability as a grid count. Testing any predicate
on a uniform sample from the grid `sⁿ` accepts with probability
`#accepting / #s ^ n`, the `Finset` generalization of
`toPMF_randVec_true`; `SchwartzZippel` is the client. -/
lemma toPMF_randVecOn_true {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] {α : Type}
    (s : Finset α) (hs : s.Nonempty) (n : ℕ) (pred : (Fin n → α) → Bool) :
    ℙ[((randVecOn s hs n : M (Fin n → α)) >>= fun r => pure (pred r)) = true] =
      (((Fintype.piFinset fun _ : Fin n => s).filter fun f => pred f).card :
        ENNReal) / (s.card : ENNReal) ^ n := by
  rw [inst.toPMF_bind, pmf_bind_eq]
  simp only [inst.toPMF_pure, pmf_pure_eq]
  rw [toPMF_randVecOn s hs n, pmf_uniformOfFinset_bind_pure_true,
    Fintype.card_piFinset_const, Nat.cast_pow]

/-!
## Executable sampling for ordered types

`randElem`/`randVecOn` enumerate an abstract `Finset`, which needs
choice; over a `LinearOrder` the sorted enumeration is canonical and
computable, restoring `#eval` for grid algorithms. The laws coincide
(`toPMF_randElemSorted`, `toPMF_randVecOnSorted`), so every theorem
about the abstract samplers transfers verbatim.
-/

section Sorted

variable {α : Type} [LinearOrder α]

/-- Computable `randElem`: draw a uniform index into the canonical
sorted enumeration of `s`. -/
def randElemSorted {M} [Monad M] [RandMonad M]
    (s : Finset α) (hs : s.Nonempty) : M α := do
  let i ← randIdx (s.sort (· ≤ ·))
    (by rw [Finset.length_sort]; exact hs.card_pos)
  pure (s.sort (· ≤ ·))[i]

/-- The sorted sampler has the same law as the abstract one. -/
lemma toPMF_randElemSorted {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] (s : Finset α) (hs : s.Nonempty) :
    𝒟_{M}[randElemSorted s hs] = PMF.uniformOfFinset s hs := by
  haveI : NeZero (s.sort (· ≤ ·)).length :=
    ⟨by rw [Finset.length_sort]; exact hs.card_pos.ne'⟩
  ext a
  rw [PMF.uniformOfFinset_apply, randElemSorted, inst.toPMF_bind,
    inst.toPMF_randIdx, pmf_bind_eq, pmf_uniform_fin_bind_apply]
  simp only [inst.toPMF_pure, pmf_pure_eq, PMF.pure_apply]
  by_cases ha : a ∈ s
  · obtain ⟨j, hj, hja⟩ :=
      List.getElem_of_mem ((Finset.mem_sort (α := α) (· ≤ ·)).mpr ha)
    rw [if_pos ha,
      Fintype.sum_eq_single (⟨j, hj⟩ : Fin (s.sort (· ≤ ·)).length)
        (fun i hne => by
          refine if_neg fun hc => hne ?_
          have hc2 : a = (s.sort (· ≤ ·))[(i : ℕ)]'i.isLt := hc
          exact Fin.ext ((s.sort_nodup (· ≤ ·)).getElem_inj_iff.mp
            (hc2.symm.trans hja.symm))),
      if_pos (show a = (s.sort (· ≤ ·))[(⟨j, hj⟩ :
        Fin (s.sort (· ≤ ·)).length)] from hja.symm),
      mul_one, Finset.length_sort]
  · rw [if_neg ha]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ?_)
    exact if_neg fun hc =>
      ha ((Finset.mem_sort (α := α) (· ≤ ·)).mp (by
        rw [hc]; exact List.getElem_mem _))

/-- Computable `randVecOn`: a vector of independent sorted draws. -/
def randVecOnSorted {M} [Monad M] [RandMonad M]
    (s : Finset α) (hs : s.Nonempty) : (n : ℕ) → M (Fin n → α)
  | 0 => return fun i => i.elim0
  | n + 1 => do
      let b ← randElemSorted s hs
      let rest ← randVecOnSorted s hs n
      return Fin.cons b rest

/-- The sorted grid sampler has the same law as the abstract one:
every theorem about `randVecOn` applies to the executable variant. -/
lemma toPMF_randVecOnSorted {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] (s : Finset α) (hs : s.Nonempty) :
    ∀ n, 𝒟_{M}[randVecOnSorted s hs n] = 𝒟_{M}[randVecOn s hs n] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [randVecOnSorted, randVecOn, inst.toPMF_bind, inst.toPMF_bind,
      toPMF_randElemSorted, toPMF_randElem]
    refine congrArg _ (funext fun b => ?_)
    rw [inst.toPMF_bind, inst.toPMF_bind, ih]

-- The demo seam (a) asked for: grid sampling now runs under `IO`.
#eval (randVecOnSorted ({2, 3, 5, 7} : Finset ℕ) (by decide) 3 :
    IO (Fin 3 → ℕ)) >>= fun v => pure (List.ofFn v)

end Sorted

end AlgoLib
