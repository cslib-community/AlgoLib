import Benchmarks.Hierholzer.GraphLib.Algorithm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Nat.Even

/-!
# Functional correctness of the timed GraphLib Hierholzer core

The proof is carried out over dense IDs and transported pointwise through the frozen decoder.
-/

set_option autoImplicit false

namespace Benchmarks.Hierholzer.GraphLib

open Cslib.Algorithms.Lean
open Benchmarks.Hierholzer.Common
open scoped _root_.GraphLib BigOperators

universe u v

variable {α : Type u} {β : Type v}
variable {G : _root_.GraphLib.Graph α β} [Finite V(G)] [Finite E(G)]

/-- Dense form of the frozen full-actual-edge link relation. -/
def DenseLink (R : CertifiedIncidenceRepresentation G) (edgeId : Fin R.m)
    (x y : Fin R.n) : Prop :=
  Link G (R.decodeEdge edgeId) (R.decodeVertex x) (R.decodeVertex y)

@[symm] theorem DenseLink.symm {R : CertifiedIncidenceRepresentation G}
    {edgeId : Fin R.m} {x y : Fin R.n} (h : DenseLink R edgeId x y) :
    DenseLink R edgeId y x := by
  exact _root_.GraphLib.Graph.IsLink.symm h

/-- A list of canonical `(edge,destination)` steps is a linked walk from `source` to `target`. -/
inductive DenseWalkSteps (R : CertifiedIncidenceRepresentation G) :
    Fin R.n → List (Fin R.m × Fin R.n) → Fin R.n → Prop
  | nil (vertex) : DenseWalkSteps R vertex [] vertex
  | cons {source middle target edgeId rest}
      (link : DenseLink R edgeId source middle)
      (tail : DenseWalkSteps R middle rest target) :
      DenseWalkSteps R source ((edgeId, middle) :: rest) target

namespace DenseWalkSteps

theorem append {R : CertifiedIncidenceRepresentation G} {a b c : Fin R.n}
    {xs ys : List (Fin R.m × Fin R.n)}
    (hxs : DenseWalkSteps R a xs b) (hys : DenseWalkSteps R b ys c) :
    DenseWalkSteps R a (xs ++ ys) c := by
  induction hxs with
  | nil => simpa using hys
  | cons link tail ih => exact .cons link (ih hys)

theorem snoc_iff {R : CertifiedIncidenceRepresentation G} {a c : Fin R.n}
    {xs : List (Fin R.m × Fin R.n)} {edgeId : Fin R.m} {dest : Fin R.n} :
    DenseWalkSteps R a (xs ++ [(edgeId, dest)]) c ↔
      c = dest ∧ ∃ middle, DenseWalkSteps R a xs middle ∧ DenseLink R edgeId middle dest := by
  constructor
  · intro h
    induction xs generalizing a with
    | nil =>
        cases h with
        | cons link tail =>
            cases tail
            exact ⟨rfl, a, .nil _, link⟩
    | cons step xs ih =>
        rcases step with ⟨firstEdge, firstDest⟩
        cases h with
        | cons link tail =>
            obtain ⟨rfl, middle, htail, hlast⟩ := ih tail
            exact ⟨rfl, middle, .cons link htail, hlast⟩
  · rintro ⟨rfl, middle, hprefix, hlast⟩
    exact hprefix.append (.cons hlast (.nil _))

theorem length_vertices {R : CertifiedIncidenceRepresentation G} {a b : Fin R.n}
    {steps : List (Fin R.m × Fin R.n)} (h : DenseWalkSteps R a steps b) :
    (a :: steps.map Prod.snd).length = steps.length + 1 := by simp

end DenseWalkSteps

/-- Loop-corrected incidence weight of one actual dense edge at a dense vertex. -/
noncomputable def edgeWeight (R : CertifiedIncidenceRepresentation G) (vertexId : Fin R.n)
    (edgeId : Fin R.m) : Nat := by
  classical
  exact (if Inc G (R.decodeEdge edgeId) (R.decodeVertex vertexId) then 1 else 0) +
    (if Loop G (R.decodeEdge edgeId) (R.decodeVertex vertexId) then 1 else 0)

/-- Incidence weight used by a dense step list. -/
noncomputable def usedDegree (R : CertifiedIncidenceRepresentation G) (vertexId : Fin R.n)
    (steps : List (Fin R.m × Fin R.n)) : Nat :=
  (steps.map fun step => edgeWeight R vertexId step.1).sum

private theorem link_inc_iff {R : CertifiedIncidenceRepresentation G}
    {edgeId : Fin R.m} {x y z : Fin R.n} (h : DenseLink R edgeId x y) :
    Inc G (R.decodeEdge edgeId) (R.decodeVertex z) ↔ z = x ∨ z = y := by
  constructor
  · intro hz
    rcases hz with ⟨other, hother⟩
    have hend := (_root_.GraphLib.Graph.IsLink.endpoints_eq h)
    have hzmem : (R.decodeVertex z).1 ∈ (R.decodeEdge edgeId).1.endpoints :=
      (_root_.GraphLib.Graph.IsLink.inc_left hother).2
    rw [hend] at hzmem
    simp only [Sym2.mem_iff] at hzmem
    rcases hzmem with hzmem | hzmem
    · left
      exact R.decodeVertex.injective (Subtype.ext hzmem)
    · right
      exact R.decodeVertex.injective (Subtype.ext hzmem)
  · rintro (rfl | rfl)
    · exact ⟨R.decodeVertex y, h⟩
    · exact ⟨R.decodeVertex x, h.symm⟩

private theorem link_loop_iff {R : CertifiedIncidenceRepresentation G}
    {edgeId : Fin R.m} {x y z : Fin R.n} (h : DenseLink R edgeId x y) :
    Loop G (R.decodeEdge edgeId) (R.decodeVertex z) ↔ z = x ∧ z = y := by
  constructor
  · intro hz
    have heq : s((R.decodeVertex x).1, (R.decodeVertex y).1) =
        s((R.decodeVertex z).1, (R.decodeVertex z).1) := by
      rw [← _root_.GraphLib.Graph.IsLink.endpoints_eq h,
        ← _root_.GraphLib.Graph.IsLink.endpoints_eq hz]
    rw [Sym2.eq_iff] at heq
    rcases heq with hxy | hxy
    · exact ⟨R.decodeVertex.injective (Subtype.ext hxy.1.symm),
        R.decodeVertex.injective (Subtype.ext hxy.2.symm)⟩
    · exact ⟨R.decodeVertex.injective (Subtype.ext hxy.1.symm),
        R.decodeVertex.injective (Subtype.ext hxy.2.symm)⟩
  · rintro ⟨rfl, rfl⟩
    exact h

theorem edgeWeight_of_link {R : CertifiedIncidenceRepresentation G}
    {edgeId : Fin R.m} {x y z : Fin R.n} (h : DenseLink R edgeId x y) :
    edgeWeight R z edgeId = (if z = x then 1 else 0) + (if z = y then 1 else 0) := by
  classical
  rw [edgeWeight, if_congr (link_inc_iff h) rfl rfl, if_congr (link_loop_iff h) rfl rfl]
  by_cases hzx : z = x <;> by_cases hzy : z = y <;> simp [hzx, hzy] <;> omega

theorem DenseLink.left_eq_of_right {R : CertifiedIncidenceRepresentation G}
    {edgeId : Fin R.m} {a b common : Fin R.n}
    (ha : DenseLink R edgeId a common) (hb : DenseLink R edgeId b common) : a = b := by
  have hbInc : Inc G (R.decodeEdge edgeId) (R.decodeVertex b) :=
    ⟨R.decodeVertex common, hb⟩
  rcases (link_inc_iff ha).mp hbInc with hba | hbc
  · exact hba.symm
  · subst b
    have hloop : Loop G (R.decodeEdge edgeId) (R.decodeVertex common) := hb
    exact ((link_loop_iff ha).mp hloop).1.symm

/-- Parity of the used degree of a walk is determined by its two endpoints. -/
theorem usedDegree_even_iff_endpoints {R : CertifiedIncidenceRepresentation G}
    {source target vertexId : Fin R.n} {steps : List (Fin R.m × Fin R.n)}
    (hwalk : DenseWalkSteps R source steps target) :
    Even (usedDegree R vertexId steps) ↔ (source = vertexId ↔ target = vertexId) := by
  induction hwalk with
  | nil => simp [usedDegree]
  | @cons source middle target edgeId rest link tail ih =>
      change Even (edgeWeight R vertexId edgeId + usedDegree R vertexId rest) ↔ _
      rw [edgeWeight_of_link link, Nat.even_add]
      simp only [Nat.even_add]
      rw [ih]
      by_cases hsv : source = vertexId <;> by_cases hmv : middle = vertexId <;>
        by_cases htv : target = vertexId <;> simp_all [Nat.even_add, eq_comm]

private theorem ncard_predicate_eq_sum_ite {γ : Type*} [Fintype γ] (p : γ → Prop)
    [DecidablePred p] :
    Set.ncard {x : γ | p x} = ∑ x : γ, if p x then 1 else 0 := by
  rw [Set.ncard_eq_toFinset_card]
  simp

/-- The adapter degree is the sum of loop-corrected weights over all dense actual-edge IDs. -/
theorem degree_eq_sum_edgeWeight (R : CertifiedIncidenceRepresentation G)
    (vertexId : Fin R.n) :
    degree G (R.decodeVertex vertexId) = ∑ edgeId : Fin R.m, edgeWeight R vertexId edgeId := by
  classical
  letI : Fintype (ActualEdge G) := Fintype.ofFinite (ActualEdge G)
  rw [degree]
  rw [ncard_predicate_eq_sum_ite, ncard_predicate_eq_sum_ite]
  rw [← Finset.sum_add_distrib]
  symm
  calc
    (∑ edgeId : Fin R.m, edgeWeight R vertexId edgeId) =
        ∑ edgeId : Fin R.m,
          ((if Inc G (R.decodeEdge edgeId) (R.decodeVertex vertexId) then 1 else 0) +
            if Loop G (R.decodeEdge edgeId) (R.decodeVertex vertexId) then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro edgeId _
              simp only [edgeWeight]
    _ = ∑ edge : ActualEdge G,
          ((if Inc G edge (R.decodeVertex vertexId) then 1 else 0) +
            if Loop G edge (R.decodeVertex vertexId) then 1 else 0) := by
      simpa using R.decodeEdge.sum_comp (fun edge : ActualEdge G =>
        ((if Inc G edge (R.decodeVertex vertexId) then 1 else 0) +
          if Loop G edge (R.decodeVertex vertexId) then 1 else 0))

/-- A no-duplicate step list containing every edge incident with `vertexId` has the full degree
there. -/
theorem usedDegree_eq_degree_of_incident_complete
    (R : CertifiedIncidenceRepresentation G) (vertexId : Fin R.n)
    (steps : List (Fin R.m × Fin R.n))
    (hnodup : (steps.map Prod.fst).Nodup)
    (hcomplete : ∀ edgeId, Inc G (R.decodeEdge edgeId) (R.decodeVertex vertexId) →
      edgeId ∈ steps.map Prod.fst) :
    usedDegree R vertexId steps = degree G (R.decodeVertex vertexId) := by
  classical
  rw [degree_eq_sum_edgeWeight]
  rw [usedDegree]
  let ids := steps.map Prod.fst
  rw [show steps.map (fun step => edgeWeight R vertexId step.1) =
      ids.map (edgeWeight R vertexId) by simp [ids, List.map_map, Function.comp_def]]
  rw [← List.sum_toFinset (edgeWeight R vertexId) hnodup]
  apply Fintype.sum_subset
  intro edgeId hweight
  apply List.mem_toFinset.mpr
  apply hcomplete edgeId
  by_contra hnotInc
  have hnotLoop : ¬Loop G (R.decodeEdge edgeId) (R.decodeVertex vertexId) := by
    intro hloop
    exact hnotInc ⟨R.decodeVertex vertexId, hloop⟩
  simp [edgeWeight, hnotInc, hnotLoop] at hweight

/-- The parity argument used exactly when the algorithm backtracks from an exhausted vertex. -/
theorem walk_closes_at_even_exhausted
    (R : CertifiedIncidenceRepresentation G) {source target : Fin R.n}
    {steps : List (Fin R.m × Fin R.n)}
    (hwalk : DenseWalkSteps R source steps target)
    (hnodup : (steps.map Prod.fst).Nodup)
    (hcomplete : ∀ edgeId, Inc G (R.decodeEdge edgeId) (R.decodeVertex target) →
      edgeId ∈ steps.map Prod.fst)
    (heven : Even (degree G (R.decodeVertex target))) : source = target := by
  have hdegree := usedDegree_eq_degree_of_incident_complete R target steps hnodup hcomplete
  have husedEven : Even (usedDegree R target steps) := by simpa [hdegree]
  exact (usedDegree_even_iff_endpoints hwalk).mp husedEven |>.mpr rfl

@[simp] theorem CoreState.usedAt_setUsed {n m : Nat} (state : CoreState n m)
    (written queried : Fin m) (value : Bool) :
    (state.setUsed written value).usedAt queried =
      if queried = written then value else state.usedAt queried := by
  classical
  by_cases h : queried = written
  · subst queried
    simp
  · have hval : written.1 ≠ queried.1 := fun heq => h (Fin.ext heq.symm)
    simp only [h, ↓reduceIte]
    unfold CoreState.setUsed CoreState.usedAt vectorGet
    change (state.used.set written.1 value written.2)[queried.1] = state.used[queried.1]
    apply Array.getElem_set_ne
    · simpa using queried.2
    · exact hval

@[simp] theorem CoreState.cursorAt_setCursor {n m : Nat} (state : CoreState n m)
    (written queried : Fin n) (value : Nat) :
    (state.setCursor written value).cursorAt queried =
      if queried = written then value else state.cursorAt queried := by
  classical
  by_cases h : queried = written
  · subst queried
    simp
  · have hval : written.1 ≠ queried.1 := fun heq => h (Fin.ext heq.symm)
    simp only [h, ↓reduceIte]
    unfold CoreState.setCursor CoreState.cursorAt vectorGet
    change (state.cursors.set written.1 value written.2)[queried.1] =
      state.cursors[queried.1]
    apply Array.getElem_set_ne
    · simpa using queried.2
    · exact hval

@[simp] theorem CoreState.cursorAt_setUsed {n m : Nat} (state : CoreState n m)
    (edgeId : Fin m) (value : Bool) (vertexId : Fin n) :
    (state.setUsed edgeId value).cursorAt vertexId = state.cursorAt vertexId := rfl

@[simp] theorem CoreState.usedAt_setCursor {n m : Nat} (state : CoreState n m)
    (vertexId : Fin n) (value : Nat) (edgeId : Fin m) :
    (state.setCursor vertexId value).usedAt edgeId = state.usedAt edgeId := rfl

/-- Every entry of an all-equal input vector remains equal after the charged push loop. -/
private theorem initVectorLoop_all {γ : Type*} (value : γ) (remaining : Nat)
    {built : Nat} (result : Vector γ built) (hall : ∀ i, vectorGet result i = value) :
    ∀ i, vectorGet (initVectorLoop value remaining result).ret i = value := by
  induction remaining generalizing built with
  | zero =>
      intro i
      simpa [initVectorLoop, vectorGet] using hall (i.cast (by omega))
  | succ remaining ih =>
      intro i
      have hpush : ∀ j, vectorGet (result.push value) j = value := by
        intro j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp [vectorGet]
        · simpa [vectorGet] using hall k
      have hrec := ih (built := built + 1) (result := result.push value) hpush
      simpa [initVectorLoop, vectorGet] using hrec (i.cast (by omega))

@[simp] theorem vectorGet_initVector {γ : Type*} (size : Nat) (value : γ) (i : Fin size) :
    vectorGet (initVector size value).ret i = value := by
  let empty : Vector γ 0 := ⟨Array.mkEmpty size, by simp⟩
  have hrec := initVectorLoop_all value size empty (fun j => Fin.elim0 j)
  simpa [initVector, empty, vectorGet] using hrec (i.cast (by omega))

@[simp] theorem initialize_usedAt {n m : Nat} (start : Fin n) (edgeId : Fin m) :
    (initializeState (m := m) start).ret.usedAt edgeId = false := by
  change vectorGet (initVector m false).ret edgeId = false
  exact vectorGet_initVector m false edgeId

@[simp] theorem initialize_cursorAt {n m : Nat} (start : Fin n) (vertexId : Fin n) :
    (initializeState (m := m) start).ret.cursorAt vertexId = 0 := by
  change vectorGet (initVector n 0).ret vertexId = 0
  exact vectorGet_initVector n 0 vertexId

/-- Remaining unscanned capacity across all persistent adjacency cursors. -/
def remainingDarts (R : CertifiedIncidenceRepresentation G) (state : CoreState R.n R.m) : Nat :=
  Finset.univ.sum (fun vertexId : Fin R.n =>
    (R.bucket vertexId).size - CoreState.cursorAt state vertexId)

theorem remainingDarts_initialize (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) :
    remainingDarts R (initializeState (m := R.m) start).ret = R.incidenceCount := by
  simp [remainingDarts, CertifiedIncidenceRepresentation.incidenceCount]

theorem remainingDarts_setCursor_succ (R : CertifiedIncidenceRepresentation G)
    (state : CoreState R.n R.m) (vertexId : Fin R.n) (position : Nat)
    (hcursor : state.cursorAt vertexId = position)
    (hposition : position < (R.bucket vertexId).size) :
    remainingDarts R (state.setCursor vertexId (position + 1)) + 1 =
      remainingDarts R state := by
  classical
  rw [remainingDarts, remainingDarts]
  rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) vertexId (fun x =>
    (R.bucket x).size - (state.setCursor vertexId (position + 1)).cursorAt x) (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) vertexId (fun x =>
    (R.bucket x).size - state.cursorAt x) (by simp)]
  have hrest :
      Finset.sum (Finset.univ \ {vertexId}) (fun x =>
          (R.bucket x).size - (state.setCursor vertexId (position + 1)).cursorAt x) =
        Finset.sum (Finset.univ \ {vertexId}) (fun x =>
          (R.bucket x).size - state.cursorAt x) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ vertexId := by simpa using hx
    simp [hne]
  rw [hrest]
  simp [hcursor]
  omega

/-- Cursor bounds, exact remaining-fuel potential, and the fact that every strict cursor prefix is
already marked used. -/
structure CursorInvariant (R : CertifiedIncidenceRepresentation G)
    (dartFuel : Nat) (state : CoreState R.n R.m) : Prop where
  cursor_le : ∀ vertexId, state.cursorAt vertexId ≤ (R.bucket vertexId).size
  remaining_eq : remainingDarts R state = dartFuel
  prefix_used : ∀ vertexId position (hposition : position < (R.bucket vertexId).size),
    position < state.cursorAt vertexId → state.usedAt (R.bucket vertexId)[position].1 = true

theorem cursorInvariant_initialize (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) :
    CursorInvariant R (R.m + R.m) (initializeState (m := R.m) start).ret := by
  constructor
  · intro vertexId
    simp
  · rw [remainingDarts_initialize, R.incidenceCount_eq_twice_edgeCount]
    omega
  · intro vertexId position hposition hlt
    simp at hlt

theorem remainingDarts_term_le (R : CertifiedIncidenceRepresentation G)
    (state : CoreState R.n R.m) (vertexId : Fin R.n) :
    (R.bucket vertexId).size - state.cursorAt vertexId ≤ remainingDarts R state := by
  classical
  rw [remainingDarts]
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun queried : Fin R.n =>
      (R.bucket queried).size - state.cursorAt queried)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ vertexId)

theorem CursorInvariant.advance_used (R : CertifiedIncidenceRepresentation G)
    {fuel position : Nat} {state : CoreState R.n R.m}
    (vertexId : Fin R.n) (hInv : CursorInvariant R (fuel + 1) state)
    (hcursor : state.cursorAt vertexId = position)
    (hposition : position < (R.bucket vertexId).size)
    (hused : state.usedAt (R.bucket vertexId)[position].1 = true) :
    CursorInvariant R fuel (state.setCursor vertexId (position + 1)) := by
  constructor
  · intro queried
    by_cases hq : queried = vertexId
    · subst queried
      simp
      omega
    · simpa [hq] using hInv.cursor_le queried
  · have hrem := remainingDarts_setCursor_succ R state vertexId position hcursor hposition
    rw [hInv.remaining_eq] at hrem
    omega
  · intro queried index hindex hlt
    by_cases hq : queried = vertexId
    · subst queried
      simp only [CoreState.cursorAt_setCursor, ↓reduceIte] at hlt
      have hle : index ≤ position := by omega
      rcases lt_or_eq_of_le hle with hbefore | rfl
      · exact hInv.prefix_used vertexId index hindex (by simpa [hcursor] using hbefore)
      · simpa using hused
    · have hbefore : index < state.cursorAt queried := by simpa [hq] using hlt
      exact hInv.prefix_used queried index hindex hbefore

theorem CursorInvariant.advance_setUsed (R : CertifiedIncidenceRepresentation G)
    {fuel position : Nat} {state : CoreState R.n R.m}
    (vertexId : Fin R.n) (hInv : CursorInvariant R (fuel + 1) state)
    (hcursor : state.cursorAt vertexId = position)
    (hposition : position < (R.bucket vertexId).size) :
    let edgeId := (R.bucket vertexId)[position].1
    CursorInvariant R fuel
      ((state.setCursor vertexId (position + 1)).setUsed edgeId true) := by
  intro edgeId
  constructor
  · intro queried
    by_cases hq : queried = vertexId
    · subst queried
      simp
      omega
    · simpa [hq] using hInv.cursor_le queried
  · have hrem := remainingDarts_setCursor_succ R state vertexId position hcursor hposition
    change remainingDarts R (state.setCursor vertexId (position + 1)) = fuel
    rw [hInv.remaining_eq] at hrem
    omega
  · intro queried index hindex hlt
    by_cases hq : queried = vertexId
    · subst queried
      simp only [CoreState.cursorAt_setUsed, CoreState.cursorAt_setCursor, ↓reduceIte] at hlt
      have hle : index ≤ position := by omega
      rcases lt_or_eq_of_le hle with hbefore | rfl
      · have hold := hInv.prefix_used vertexId index hindex (by simpa [hcursor] using hbefore)
        simp [hold]
      · change
          ((state.setCursor vertexId (index + 1)).setUsed
            (R.bucket vertexId)[index].1 true).usedAt
              (R.bucket vertexId)[index].1 = true
        simp
    · have hbefore : index < state.cursorAt queried := by
        simpa [hq] using hlt
      have hold := hInv.prefix_used queried index hindex hbefore
      simp [hold]

/-- The semantic facts exposed by one adjacency scan.  A successful scan leaves its returned
edge unmarked for the caller, so its cursor invariant is stated after that one pending mark. -/
structure ScanCorrect (R : CertifiedIncidenceRepresentation G) (vertexId : Fin R.n)
    (initial : CoreState R.n R.m)
    (result : Option (Dart R.m) × CoreState R.n R.m × Nat) : Prop where
  used_eq : ∀ edgeId, result.2.1.usedAt edgeId = initial.usedAt edgeId
  cursor_mono : ∀ queried, initial.cursorAt queried ≤ result.2.1.cursorAt queried
  stack_eq : result.2.1.stack = initial.stack
  output_eq : result.2.1.outputSteps = initial.outputSteps
  outcome : match result.1 with
    | some dart =>
        R.dartVertex dart = vertexId ∧
        result.2.1.usedAt dart.1 = false ∧
        CursorInvariant R result.2.2 (result.2.1.setUsed dart.1 true)
    | none =>
        CursorInvariant R result.2.2 result.2.1 ∧
        result.2.1.cursorAt vertexId = (R.bucket vertexId).size

theorem scanBucket_correct (R : CertifiedIncidenceRepresentation G)
    (vertexId : Fin R.n) (bucket : BucketView R.m)
    (hentries : bucket.entries = R.bucket vertexId)
    (dartFuel position : Nat) (state : CoreState R.n R.m)
    (hInv : CursorInvariant R dartFuel state)
    (hcursor : state.cursorAt vertexId = position) :
    ScanCorrect R vertexId state (scanBucket R vertexId bucket dartFuel position state).ret := by
  induction dartFuel generalizing position state with
  | zero =>
      have hterm := remainingDarts_term_le R state vertexId
      have heq : state.cursorAt vertexId = (R.bucket vertexId).size := by
        rw [hInv.remaining_eq] at hterm
        have := hInv.cursor_le vertexId
        omega
      simp [scanBucket]
      exact ⟨fun _ => rfl, fun _ => le_rfl, rfl, rfl, hInv, heq⟩
  | succ fuel ih =>
      rw [scanBucket]
      split
      next hBounds =>
        have hnot : ¬position < bucket.size := by
          simpa [Event.indexLt] using of_decide_eq_false hBounds
        have heq : state.cursorAt vertexId = (R.bucket vertexId).size := by
          have hle := hInv.cursor_le vertexId
          have hsize : bucket.size = (R.bucket vertexId).size := by
            rw [bucket.size_eq, hentries]
          omega
        simp
        exact ⟨fun _ => rfl, fun _ => le_rfl, rfl, rfl, hInv, heq⟩
      next hBounds =>
        have harray : position < bucket.entries.size := by
          have hlt : position < bucket.size := by
            simpa [Event.indexLt] using of_decide_eq_true hBounds
          simpa [bucket.size_eq] using hlt
        let dart : Dart R.m := bucket.entries[position]'harray
        have hdartMem : dart ∈ (R.bucket vertexId).toList := by
          rw [← hentries]
          exact Array.getElem_mem_toList harray
        have hdartVertex : R.dartVertex dart = vertexId :=
          (R.dart_mem_bucket_iff vertexId dart).mp hdartMem
        have hpositionR : position < (R.bucket vertexId).size := by
          simpa [hentries] using harray
        have hcursorStep :
            (state.setCursor vertexId (position + 1)).cursorAt vertexId = position + 1 := by simp
        by_cases hused :
            (state.setCursor vertexId (position + 1)).usedAt dart.1 = true
        · have hnextInv : CursorInvariant R fuel
              (state.setCursor vertexId (position + 1)) := by
            apply hInv.advance_used R vertexId hcursor hpositionR
            simpa [dart, hentries] using hused
          have hrec := ih (position := position + 1)
            (state := state.setCursor vertexId (position + 1)) hnextInv hcursorStep
          dsimp [dart] at hused hrec ⊢
          simp [hused]
          refine ⟨?_, ?_, hrec.stack_eq, hrec.output_eq, hrec.outcome⟩
          intro edgeId
          rw [hrec.used_eq]
          rfl
          intro queried
          apply le_trans ?_ (hrec.cursor_mono queried)
          by_cases hq : queried = vertexId
          · subst queried
            simp [hcursor]
          · simp [hq]
        · have hfalse :
              (state.setCursor vertexId (position + 1)).usedAt dart.1 = false := by
            cases hvalue : (state.setCursor vertexId (position + 1)).usedAt dart.1
            · rfl
            · exact (hused hvalue).elim
          have hnextInv : CursorInvariant R fuel
              ((state.setCursor vertexId (position + 1)).setUsed dart.1 true) := by
            have := hInv.advance_setUsed R vertexId hcursor hpositionR
            simpa [dart, hentries] using this
          dsimp [dart] at hfalse hnextInv hdartVertex ⊢
          simp [hfalse]
          refine ⟨?_, ?_, rfl, rfl, hdartVertex, hfalse, hnextInv⟩
          intro edgeId
          rfl
          intro queried
          by_cases hq : queried = vertexId
          · subst queried
            simp [hcursor]
          · simp [hq]

theorem nextIncident_correct (R : CertifiedIncidenceRepresentation G)
    (vertexId : Fin R.n) (dartFuel : Nat) (state : CoreState R.n R.m)
    (hInv : CursorInvariant R dartFuel state) :
    ScanCorrect R vertexId state (nextIncident R vertexId dartFuel state).ret := by
  simp only [nextIncident, TimeM.ret_bind, Event.ret_incidenceRead, Event.ret_cursorRead]
  let entries := R.bucket vertexId
  let bucket : BucketView R.m := ⟨entries, entries.size, rfl⟩
  exact scanBucket_correct R vertexId bucket (by simp [bucket, entries]) dartFuel
    (state.cursorAt vertexId) state hInv rfl

/-- Bottom-to-top stack edges, in traversal order. -/
def stackSteps {n m : Nat} : List (Frame n m) → List (Fin m × Fin n)
  | [] => []
  | frame :: rest =>
      stackSteps rest ++ (frame.incoming.map (fun edgeId => (edgeId, frame.vertex))).toList

@[simp] theorem stackSteps_nil {n m : Nat} : stackSteps ([] : List (Frame n m)) = [] := rfl

@[simp] theorem stackSteps_cons_none {n m : Nat} (vertexId : Fin n)
    (rest : List (Frame n m)) :
    stackSteps ({ vertex := vertexId, incoming := none } :: rest) = stackSteps rest := by
  simp [stackSteps]

@[simp] theorem stackSteps_cons_some {n m : Nat} (vertexId : Fin n) (edgeId : Fin m)
    (rest : List (Frame n m)) :
    stackSteps ({ vertex := vertexId, incoming := some edgeId } :: rest) =
      stackSteps rest ++ [(edgeId, vertexId)] := by
  simp [stackSteps]

/-- The root frame is the unique `none` frame and remains at the bottom of every nonempty stack;
each pushed frame records the edge that links it to the previous top. -/
inductive StackShape (R : CertifiedIncidenceRepresentation G) (start : Fin R.n) :
    List (Frame R.n R.m) → Prop
  | root : StackShape R start [{ vertex := start, incoming := none }]
  | push {parent : Frame R.n R.m} {rest : List (Frame R.n R.m)}
      (shape : StackShape R start (parent :: rest))
      {vertexId : Fin R.n} {edgeId : Fin R.m}
      (link : DenseLink R edgeId parent.vertex vertexId) :
      StackShape R start ({ vertex := vertexId, incoming := some edgeId } :: parent :: rest)

namespace StackShape

theorem nonempty {R : CertifiedIncidenceRepresentation G} {start : Fin R.n}
    {stack : List (Frame R.n R.m)}
    (shape : StackShape R start stack) : stack ≠ [] := by
  cases shape <;> simp

theorem steps_length {R : CertifiedIncidenceRepresentation G} {start : Fin R.n}
    {stack : List (Frame R.n R.m)}
    (shape : StackShape R start stack) : (stackSteps stack).length + 1 = stack.length := by
  induction shape with
  | root => simp
  | push shape link ih => simp [ih]

theorem of_cons_some {R : CertifiedIncidenceRepresentation G}
    {start vertexId : Fin R.n} {edgeId : Fin R.m}
    {rest : List (Frame R.n R.m)}
    (shape : StackShape R start ({ vertex := vertexId, incoming := some edgeId } :: rest)) :
    ∃ parent tail, rest = parent :: tail ∧ StackShape R start rest ∧
      DenseLink R edgeId parent.vertex vertexId := by
  cases shape with
  | push shape link => exact ⟨_, _, rfl, shape, link⟩

theorem cons_none_eq_root {R : CertifiedIncidenceRepresentation G}
    {start vertexId : Fin R.n} {rest : List (Frame R.n R.m)}
    (shape : StackShape R start ({ vertex := vertexId, incoming := none } :: rest)) :
    vertexId = start ∧ rest = [] := by
  cases shape with
  | root => exact ⟨rfl, rfl⟩

end StackShape

/-- The live edge sequence: already emitted closed material followed by the bottom-to-top stack
trail.  A pop rotates its last edge to the front without changing this sequence as a multiset. -/
def chainSteps {n m : Nat} (state : CoreState n m) : List (Fin m × Fin n) :=
  state.outputSteps ++ stackSteps state.stack

/-- Main semantic invariant of the iterative implementation. -/
structure CoreInvariant (R : CertifiedIncidenceRepresentation G) (start : Fin R.n)
    (dartFuel : Nat) (state : CoreState R.n R.m) : Prop where
  cursor : CursorInvariant R dartFuel state
  shape : state.stack = [] ∨ StackShape R start state.stack
  walk_empty : state.stack = [] → DenseWalkSteps R start state.outputSteps start
  walk_nonempty : ∀ frame rest, state.stack = frame :: rest →
    ∃ source, DenseWalkSteps R source (chainSteps state) frame.vertex
  used_iff : ∀ edgeId, state.usedAt edgeId = true ↔ edgeId ∈ (chainSteps state).map Prod.fst
  edges_nodup : ((chainSteps state).map Prod.fst).Nodup
  output_exhausted : ∀ edgeId vertexId, (edgeId, vertexId) ∈ state.outputSteps →
    state.cursorAt vertexId = (R.bucket vertexId).size
  start_exhausted_if_empty : state.stack = [] →
    state.cursorAt start = (R.bucket start).size

theorem coreInvariant_initialize (R : CertifiedIncidenceRepresentation G) (start : Fin R.n) :
    CoreInvariant R start (R.m + R.m) (initializeState (m := R.m) start).ret := by
  constructor
  · exact cursorInvariant_initialize R start
  · right
    exact .root
  · intro h
    simp [initializeState] at h
  · intro frame rest hstack
    simp [initializeState] at hstack
    obtain ⟨rfl, rfl⟩ := hstack
    exact ⟨start, by simp [chainSteps]; exact .nil start⟩
  · intro edgeId
    simp [chainSteps, initializeState, stackSteps]
    exact initialize_usedAt start edgeId
  · simp [chainSteps, initializeState, stackSteps]
  · intro edgeId vertexId hmem
    simp [initializeState] at hmem
  · intro hstack
    simp [initializeState] at hstack

/-- Every mathematical incidence has at least one corresponding dart in the certified bucket. -/
theorem incident_has_bucket_dart (R : CertifiedIncidenceRepresentation G)
    (edgeId : Fin R.m) (vertexId : Fin R.n)
    (hinc : Inc G (R.decodeEdge edgeId) (R.decodeVertex vertexId)) :
    ∃ dart : Dart R.m, dart.1 = edgeId ∧ dart ∈ (R.bucket vertexId).toList := by
  have hend := R.endpoint_sound edgeId
  rw [link_inc_iff hend] at hinc
  rcases hinc with hleft | hright
  · refine ⟨(edgeId, false), rfl, (R.dart_mem_bucket_iff vertexId _).mpr ?_⟩
    simpa using hleft.symm
  · refine ⟨(edgeId, true), rfl, (R.dart_mem_bucket_iff vertexId _).mpr ?_⟩
    simpa using hright.symm

/-- At a fully scanned cursor, every incident actual edge is marked used. -/
theorem used_of_cursor_exhausted (R : CertifiedIncidenceRepresentation G)
    {dartFuel : Nat} {state : CoreState R.n R.m} (hInv : CursorInvariant R dartFuel state)
    (vertexId : Fin R.n)
    (hexhausted : state.cursorAt vertexId = (R.bucket vertexId).size)
    (edgeId : Fin R.m)
    (hinc : Inc G (R.decodeEdge edgeId) (R.decodeVertex vertexId)) :
    state.usedAt edgeId = true := by
  obtain ⟨dart, hdart, hmem⟩ := incident_has_bucket_dart R edgeId vertexId hinc
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨position, hposition, hget⟩ := hmem
  have hused := hInv.prefix_used vertexId position (by simpa using hposition) (by
    rw [hexhausted]
    simpa using hposition)
  have harray : (R.bucket vertexId)[position] = dart := by simpa using hget
  simpa [harray, hdart] using hused

/-- Preservation of the main invariant in the forward-growth branch. -/
theorem CoreInvariant.push (R : CertifiedIncidenceRepresentation G) (start : Fin R.n)
    {oldFuel newFuel : Nat} {state scanned : CoreState R.n R.m}
    {frame : Frame R.n R.m} {rest : List (Frame R.n R.m)}
    (hInv : CoreInvariant R start oldFuel state)
    (hstack : state.stack = frame :: rest)
    (dart : Dart R.m)
    (hscan : ScanCorrect R frame.vertex state (some dart, scanned, newFuel)) :
    let marked := scanned.setUsed dart.1 true
    let nextFrame : Frame R.n R.m :=
      { vertex := R.dartOther dart, incoming := some dart.1 }
    CoreInvariant R start newFuel { marked with stack := nextFrame :: marked.stack } := by
  dsimp
  obtain ⟨hdartVertex, hunused, hcursorInv⟩ := hscan.outcome
  change scanned.usedAt dart.1 = false at hunused
  change CursorInvariant R newFuel (scanned.setUsed dart.1 true) at hcursorInv
  have hsUsed : ∀ edgeId, scanned.usedAt edgeId = state.usedAt edgeId := hscan.used_eq
  have hsMono : ∀ vertexId, state.cursorAt vertexId ≤ scanned.cursorAt vertexId :=
    hscan.cursor_mono
  have hsStack : scanned.stack = state.stack := hscan.stack_eq
  have hsOutput : scanned.outputSteps = state.outputSteps := hscan.output_eq
  have hstateFalse : state.usedAt dart.1 = false := by
    rw [← hsUsed]
    exact hunused
  have hnotmem : dart.1 ∉ (chainSteps state).map Prod.fst := by
    intro hmem
    have htrue := (hInv.used_iff dart.1).mpr hmem
    rw [hstateFalse] at htrue
    contradiction
  have hlink : DenseLink R dart.1 frame.vertex (R.dartOther dart) := by
    simpa [DenseLink, hdartVertex] using R.dart_link dart
  constructor
  · rcases hcursorInv with ⟨hcursorLe, hremaining, hprefix⟩
    constructor
    · exact hcursorLe
    · exact hremaining
    · exact hprefix
  · right
    rcases hInv.shape with hempty | hshape
    · rw [hstack] at hempty
      contradiction
    · have hparentShape : StackShape R start (frame :: rest) := by simpa [hstack] using hshape
      have hpushed := StackShape.push hparentShape hlink
      simpa [CoreState.setUsed, hsStack, hstack] using hpushed
  · intro hempty
    simp at hempty
  · intro queried tail hnewStack
    simp only [List.cons.injEq] at hnewStack
    obtain ⟨rfl, rfl⟩ := hnewStack
    obtain ⟨source, hwalk⟩ := hInv.walk_nonempty frame rest hstack
    have hstep : DenseWalkSteps R frame.vertex [(dart.1, R.dartOther dart)]
        (R.dartOther dart) := .cons hlink (.nil _)
    refine ⟨source, ?_⟩
    have happ := hwalk.append hstep
    simpa [chainSteps, stackSteps, CoreState.setUsed, hsStack, hsOutput,
      List.append_assoc] using happ
  · intro edgeId
    change (scanned.setUsed dart.1 true).usedAt edgeId = true ↔
      edgeId ∈ (scanned.outputSteps ++
        (stackSteps scanned.stack ++ [(dart.1, R.dartOther dart)])).map Prod.fst
    by_cases hedge : edgeId = dart.1
    · subst edgeId
      simp
    · rw [CoreState.usedAt_setUsed]
      simp only [hedge, ↓reduceIte]
      rw [hsUsed, hInv.used_iff]
      simp [chainSteps, hsStack, hsOutput, hedge]
  · change
      ((scanned.outputSteps ++
        (stackSteps scanned.stack ++ [(dart.1, R.dartOther dart)])).map Prod.fst).Nodup
    rw [List.map_append, List.map_append]
    simp only [List.map_cons, List.map_nil, List.append_nil]
    rw [hsStack, hsOutput, ← List.append_assoc]
    rw [← List.map_append]
    change ((chainSteps state).map Prod.fst ++ [dart.1]).Nodup
    rw [List.nodup_append]
    refine ⟨hInv.edges_nodup, by simp, ?_⟩
    intro oldEdge hold queried hqueried
    simp only [List.mem_singleton] at hqueried
    subst queried
    intro heq
    subst oldEdge
    exact hnotmem hold
  · intro edgeId vertexId hmem
    change (edgeId, vertexId) ∈ scanned.outputSteps at hmem
    have holdMem : (edgeId, vertexId) ∈ state.outputSteps := by
      simpa [hsOutput] using hmem
    have hold := hInv.output_exhausted edgeId vertexId holdMem
    have hmono := hsMono vertexId
    have hle := hcursorInv.cursor_le vertexId
    simp only [CoreState.cursorAt_setUsed] at hle
    change scanned.cursorAt vertexId = (R.bucket vertexId).size
    omega
  · intro hempty
    simp at hempty

/-- Parity closes the live walk exactly when the current stack vertex is exhausted. -/
theorem CoreInvariant.closed_walk_of_scan_none
    (R : CertifiedIncidenceRepresentation G) (start : Fin R.n)
    {oldFuel newFuel : Nat} {state scanned : CoreState R.n R.m}
    {frame : Frame R.n R.m} {rest : List (Frame R.n R.m)}
    (hInv : CoreInvariant R start oldFuel state)
    (hstack : state.stack = frame :: rest)
    (hscan : ScanCorrect R frame.vertex state (none, scanned, newFuel))
    (heven : ∀ vertex : V(G), Even (degree G vertex)) :
    DenseWalkSteps R frame.vertex (chainSteps state) frame.vertex := by
  obtain ⟨hcursorInv, hexhausted⟩ := hscan.outcome
  change CursorInvariant R newFuel scanned at hcursorInv
  change scanned.cursorAt frame.vertex = (R.bucket frame.vertex).size at hexhausted
  obtain ⟨source, hwalk⟩ := hInv.walk_nonempty frame rest hstack
  have hcomplete : ∀ edgeId,
      Inc G (R.decodeEdge edgeId) (R.decodeVertex frame.vertex) →
        edgeId ∈ (chainSteps state).map Prod.fst := by
    intro edgeId hinc
    have husedScanned := used_of_cursor_exhausted R hcursorInv frame.vertex
      hexhausted edgeId hinc
    have husedState : state.usedAt edgeId = true := by
      rw [← hscan.used_eq]
      exact husedScanned
    exact (hInv.used_iff edgeId).mp husedState
  have hsource : source = frame.vertex :=
    walk_closes_at_even_exhausted R hwalk hInv.edges_nodup hcomplete
      (heven (R.decodeVertex frame.vertex))
  simpa [hsource] using hwalk

/-- Preservation of the main invariant when a non-root frame is backtracked and emitted. -/
theorem CoreInvariant.pop_some
    (R : CertifiedIncidenceRepresentation G) (start : Fin R.n)
    {oldFuel newFuel : Nat} {state scanned : CoreState R.n R.m}
    (vertexId : Fin R.n) (edgeId : Fin R.m) (rest : List (Frame R.n R.m))
    (hInv : CoreInvariant R start oldFuel state)
    (hstack : state.stack =
      ({ vertex := vertexId, incoming := some edgeId } : Frame R.n R.m) :: rest)
    (hscan : ScanCorrect R vertexId state (none, scanned, newFuel))
    (heven : ∀ vertex : V(G), Even (degree G vertex)) :
    CoreInvariant R start newFuel
      { scanned with
        stack := rest
        outputSteps := (edgeId, vertexId) :: scanned.outputSteps } := by
  obtain ⟨hcursorInv, hexhausted⟩ := hscan.outcome
  change CursorInvariant R newFuel scanned at hcursorInv
  change scanned.cursorAt vertexId = (R.bucket vertexId).size at hexhausted
  have hsUsed : ∀ queried, scanned.usedAt queried = state.usedAt queried := hscan.used_eq
  have hsMono : ∀ queried, state.cursorAt queried ≤ scanned.cursorAt queried :=
    hscan.cursor_mono
  have hsStack : scanned.stack = state.stack := hscan.stack_eq
  have hsOutput : scanned.outputSteps = state.outputSteps := hscan.output_eq
  have hshape : StackShape R start
      (({ vertex := vertexId, incoming := some edgeId } : Frame R.n R.m) :: rest) := by
    rcases hInv.shape with hempty | hshape
    · rw [hstack] at hempty
      contradiction
    · simpa [hstack] using hshape
  obtain ⟨parent, tail, rfl, htailShape, hparentLink⟩ := StackShape.of_cons_some hshape
  have hclosed := hInv.closed_walk_of_scan_none R start hstack hscan heven
  have hclosed' : DenseWalkSteps R vertexId
      ((state.outputSteps ++ stackSteps (parent :: tail)) ++ [(edgeId, vertexId)])
      vertexId := by
    simpa [chainSteps, hstack, stackSteps, List.append_assoc] using hclosed
  obtain ⟨_, middle, hprefix, hlast⟩ := DenseWalkSteps.snoc_iff.mp hclosed'
  have hmiddle : middle = parent.vertex :=
    DenseLink.left_eq_of_right hlast hparentLink
  subst middle
  have hfirst : DenseWalkSteps R parent.vertex [(edgeId, vertexId)] vertexId :=
    .cons hparentLink (.nil _)
  have hrotated : DenseWalkSteps R parent.vertex
      ((edgeId, vertexId) :: (state.outputSteps ++ stackSteps (parent :: tail)))
      parent.vertex := by
    simpa using hfirst.append hprefix
  constructor
  · rcases hcursorInv with ⟨hcursorLe, hremaining, hprefixUsed⟩
    exact ⟨hcursorLe, hremaining, hprefixUsed⟩
  · right
    exact htailShape
  · intro hempty
    exact (htailShape.nonempty hempty).elim
  · intro queried queriedTail hnewStack
    simp only [List.cons.injEq] at hnewStack
    obtain ⟨rfl, rfl⟩ := hnewStack
    refine ⟨parent.vertex, ?_⟩
    simpa [chainSteps, hsOutput] using hrotated
  · intro queried
    change scanned.usedAt queried = true ↔ queried ∈
      (((edgeId, vertexId) :: scanned.outputSteps) ++
        stackSteps (parent :: tail)).map Prod.fst
    rw [hsUsed, hInv.used_iff]
    simp only [chainSteps, hstack, stackSteps_cons_some, List.map_append,
      List.map_cons, List.map_nil, List.append_nil, hsOutput]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · let prefixIds := (state.outputSteps ++ stackSteps (parent :: tail)).map Prod.fst
    have hold : (prefixIds ++ [edgeId]).Nodup := by
      simpa [prefixIds, chainSteps, hstack, stackSteps, List.map_append,
        List.append_assoc] using hInv.edges_nodup
    have hrotatedNodup : ([edgeId] ++ prefixIds).Nodup :=
      (List.nodup_append_comm (l₁ := prefixIds) (l₂ := [edgeId])).mp hold
    simpa [prefixIds, chainSteps, hsOutput, List.map_append, List.append_assoc] using
      hrotatedNodup
  · intro queriedEdge queriedVertex hmem
    change (queriedEdge, queriedVertex) ∈
      (edgeId, vertexId) :: scanned.outputSteps at hmem
    change scanned.cursorAt queriedVertex = (R.bucket queriedVertex).size
    rcases List.mem_cons.mp hmem with hhead | hold
    · cases hhead
      exact hexhausted
    · have holdState : (queriedEdge, queriedVertex) ∈ state.outputSteps := by
        simpa [hsOutput] using hold
      have heq := hInv.output_exhausted queriedEdge queriedVertex holdState
      have hmono := hsMono queriedVertex
      have hle := hcursorInv.cursor_le queriedVertex
      omega
  · intro hempty
    exact (htailShape.nonempty hempty).elim

/-- Preservation of the main invariant when the exhausted root frame is removed. -/
theorem CoreInvariant.pop_none
    (R : CertifiedIncidenceRepresentation G) (start : Fin R.n)
    {oldFuel newFuel : Nat} {state scanned : CoreState R.n R.m}
    (vertexId : Fin R.n) (rest : List (Frame R.n R.m))
    (hInv : CoreInvariant R start oldFuel state)
    (hstack : state.stack =
      ({ vertex := vertexId, incoming := none } : Frame R.n R.m) :: rest)
    (hscan : ScanCorrect R vertexId state (none, scanned, newFuel))
    (heven : ∀ vertex : V(G), Even (degree G vertex)) :
    CoreInvariant R start newFuel { scanned with stack := rest } := by
  have hshape : StackShape R start
      (({ vertex := vertexId, incoming := none } : Frame R.n R.m) :: rest) := by
    rcases hInv.shape with hempty | hshape
    · rw [hstack] at hempty
      contradiction
    · simpa [hstack] using hshape
  obtain ⟨hvertex, hrest⟩ := StackShape.cons_none_eq_root hshape
  subst vertexId
  subst rest
  obtain ⟨hcursorInv, hexhausted⟩ := hscan.outcome
  change CursorInvariant R newFuel scanned at hcursorInv
  change scanned.cursorAt start = (R.bucket start).size at hexhausted
  have hsUsed : ∀ queried, scanned.usedAt queried = state.usedAt queried := hscan.used_eq
  have hsMono : ∀ queried, state.cursorAt queried ≤ scanned.cursorAt queried :=
    hscan.cursor_mono
  have hsOutput : scanned.outputSteps = state.outputSteps := hscan.output_eq
  have hclosed := hInv.closed_walk_of_scan_none R start hstack hscan heven
  have hclosedOutput : DenseWalkSteps R start state.outputSteps start := by
    simpa [chainSteps, hstack, stackSteps] using hclosed
  constructor
  · rcases hcursorInv with ⟨hcursorLe, hremaining, hprefixUsed⟩
    exact ⟨hcursorLe, hremaining, hprefixUsed⟩
  · left
    rfl
  · intro _
    simpa [hsOutput] using hclosedOutput
  · intro frame tail hnonempty
    simp at hnonempty
  · intro queried
    simp only [chainSteps, stackSteps, List.append_nil]
    change scanned.usedAt queried = true ↔ queried ∈ scanned.outputSteps.map Prod.fst
    rw [hsUsed, hInv.used_iff]
    simp [chainSteps, hstack, stackSteps, hsOutput]
  · simp only [chainSteps, stackSteps, List.append_nil]
    change (scanned.outputSteps.map Prod.fst).Nodup
    simpa [chainSteps, hstack, stackSteps, hsOutput] using hInv.edges_nodup
  · intro queriedEdge queriedVertex hmem
    change (queriedEdge, queriedVertex) ∈ scanned.outputSteps at hmem
    change scanned.cursorAt queriedVertex = (R.bucket queriedVertex).size
    have holdState : (queriedEdge, queriedVertex) ∈ state.outputSteps := by
      simpa [hsOutput] using hmem
    have heq := hInv.output_exhausted queriedEdge queriedVertex holdState
    have hmono := hsMono queriedVertex
    have hle := hcursorInv.cursor_le queriedVertex
    omega
  · intro _
    exact hexhausted

/-- Structural loop potential: two credits per edge not yet in the live sequence, plus one per
stack frame.  A push and either kind of pop consume exactly one credit. -/
def corePotential (R : CertifiedIncidenceRepresentation G) (state : CoreState R.n R.m) : Nat :=
  2 * (R.m - (chainSteps state).length) + state.stack.length

theorem CoreInvariant.chain_length_le (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) {dartFuel : Nat} {state : CoreState R.n R.m}
    (hInv : CoreInvariant R start dartFuel state) : (chainSteps state).length ≤ R.m := by
  have hcard := hInv.edges_nodup.length_le_card
  simpa using hcard

theorem corePotential_initialize (R : CertifiedIncidenceRepresentation G) (start : Fin R.n) :
    corePotential R (initializeState (m := R.m) start).ret = 2 * R.m + 1 := by
  simp [corePotential, chainSteps, stackSteps, initializeState]

theorem corePotential_push (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) {oldFuel newFuel : Nat}
    {state scanned : CoreState R.n R.m} {frame : Frame R.n R.m}
    {rest : List (Frame R.n R.m)}
    (hInv : CoreInvariant R start oldFuel state)
    (hstack : state.stack = frame :: rest) (dart : Dart R.m)
    (hscan : ScanCorrect R frame.vertex state (some dart, scanned, newFuel))
    (hnext : CoreInvariant R start newFuel
      { (scanned.setUsed dart.1 true) with
        stack := { vertex := R.dartOther dart, incoming := some dart.1 } ::
          (scanned.setUsed dart.1 true).stack }) :
    corePotential R
        { (scanned.setUsed dart.1 true) with
          stack := { vertex := R.dartOther dart, incoming := some dart.1 } ::
            (scanned.setUsed dart.1 true).stack } + 1 =
      corePotential R state := by
  have holdLe := hInv.chain_length_le R start
  have hnextLe := hnext.chain_length_le R start
  have hsStack : scanned.stack = state.stack := hscan.stack_eq
  have hsOutput : scanned.outputSteps = state.outputSteps := hscan.output_eq
  simp [corePotential, chainSteps, stackSteps, CoreState.setUsed, hsStack, hsOutput,
    List.length_append] at holdLe hnextLe ⊢
  omega

theorem corePotential_pop_some (R : CertifiedIncidenceRepresentation G)
    {newFuel : Nat} {state scanned : CoreState R.n R.m}
    (vertexId : Fin R.n) (edgeId : Fin R.m)
    (rest : List (Frame R.n R.m))
    (hstack : state.stack =
      ({ vertex := vertexId, incoming := some edgeId } : Frame R.n R.m) :: rest)
    (hscan : ScanCorrect R vertexId state (none, scanned, newFuel)) :
    corePotential R
        { scanned with
          stack := rest
          outputSteps := (edgeId, vertexId) :: scanned.outputSteps } + 1 =
      corePotential R state := by
  have hsStack : scanned.stack = state.stack := hscan.stack_eq
  have hsOutput : scanned.outputSteps = state.outputSteps := hscan.output_eq
  simp [corePotential, chainSteps, hstack, stackSteps, hsStack, hsOutput,
    List.length_append]
  omega

theorem corePotential_pop_none (R : CertifiedIncidenceRepresentation G)
    {newFuel : Nat} {state scanned : CoreState R.n R.m} (vertexId : Fin R.n)
    (rest : List (Frame R.n R.m))
    (hstack : state.stack =
      ({ vertex := vertexId, incoming := none } : Frame R.n R.m) :: rest)
    (hscan : ScanCorrect R vertexId state (none, scanned, newFuel))
    (hrest : rest = []) :
    corePotential R { scanned with stack := rest } + 1 = corePotential R state := by
  have hsStack : scanned.stack = state.stack := hscan.stack_eq
  have hsOutput : scanned.outputSteps = state.outputSteps := hscan.output_eq
  subst rest
  simp [corePotential, chainSteps, hstack, stackSteps, hsStack, hsOutput]

/-- The structural fuel bounds the semantic potential.  At zero potential the stack is empty, so
the loop cannot return through its fuel-zero guard with unfinished work. -/
theorem runLoop_correct (R : CertifiedIncidenceRepresentation G) (start : Fin R.n)
    (stepFuel dartFuel : Nat) (state : CoreState R.n R.m)
    (hInv : CoreInvariant R start dartFuel state)
    (hpotential : corePotential R state ≤ stepFuel)
    (heven : ∀ vertex : V(G), Even (degree G vertex)) :
    let result := runLoop R stepFuel dartFuel state
    result.ret.1.stack = [] ∧ CoreInvariant R start result.ret.2 result.ret.1 := by
  induction stepFuel generalizing dartFuel state with
  | zero =>
      have hzero : corePotential R state = 0 := by omega
      have hlength : state.stack.length = 0 := by
        simp only [corePotential] at hzero
        omega
      have hstack : state.stack = [] := List.length_eq_zero_iff.mp hlength
      simp [runLoop, hstack, hInv]
  | succ stepFuel ih =>
      rw [runLoop]
      cases hstack : state.stack with
      | nil =>
          simp [hstack]
          exact hInv
      | cons frame rest =>
          simp only [Event.ret_stackCheck, hstack, Event.ret_stackPeek]
          dsimp
          simp only [Event.ret_stackPeek]
          generalize hscanEq : nextIncident R frame.vertex dartFuel state = scan
          have hscanCorrect := nextIncident_correct R frame.vertex dartFuel state hInv.cursor
          rw [hscanEq] at hscanCorrect
          cases hoption : scan.ret.1 with
          | some dart =>
              have hspec : ScanCorrect R frame.vertex state
                  (some dart, scan.ret.2.1, scan.ret.2.2) := by
                have hret : scan.ret = (some dart, scan.ret.2) :=
                  Prod.ext hoption rfl
                rw [hret] at hscanCorrect
                exact hscanCorrect
              let nextState : CoreState R.n R.m :=
                { (scan.ret.2.1.setUsed dart.1 true) with
                  stack :=
                    { vertex := R.dartOther dart, incoming := some dart.1 } ::
                      (scan.ret.2.1.setUsed dart.1 true).stack }
              have hnext : CoreInvariant R start scan.ret.2.2 nextState := by
                simpa [nextState, CertifiedIncidenceRepresentation.dartOther] using
                  hInv.push R start hstack dart hspec
              have hdrop : corePotential R nextState + 1 = corePotential R state := by
                exact corePotential_push R start hInv hstack dart hspec hnext
              have hnextPotential : corePotential R nextState ≤ stepFuel := by omega
              have hrec := ih scan.ret.2.2 nextState hnext hnextPotential
              dsimp [nextState] at hrec ⊢
              simpa [hoption, CertifiedIncidenceRepresentation.dartOther] using hrec
          | none =>
              have hspec : ScanCorrect R frame.vertex state
                  (none, scan.ret.2.1, scan.ret.2.2) := by
                have hret : scan.ret = (none, scan.ret.2) :=
                  Prod.ext hoption rfl
                rw [hret] at hscanCorrect
                exact hscanCorrect
              cases hincoming : frame.incoming with
              | none =>
                  let nextState : CoreState R.n R.m :=
                    { scan.ret.2.1 with stack := rest }
                  have hstackNone : state.stack =
                      ({ vertex := frame.vertex, incoming := none } : Frame R.n R.m) :: rest := by
                    cases frame with
                    | mk frameVertex frameIncoming =>
                        simp only at hincoming
                        subst frameIncoming
                        exact hstack
                  have hnext : CoreInvariant R start scan.ret.2.2 nextState := by
                    simpa [nextState] using
                      hInv.pop_none R start frame.vertex rest hstackNone hspec heven
                  have hshape : StackShape R start
                      (({ vertex := frame.vertex, incoming := none } : Frame R.n R.m) :: rest) := by
                    rcases hInv.shape with hempty | hshape
                    · rw [hstack] at hempty
                      contradiction
                    · rw [hstackNone] at hshape
                      exact hshape
                  have hrest : rest = [] := (StackShape.cons_none_eq_root hshape).2
                  have hdrop : corePotential R nextState + 1 = corePotential R state := by
                    exact corePotential_pop_none R frame.vertex rest hstackNone hspec hrest
                  have hnextPotential : corePotential R nextState ≤ stepFuel := by omega
                  have hrec := ih scan.ret.2.2 nextState hnext hnextPotential
                  dsimp [nextState] at hrec ⊢
                  simpa [hoption, hincoming] using hrec
              | some edgeId =>
                  let nextState : CoreState R.n R.m :=
                    { scan.ret.2.1 with
                      stack := rest
                      outputSteps := (edgeId, frame.vertex) :: scan.ret.2.1.outputSteps }
                  have hstackSome : state.stack =
                      ({ vertex := frame.vertex, incoming := some edgeId } : Frame R.n R.m) :: rest := by
                    cases frame with
                    | mk frameVertex frameIncoming =>
                        simp only at hincoming
                        subst frameIncoming
                        exact hstack
                  have hnext : CoreInvariant R start scan.ret.2.2 nextState := by
                    simpa [nextState] using
                      hInv.pop_some R start frame.vertex edgeId rest hstackSome hspec heven
                  have hdrop : corePotential R nextState + 1 = corePotential R state := by
                    exact corePotential_pop_some R frame.vertex edgeId rest hstackSome hspec
                  have hnextPotential : corePotential R nextState ≤ stepFuel := by omega
                  have hrec := ih scan.ret.2.2 nextState hnext hnextPotential
                  dsimp [nextState] at hrec ⊢
                  simpa [hoption, hincoming] using hrec

theorem DenseWalkSteps.property_of_incident_mem
    (R : CertifiedIncidenceRepresentation G) (P : Fin R.n → Prop)
    {source target : Fin R.n} {steps : List (Fin R.m × Fin R.n)}
    (hwalk : DenseWalkSteps R source steps target)
    (hsource : P source)
    (hdest : ∀ edgeId vertexId, (edgeId, vertexId) ∈ steps → P vertexId)
    {queriedEdge : Fin R.m} {queriedVertex : Fin R.n}
    (hmem : queriedEdge ∈ steps.map Prod.fst)
    (hinc : Inc G (R.decodeEdge queriedEdge) (R.decodeVertex queriedVertex)) :
    P queriedVertex := by
  induction hwalk generalizing queriedEdge queriedVertex with
  | nil => simp at hmem
  | @cons source middle target edgeId rest link tail ih =>
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with hedge | htailMem
      · subst queriedEdge
        rcases (link_inc_iff link).mp hinc with hqueried | hqueried
        · simpa [hqueried] using hsource
        · simpa [hqueried] using hdest edgeId middle (by simp)
      · have hmiddle : P middle := hdest edgeId middle (by simp)
        apply ih hmiddle
        · intro tailEdge tailVertex htail
          exact hdest tailEdge tailVertex (by simp [htail])
        · exact htailMem
        · exact hinc

/-- Reachability from the start propagates cursor exhaustion in a completed run. -/
theorem CoreInvariant.reachable_exhausted
    (R : CertifiedIncidenceRepresentation G) (start : Fin R.n)
    {dartFuel : Nat} {state : CoreState R.n R.m}
    (hInv : CoreInvariant R start dartFuel state) (hempty : state.stack = [])
    {vertexId : Fin R.n}
    (hreach : Reachable G (R.decodeVertex start) (R.decodeVertex vertexId)) :
    state.cursorAt vertexId = (R.bucket vertexId).size := by
  have hwalk := hInv.walk_empty hempty
  have hstart := hInv.start_exhausted_if_empty hempty
  change Relation.ReflTransGen (Step G) (R.decodeVertex start)
      (R.decodeVertex vertexId) at hreach
  have hprop : ∀ target : Vertex G,
      Relation.ReflTransGen (Step G) (R.decodeVertex start) target →
      state.cursorAt (R.encodeVertex target) =
        (R.bucket (R.encodeVertex target)).size := by
    intro target htarget
    induction htarget with
    | refl =>
        simpa [CertifiedIncidenceRepresentation.encodeVertex] using hstart
    | @tail middle target hreach hstep ih =>
        obtain ⟨edge, hlink⟩ := hstep
        let middleId := R.encodeVertex middle
        let targetId := R.encodeVertex target
        let edgeId := R.decodeEdge.symm edge
        have hmiddleDecode : R.decodeVertex middleId = middle := by
          simp [middleId, CertifiedIncidenceRepresentation.encodeVertex]
        have htargetDecode : R.decodeVertex targetId = target := by
          simp [targetId, CertifiedIncidenceRepresentation.encodeVertex]
        have hedgeDecode : R.decodeEdge edgeId = edge := by simp [edgeId]
        have hmiddleExhausted :
            state.cursorAt middleId = (R.bucket middleId).size := by
          simpa [middleId] using ih
        have hdenseLink : DenseLink R edgeId middleId targetId := by
          simpa [DenseLink, hmiddleDecode, htargetDecode, hedgeDecode] using hlink
        have hused : state.usedAt edgeId = true :=
          used_of_cursor_exhausted R hInv.cursor middleId hmiddleExhausted edgeId
            ⟨R.decodeVertex targetId, hdenseLink⟩
        have hmem : edgeId ∈ state.outputSteps.map Prod.fst := by
          have := (hInv.used_iff edgeId).mp hused
          simpa [chainSteps, hempty, stackSteps] using this
        have htargetExhausted :
            state.cursorAt targetId = (R.bucket targetId).size := by
          apply hwalk.property_of_incident_mem R
            (fun queried => state.cursorAt queried = (R.bucket queried).size)
            hstart hInv.output_exhausted hmem
          exact ⟨R.decodeVertex middleId, hdenseLink.symm⟩
        simpa [targetId] using htargetExhausted
  have := hprop (R.decodeVertex vertexId) hreach
  simpa [CertifiedIncidenceRepresentation.encodeVertex] using this

/-- Every dense actual-edge ID occurs after a completed run, using only the frozen connectivity
hypothesis for non-isolated vertices. -/
theorem CoreInvariant.edges_complete
    (R : CertifiedIncidenceRepresentation G) (start : Fin R.n)
    {dartFuel : Nat} {state : CoreState R.n R.m}
    (hInv : CoreInvariant R start dartFuel state) (hempty : state.stack = [])
    (hconn : ∀ vertex : V(G), (∃ edge : ActualEdge G, Inc G edge vertex) →
      Reachable G (R.decodeVertex start) vertex) :
    ∀ edgeId : Fin R.m, edgeId ∈ state.outputSteps.map Prod.fst := by
  intro edgeId
  let endpointId := (R.ends edgeId).1
  have hlink := R.endpoint_sound edgeId
  have hinc : Inc G (R.decodeEdge edgeId) (R.decodeVertex endpointId) :=
    ⟨R.decodeVertex (R.ends edgeId).2, hlink⟩
  have hreach := hconn (R.decodeVertex endpointId) ⟨R.decodeEdge edgeId, hinc⟩
  have hexhausted := hInv.reachable_exhausted R start hempty hreach
  have hused := used_of_cursor_exhausted R hInv.cursor endpointId hexhausted edgeId hinc
  have hmem := (hInv.used_iff edgeId).mp hused
  simpa [chainSteps, hempty, stackSteps] using hmem

theorem DenseWalkSteps.vertices_getLast {R : CertifiedIncidenceRepresentation G}
    {source target : Fin R.n} {steps : List (Fin R.m × Fin R.n)}
    (hwalk : DenseWalkSteps R source steps target) :
    (source :: steps.map Prod.snd).getLast? = some target := by
  induction hwalk with
  | nil => simp
  | cons link tail ih =>
      simp only [List.map_cons]
      simpa using ih

theorem DenseWalkSteps.decoded_links {R : CertifiedIncidenceRepresentation G}
    {source target : Fin R.n} {steps : List (Fin R.m × Fin R.n)}
    (hwalk : DenseWalkSteps R source steps target) :
    List.Forall₂
      (fun edge endpoints => Link G edge endpoints.1 endpoints.2)
      (steps.map (fun step => R.decodeEdge step.1))
      ((R.decodeVertex source :: steps.map (fun step => R.decodeVertex step.2)).zip
        (R.decodeVertex source :: steps.map (fun step => R.decodeVertex step.2)).tail) := by
  induction hwalk with
  | nil => simp
  | cons link tail ih =>
      simp only [List.map_cons, List.tail_cons, List.zip_cons_cons]
      exact .cons link ih

/-- The exact six-clause frozen correctness theorem. -/
theorem hierholzer_correct
    (R : CertifiedIncidenceRepresentation G) (s : Vertex G)
    (heven : ∀ vertex : Vertex G, Even (degree G vertex))
    (hconn : ∀ vertex : Vertex G, (∃ edge : ActualEdge G, Inc G edge vertex) →
      Reachable G s vertex) :
    ValidEulerTour (Link G) s
      ((hierholzer R (R.encodeVertex s)).ret.decode R.decodeVertex R.decodeEdge) := by
  let start := R.encodeVertex s
  let initial := (initializeState (m := R.m) start).ret
  let loopResult := runLoop R (R.m + R.m + 1) (R.m + R.m) initial
  have hinitial : CoreInvariant R start (R.m + R.m) initial := by
    simpa [initial] using coreInvariant_initialize R start
  have hpotential : corePotential R initial ≤ R.m + R.m + 1 := by
    rw [show corePotential R initial = 2 * R.m + 1 by
      simpa [initial] using corePotential_initialize R start]
    omega
  have hrun : loopResult.ret.1.stack = [] ∧
      CoreInvariant R start loopResult.ret.2 loopResult.ret.1 := by
    simpa [loopResult] using
      runLoop_correct R start (R.m + R.m + 1) (R.m + R.m) initial
        hinitial hpotential heven
  let indexed : IndexedTour R.n R.m :=
    { start := start, steps := loopResult.ret.1.outputSteps }
  have hhierholzer : (hierholzer R start).ret = indexed := by
    simp [hierholzer, indexed, loopResult, initial]
  have hstartDecode : R.decodeVertex start = s := by
    simp [start, CertifiedIncidenceRepresentation.encodeVertex]
  have hwalk : DenseWalkSteps R start loopResult.ret.1.outputSteps start :=
    hrun.2.walk_empty hrun.1
  have hnodup : (loopResult.ret.1.outputSteps.map Prod.fst).Nodup := by
    simpa [chainSteps, hrun.1, stackSteps] using hrun.2.edges_nodup
  have hconn' : ∀ vertex : Vertex G,
      (∃ edge : ActualEdge G, Inc G edge vertex) →
        Reachable G (R.decodeVertex start) vertex := by
    intro vertex hincident
    simpa [hstartDecode] using hconn vertex hincident
  have hcomplete : ∀ edgeId : Fin R.m,
      edgeId ∈ loopResult.ret.1.outputSteps.map Prod.fst :=
    hrun.2.edges_complete R start hrun.1 hconn'
  rw [show R.encodeVertex s = start by rfl, hhierholzer]
  constructor
  · simp [indexed, IndexedTour.decode]
  · simp [indexed, IndexedTour.decode, hstartDecode]
  · rw [← hstartDecode]
    change
      (R.decodeVertex start ::
        loopResult.ret.1.outputSteps.map (fun step => R.decodeVertex step.2)).getLast? =
          some (R.decodeVertex start)
    rw [show
      R.decodeVertex start ::
          loopResult.ret.1.outputSteps.map (fun step => R.decodeVertex step.2) =
        (start :: loopResult.ret.1.outputSteps.map Prod.snd).map R.decodeVertex by simp]
    rw [List.getLast?_map, DenseWalkSteps.vertices_getLast hwalk]
    rfl
  · simpa [indexed, IndexedTour.decode] using hwalk.decoded_links
  · rw [IndexedTour.decode_edges_nodup_iff]
    exact hnodup
  · rw [IndexedTour.decode_edges_complete_iff]
    exact hcomplete

private theorem length_eq_fin_card {m : Nat} (ids : List (Fin m))
    (hnodup : ids.Nodup) (hcomplete : ∀ edgeId : Fin m, edgeId ∈ ids) :
    ids.length = m := by
  classical
  have hset : ids.toFinset = Finset.univ := by
    ext edgeId
    simp [hcomplete edgeId]
  calc
    ids.length = ids.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = Finset.univ.card := by rw [hset]
    _ = m := by simp

@[simp] theorem hierholzer_ret_start (R : CertifiedIncidenceRepresentation G)
    (start : Fin R.n) : (hierholzer R start).ret.start = start := by
  simp [hierholzer]

/-- Mandatory edgeless corollary; it is structural and needs no Eulerian hypotheses. -/
theorem hierholzer_edgeless
    (R : CertifiedIncidenceRepresentation G) (s : Vertex G)
    (hedgeless : edgeCount G = 0) :
    let decoded :=
      (hierholzer R (R.encodeVertex s)).ret.decode R.decodeVertex R.decodeEdge
    decoded.edges = [] ∧ decoded.vertices = [s] := by
  dsimp
  have hm : R.m = 0 := by rw [R.m_eq, hedgeless]
  have hsteps : (hierholzer R (R.encodeVertex s)).ret.steps = [] := by
    cases hlist : (hierholzer R (R.encodeVertex s)).ret.steps with
    | nil => rfl
    | cons step rest =>
        have hlt := step.1.isLt
        omega
  constructor
  · simpa [IndexedTour.decode] using hsteps
  · rw [hsteps]
    simp [CertifiedIncidenceRepresentation.encodeVertex]

/-- Mandatory exact-length corollary, stated in the official mathematical edge count. -/
theorem hierholzer_exact_length
    (R : CertifiedIncidenceRepresentation G) (s : Vertex G)
    (heven : ∀ vertex : Vertex G, Even (degree G vertex))
    (hconn : ∀ vertex : Vertex G, (∃ edge : ActualEdge G, Inc G edge vertex) →
      Reachable G s vertex) :
    let decoded :=
      (hierholzer R (R.encodeVertex s)).ret.decode R.decodeVertex R.decodeEdge
    decoded.edges.length = edgeCount G ∧
      decoded.vertices.length = edgeCount G + 1 := by
  let indexed := (hierholzer R (R.encodeVertex s)).ret
  have hvalid := hierholzer_correct R s heven hconn
  have hnodup : (indexed.steps.map Prod.fst).Nodup := by
    exact (IndexedTour.decode_edges_nodup_iff indexed R.decodeVertex R.decodeEdge).mp
      hvalid.edges_nodup
  have hcomplete : ∀ edgeId : Fin R.m, edgeId ∈ indexed.steps.map Prod.fst := by
    exact (IndexedTour.decode_edges_complete_iff indexed R.decodeVertex R.decodeEdge).mp
      hvalid.edges_complete
  have hlength : indexed.steps.length = R.m := by
    have := length_eq_fin_card (indexed.steps.map Prod.fst) hnodup hcomplete
    simpa using this
  dsimp
  constructor
  · simpa [indexed, IndexedTour.decode, hlength] using R.m_eq
  · simp [indexed, IndexedTour.decode, hlength, R.m_eq]

/-- The common positive-length closed-trail/every-edge-once formulation. -/
def PositiveEdgeCircuit {V E : Type*} (Link : E → V → V → Prop) (start : V)
    (tour : TourData V E) : Prop :=
  ValidEulerTour Link start tour ∧ 0 < tour.edges.length

/-- Mandatory positive-edge circuit corollary. -/
theorem hierholzer_positive_edge_circuit
    (R : CertifiedIncidenceRepresentation G) (s : Vertex G)
    (heven : ∀ vertex : Vertex G, Even (degree G vertex))
    (hconn : ∀ vertex : Vertex G, (∃ edge : ActualEdge G, Inc G edge vertex) →
      Reachable G s vertex)
    (hpositive : 0 < edgeCount G) :
    PositiveEdgeCircuit (Link G) s
      ((hierholzer R (R.encodeVertex s)).ret.decode R.decodeVertex R.decodeEdge) := by
  refine ⟨hierholzer_correct R s heven hconn, ?_⟩
  have hlength := (hierholzer_exact_length R s heven hconn).1
  omega

end Benchmarks.Hierholzer.GraphLib
