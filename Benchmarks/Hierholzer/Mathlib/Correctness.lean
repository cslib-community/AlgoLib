module

public import Benchmarks.Hierholzer.Mathlib.Resource
public import Benchmarks.Hierholzer.Mathlib.Trail
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic

/-!
# Functional correctness of the array-backed Hierholzer core

The proof follows the executable loop.  Its central invariant records a dense trail along the
stack, the already emitted suffix, exact correspondence between used flags and those two edge
lists, cursor-prefix exhaustion, and the two fuel equations.  The only graph-theoretic step in a
pop is the usual even-degree argument: an exhausted stack top must be the current splice anchor.
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open Set
open scoped Graph
open Benchmarks.Hierholzer.Common
open Cslib.Algorithms.Lean

universe u v

variable {α : Type u} {ε : Type v} {G : Graph α ε}

namespace CertifiedIncidenceRepresentation

variable (R : CertifiedIncidenceRepresentation G)

/-- Stack frames read from bottom to top as canonical indexed steps. -/
def frameSteps : List (Frame R.n R.m) → List (Fin R.m × Fin R.n)
  | [] => []
  | frame :: rest =>
      frameSteps rest ++ frame.incoming.toList.map (fun edge => (edge, frame.vertex))

@[simp] theorem frameSteps_nil : R.frameSteps [] = [] := rfl

@[simp] theorem frameSteps_bottom (x : Fin R.n) :
    R.frameSteps [({ incoming := none, vertex := x } : Frame R.n R.m)] = [] := by
  simp [frameSteps]

@[simp] theorem frameSteps_push (stack : List (Frame R.n R.m)) (e : Fin R.m)
    (x : Fin R.n) :
    R.frameSteps ({ incoming := some e, vertex := x } :: stack) =
      R.frameSteps stack ++ [(e, x)] := by
  simp [frameSteps]

/-- The stack is precisely a dense path grown from the supplied start. -/
inductive StackPath (start : Fin R.n) : List (Frame R.n R.m) → Fin R.n → Prop where
  | bottom : StackPath start [({ incoming := none, vertex := start } : Frame R.n R.m)] start
  | push {stack : List (Frame R.n R.m)} {x y : Fin R.n} {e : Fin R.m} :
      StackPath start stack x → R.DenseLink e x y →
        StackPath start ({ incoming := some e, vertex := y } :: stack) y

theorem StackPath.ne_nil {start current : Fin R.n} {stack : List (Frame R.n R.m)}
    (h : R.StackPath start stack current) : stack ≠ [] := by
  cases h <;> simp

theorem StackPath.head_vertex {start current : Fin R.n} {top : Frame R.n R.m}
    {rest : List (Frame R.n R.m)}
    (h : R.StackPath start (top :: rest) current) : top.vertex = current := by
  cases h with
  | bottom => rfl
  | push => rfl

theorem StackPath.current_unique {start x y : Fin R.n}
    {stack : List (Frame R.n R.m)}
    (hx : R.StackPath start stack x) (hy : R.StackPath start stack y) : x = y := by
  cases stack with
  | nil => exact ((StackPath.ne_nil R hx) rfl).elim
  | cons top rest =>
      exact (hx.head_vertex (R := R)).symm.trans (hy.head_vertex (R := R))

theorem StackPath.trail {start current : Fin R.n} {stack : List (Frame R.n R.m)}
    (h : R.StackPath start stack current) : R.DenseTrail start (R.frameSteps stack) current := by
  induction h with
  | bottom => exact .nil start
  | @push stack x y e _ hlink ih =>
      simpa using ih.snoc hlink

theorem StackPath.pop {start current : Fin R.n} {e : Fin R.m}
    {rest : List (Frame R.n R.m)}
    (h : R.StackPath start ({ incoming := some e, vertex := current } :: rest) current) :
    ∃ previous, R.StackPath start rest previous ∧ R.DenseLink e previous current := by
  cases h with
  | push hpath hlink => exact ⟨_, hpath, hlink⟩

theorem StackPath.none_bottom {start current : Fin R.n}
    {rest : List (Frame R.n R.m)}
    (h : R.StackPath start ({ incoming := none, vertex := current } :: rest) current) :
    current = start ∧ rest = [] := by
  cases h with
  | bottom => exact ⟨rfl, rfl⟩

/-- Every previously scanned dart has its actual edge marked used. -/
def CursorPrefixUsed (state : CoreState R.n R.m) : Prop :=
  (∀ x : Fin R.n, state.cursor.get x ≤ (R.buckets.get x).size) ∧
  ∀ (x : Fin R.n) (i : Nat), i < state.cursor.get x →
    ∀ dart, (R.buckets.get x)[i]? = some dart → state.used.get dart.edge = true

/-- Every edge incident to a vertex is currently marked used. -/
def Exhausted (used : Vector Bool R.m) (x : Fin R.n) : Prop :=
  ∀ e : Fin R.m, R.DenseInc e x → used.get e = true

def combinedSteps (state : CoreState R.n R.m) : List (Fin R.m × Fin R.n) :=
  R.frameSteps state.stack ++ state.output

/-- The semantic and progress invariant threaded through the two-fuel loop. -/
structure RunInvariant (start : Fin R.n) (scanFuel popFuel : Nat)
    (state : CoreState R.n R.m) : Prop where
  cursorPrefixUsed : R.CursorPrefixUsed state
  stackShape : state.stack = [] ∨ ∃ current, R.StackPath start state.stack current
  splice : ∀ {current}, R.StackPath start state.stack current →
    ∃ anchor pre active,
      R.frameSteps state.stack = pre ++ active ∧
      R.DenseTrail start pre anchor ∧
      R.DenseTrail anchor active current ∧
      R.DenseTrail anchor state.output start
  edgesNodup : ((R.combinedSteps state).map Prod.fst).Nodup
  used_iff : ∀ e : Fin R.m,
    state.used.get e = true ↔ e ∈ (R.combinedSteps state).map Prod.fst
  outputExhausted : ∀ step ∈ state.output, R.Exhausted state.used step.2
  emptyExhausted : state.stack = [] → R.Exhausted state.used start
  emptyTrail : state.stack = [] → R.DenseTrail start state.output start
  scanBalance : scanFuel + ∑ x : Fin R.n, state.cursor.get x = R.incidenceCount
  popBalance : state.stack ≠ [] → popFuel + state.output.length = R.m + 1

theorem denseLink_otherEndpoint {x : Fin R.n} {d : Dart R.m}
    (hmem : d ∈ (R.buckets.get x).toList) :
    R.DenseLink d.edge x
      (Core.otherEndpoint d.role (R.ends.get d.edge).1 (R.ends.get d.edge).2) := by
  rw [R.mem_bucket_iff] at hmem
  rcases d with ⟨edge, role⟩
  cases role with
  | false =>
      simp only [Dart.vertex_role0] at hmem
      exact Or.inl ⟨hmem.symm, rfl⟩
  | true =>
      simp only [Dart.vertex_role1] at hmem
      exact Or.inr ⟨hmem.symm, rfl⟩

theorem denseInc_has_dart {x : Fin R.n} {e : Fin R.m} (h : R.DenseInc e x) :
    ∃ d : Dart R.m, d.edge = e ∧ d ∈ (R.buckets.get x).toList := by
  rcases h with h | h
  · exact ⟨⟨e, false⟩, rfl, (R.role0_mem_iff x e).2 h⟩
  · exact ⟨⟨e, true⟩, rfl, (R.role1_mem_iff x e).2 h⟩

theorem CursorPrefixUsed.exhausted_of_eq {state : CoreState R.n R.m} {x : Fin R.n}
    (h : R.CursorPrefixUsed state)
    (hcursor : state.cursor.get x = (R.buckets.get x).size) :
    R.Exhausted state.used x := by
  intro e hinc
  obtain ⟨d, rfl, hd⟩ := R.denseInc_has_dart hinc
  have hd' : d ∈ R.buckets.get x := by simpa using hd
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hd'
  apply h.2 x i
  · simpa [hcursor] using hi
  · rw [Array.getElem?_eq_getElem hi, hget]

theorem used_set_true_get (used : Vector Bool R.m) (e f : Fin R.m) :
    (Core.setFin used e true).get f = true ↔ used.get f = true ∨ f = e := by
  by_cases hfe : f = e
  · subst f
    change (Core.setFin used e true)[e.1] = true ↔ _
    simp [Core.setFin]
  ·
    have hval : f.1 ≠ e.1 := by
      intro h
      exact hfe (Fin.ext h)
    change (Core.setFin used e true)[f.1] = true ↔ used[f.1] = true ∨ f = e
    have hget : (Core.setFin used e true)[f.1] = used[f.1] := by
      exact Vector.getElem_set_ne e.2 f.2 (Ne.symm hval)
    rw [hget]
    simp [hfe]

theorem Exhausted.mono_set {used : Vector Bool R.m} {x : Fin R.n} {e : Fin R.m}
    (h : R.Exhausted used x) : R.Exhausted (Core.setFin used e true) x := by
  intro f hf
  rw [R.used_set_true_get]
  exact Or.inl (h f hf)

/-- Pointwise characterization of the dense vector update used by the core. -/
theorem setFin_get {A : Type*} (values : Vector A R.n) (i j : Fin R.n) (value : A) :
    (Core.setFin values i value).get j = if i = j then value else values.get j := by
  unfold Core.setFin
  change (values.set i.1 value i.2)[j.1] = _
  rw [Vector.getElem_set]
  by_cases hij : i = j
  · subst j
    simp
  ·
    have hval : i.1 ≠ j.1 := by
      intro h
      exact hij (Fin.ext h)
    simp only [if_neg hval, if_neg hij]
    rfl

def UsedExtends (old new : Vector Bool R.m) : Prop :=
  ∀ e : Fin R.m, old.get e = true → new.get e = true

theorem usedExtends_refl (used : Vector Bool R.m) : R.UsedExtends used used :=
  fun _ h ↦ h

theorem usedExtends_set_true (used : Vector Bool R.m) (e : Fin R.m) :
    R.UsedExtends used (Core.setFin used e true) := by
  intro f hf
  exact (R.used_set_true_get used e f).2 (Or.inl hf)

theorem Exhausted.mono {old new : Vector Bool R.m} {x : Fin R.n}
    (hext : R.UsedExtends old new) (h : R.Exhausted old x) : R.Exhausted new x := by
  intro e he
  exact hext e (h e he)

theorem CursorPrefixUsed.advance {state : CoreState R.n R.m} (h : R.CursorPrefixUsed state)
    (x : Fin R.n) (dart : Dart R.m)
    (hget : (R.buckets.get x)[state.cursor.get x]? = some dart)
    (newUsed : Vector Bool R.m) (hext : R.UsedExtends state.used newUsed)
    (hmarked : newUsed.get dart.edge = true) :
    R.CursorPrefixUsed
      { state with
        used := newUsed
        cursor := Core.setFin state.cursor x (state.cursor.get x + 1) } := by
  obtain ⟨hindex, hget'⟩ := Array.getElem?_eq_some_iff.mp hget
  constructor
  · intro y
    rw [R.setFin_get]
    by_cases hxy : x = y
    · subst y
      simp
      omega
    · rw [if_neg hxy]
      exact h.1 y
  · intro y i hi d hd
    rw [R.setFin_get] at hi
    split at hi
    · rename_i hxy
      subst y
      by_cases hic : i < state.cursor.get x
      · exact hext d.edge (h.2 x i hic d hd)
      · have hieq : i = state.cursor.get x := by omega
        subst i
        rw [hget] at hd
        injection hd with hdd
        subst d
        exact hmarked
    · exact hext d.edge (h.2 y i hi d hd)

theorem sum_cursor_set_succ (cursor : Vector Nat R.n) (x : Fin R.n) :
    (∑ y : Fin R.n, (Core.setFin cursor x (cursor.get x + 1)).get y) =
      (∑ y : Fin R.n, cursor.get y) + 1 := by
  classical
  have hfun : (fun y : Fin R.n ↦ (Core.setFin cursor x (cursor.get x + 1)).get y) =
      Function.update (fun y : Fin R.n ↦ cursor.get y) x (cursor.get x + 1) := by
    funext y
    rw [R.setFin_get]
    by_cases hxy : x = y
    · subst y
      simp
    · simp [Function.update, hxy, Ne.symm hxy]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ x)]
  have hold := Finset.sum_erase_add (Finset.univ : Finset (Fin R.n))
    (fun y : Fin R.n ↦ cursor.get y) (Finset.mem_univ x)
  rw [← hold]
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

@[simp] theorem vector_replicate_get {A : Type*} (n : Nat) (value : A) (i : Fin n) :
    (Vector.replicate n value).get i = value := by
  change (Vector.replicate n value)[i.1] = value
  exact Vector.getElem_replicate i.2

theorem RunInvariant.initial (start : Fin R.n) :
    R.RunInvariant start R.incidenceCount (R.m + 1)
      (Core.initState R.n R.m start).ret := by
  rw [Core.initState_ret]
  constructor
  · constructor
    · intro x
      simp
    · intro x i hi
      simp at hi
  · exact Or.inr ⟨start, .bottom⟩
  · intro current hpath
    have hcurrent : current = start := by
      cases hpath
      rfl
    subst current
    exact ⟨start, [], [], by simp, .nil start, .nil start, .nil start⟩
  · simp [combinedSteps]
  · intro e
    simp [combinedSteps]
  · simp
  · simp
  · simp
  · simp [incidenceCount]
  · simp

theorem nodup_insert_middle {A : Type*} [DecidableEq A] {left right : List A} {a : A}
    (hn : (left ++ right).Nodup) (ha : a ∉ left ++ right) :
    (left ++ a :: right).Nodup := by
  rw [List.nodup_append] at hn ⊢
  rcases hn with ⟨hleft, hright, hcross⟩
  constructor
  · exact hleft
  constructor
  · rw [List.nodup_cons]
    exact ⟨fun haright ↦ ha (by simp [haright]), hright⟩
  · intro x hx y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · intro hxa
      apply ha
      exact List.mem_append_left _ (hxa ▸ hx)
    · exact hcross x hx y hy

theorem RunInvariant.skip {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start (scanFuel + 1) popFuel state)
    (x : Fin R.n) (dart : Dart R.m)
    (hget : (R.buckets.get x)[state.cursor.get x]? = some dart)
    (hmarked : state.used.get dart.edge = true) :
    R.RunInvariant start scanFuel popFuel
      (Core.skipState state
        (Core.setFin state.cursor x (state.cursor.get x + 1))) := by
  let nextState := Core.skipState state
    (Core.setFin state.cursor x (state.cursor.get x + 1))
  have hcursor : R.CursorPrefixUsed nextState := by
    simpa [nextState, Core.skipState] using
      h.cursorPrefixUsed.advance (R := R) x dart hget state.used
        (R.usedExtends_refl state.used) hmarked
  constructor
  · exact hcursor
  · simpa [nextState, Core.skipState] using h.stackShape
  · intro current hpath
    exact h.splice (by simpa [nextState, Core.skipState] using hpath)
  · simpa [nextState, Core.skipState, combinedSteps] using h.edgesNodup
  · intro e
    simpa [nextState, Core.skipState, combinedSteps] using h.used_iff e
  · intro step hs
    exact h.outputExhausted step (by simpa [nextState, Core.skipState] using hs)
  · intro hempty
    exact h.emptyExhausted (by simpa [nextState, Core.skipState] using hempty)
  · intro hempty
    exact h.emptyTrail (by simpa [nextState, Core.skipState] using hempty)
  · have hsum := R.sum_cursor_set_succ state.cursor x
    have hbalance := h.scanBalance
    simpa [nextState, Core.skipState] using (show
      scanFuel + ∑ y : Fin R.n,
          (Core.setFin state.cursor x (state.cursor.get x + 1)).get y =
        R.incidenceCount by omega)
  · intro hne
    exact h.popBalance (by simpa [nextState, Core.skipState] using hne)

theorem RunInvariant.push {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start (scanFuel + 1) popFuel state)
    {current next : Fin R.n} {edge : Fin R.m} {dart : Dart R.m}
    (hpath : R.StackPath start state.stack current)
    (hget : (R.buckets.get current)[state.cursor.get current]? = some dart)
    (hedge : dart.edge = edge)
    (hlink : R.DenseLink edge current next)
    (hunused : state.used.get edge = false) :
    R.RunInvariant start scanFuel popFuel
      (Core.pushState state (Core.setFin state.used edge true)
        (Core.setFin state.cursor current (state.cursor.get current + 1))
        ({ incoming := some edge, vertex := next } :: state.stack)) := by
  let nextState := Core.pushState state (Core.setFin state.used edge true)
    (Core.setFin state.cursor current (state.cursor.get current + 1))
    ({ incoming := some edge, vertex := next } :: state.stack)
  have hmarked : (Core.setFin state.used edge true).get dart.edge = true := by
    subst edge
    exact (R.used_set_true_get state.used dart.edge dart.edge).2 (Or.inr rfl)
  have hcursor : R.CursorPrefixUsed nextState := by
    simpa [nextState, Core.pushState] using
      h.cursorPrefixUsed.advance (R := R) current dart hget
        (Core.setFin state.used edge true) (R.usedExtends_set_true state.used edge) hmarked
  have hnextPath : R.StackPath start nextState.stack next := by
    simpa [nextState, Core.pushState] using StackPath.push hpath hlink
  constructor
  · exact hcursor
  · exact Or.inr ⟨next, hnextPath⟩
  · intro current' hpath'
    have hcurrent : current' = next := by
      have hv := hpath'.head_vertex (R := R)
      simp only [nextState, Core.pushState] at hv
      exact hv.symm
    subst current'
    obtain ⟨anchor, pre, active, hsteps, hpre, hactive, hout⟩ := h.splice hpath
    refine ⟨anchor, pre, active ++ [(edge, next)], ?_, hpre, hactive.snoc hlink, hout⟩
    simp [nextState, Core.pushState, frameSteps, hsteps, List.append_assoc]
  ·
    have hedge_not_mem : edge ∉ (R.combinedSteps state).map Prod.fst := by
      intro he
      have := (h.used_iff edge).2 he
      simp [hunused] at this
    have hn := nodup_insert_middle
      (left := (R.frameSteps state.stack).map Prod.fst)
      (right := state.output.map Prod.fst) (a := edge)
      (by simpa [combinedSteps, List.map_append] using h.edgesNodup)
      (by simpa [combinedSteps, List.map_append] using hedge_not_mem)
    simpa [nextState, Core.pushState, combinedSteps, frameSteps, List.map_append,
      List.append_assoc] using hn
  · intro e
    rw [show nextState.used = Core.setFin state.used edge true by rfl,
      R.used_set_true_get, h.used_iff]
    simp only [nextState, Core.pushState, combinedSteps, frameSteps_push,
      List.map_append, List.map_singleton, List.mem_append, List.mem_cons,
      List.not_mem_nil, Prod.fst, or_false]
    tauto
  · intro step hs
    have hs' : step ∈ state.output := by simpa [nextState, Core.pushState] using hs
    exact (h.outputExhausted step hs').mono (R := R) (R.usedExtends_set_true state.used edge)
  · simp [nextState, Core.pushState]
  · simp [nextState, Core.pushState]
  · have hsum := R.sum_cursor_set_succ state.cursor current
    have hbalance := h.scanBalance
    simpa [nextState, Core.pushState] using (show
      scanFuel + ∑ y : Fin R.n,
          (Core.setFin state.cursor current (state.cursor.get current + 1)).get y =
        R.incidenceCount by omega)
  · intro _
    exact h.popBalance hpath.ne_nil

theorem edgeDegree_indicator_parity {start anchor current : Fin R.n}
    {pre active output : List (Fin R.m × Fin R.n)}
    (hp : R.DenseTrail start pre anchor)
    (ha : R.DenseTrail anchor active current)
    (ho : R.DenseTrail anchor output start) (x : Fin R.n) :
    Even (R.degreeOn x (pre ++ active ++ output) +
      R.vertexIndicator x anchor + R.vertexIndicator x current) := by
  rcases hp.even_degreeOn_endpoints (R := R) (x := x) with ⟨a, ha'⟩
  rcases ha.even_degreeOn_endpoints (R := R) (x := x) with ⟨b, hb'⟩
  rcases ho.even_degreeOn_endpoints (R := R) (x := x) with ⟨c, hc'⟩
  have hs : R.vertexIndicator x start ≤ 1 := by
    unfold vertexIndicator
    split <;> omega
  have hn : R.vertexIndicator x anchor ≤ 1 := by
    unfold vertexIndicator
    split <;> omega
  refine ⟨a + b + c - R.vertexIndicator x start - R.vertexIndicator x anchor, ?_⟩
  rw [R.degreeOn_append, R.degreeOn_append]
  omega

theorem exhausted_top_eq_anchor {state : CoreState R.n R.m} {start current anchor : Fin R.n}
    {pre active : List (Fin R.m × Fin R.n)}
    (heven : ∀ x : Fin R.n, Even (R.fullDenseDegree x))
    (hsteps : R.frameSteps state.stack = pre ++ active)
    (hp : R.DenseTrail start pre anchor)
    (ha : R.DenseTrail anchor active current)
    (ho : R.DenseTrail anchor state.output start)
    (hn : ((R.combinedSteps state).map Prod.fst).Nodup)
    (hused : ∀ e : Fin R.m,
      state.used.get e = true ↔ e ∈ (R.combinedSteps state).map Prod.fst)
    (hexhausted : R.Exhausted state.used current) : current = anchor := by
  have hcover : ∀ e : Fin R.m, R.DenseInc e current →
      e ∈ (R.combinedSteps state).map Prod.fst := by
    intro e hinc
    exact (hused e).mp (hexhausted e hinc)
  have hdegree := R.degreeOn_eq_fullDenseDegree hn hcover
  have hparity := R.edgeDegree_indicator_parity hp ha ho current
  rw [← hsteps] at hparity
  change Even (R.degreeOn current (R.combinedSteps state) +
    R.vertexIndicator current anchor + R.vertexIndicator current current) at hparity
  rw [hdegree] at hparity
  rcases heven current with ⟨a, haeven⟩
  rcases hparity with ⟨b, hbeven⟩
  by_contra hne
  simp [vertexIndicator, hne] at hbeven
  omega

theorem RunInvariant.popNone {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} {current : Fin R.n}
    (hstack : state.stack =
      ({ incoming := none, vertex := current } : Frame R.n R.m) :: [])
    (h : R.RunInvariant start scanFuel (popFuel + 1) state)
    (hpath : R.StackPath start state.stack current)
    (hnone : (R.buckets.get current)[state.cursor.get current]? = none) :
    R.RunInvariant start scanFuel popFuel
      (Core.popState state [] none) := by
  have hsize : (R.buckets.get current).size ≤ state.cursor.get current :=
    Array.getElem?_eq_none_iff.mp hnone
  have hcursor : state.cursor.get current = (R.buckets.get current).size := by
    have := h.cursorPrefixUsed.1 current
    omega
  have hexhausted : R.Exhausted state.used current :=
    h.cursorPrefixUsed.exhausted_of_eq (R := R) hcursor
  have hcurrent : current = start := by
    have hp : R.StackPath start
        (({ incoming := none, vertex := current } : Frame R.n R.m) :: []) current := by
      simpa [hstack] using hpath
    exact hp.none_bottom (R := R).1
  subst current
  constructor
  · simpa [Core.popState] using h.cursorPrefixUsed
  · simp [Core.popState]
  · intro current hpath'
    have hne : ([] : List (Frame R.n R.m)) ≠ [] := StackPath.ne_nil (R := R) hpath'
    exact (hne rfl).elim
  · simpa [Core.popState, combinedSteps, hstack, frameSteps] using h.edgesNodup
  · intro e
    simpa [Core.popState, combinedSteps, hstack, frameSteps] using h.used_iff e
  · simpa [Core.popState] using h.outputExhausted
  · intro _
    simpa [Core.popState] using hexhausted
  · intro _
    obtain ⟨anchor, pre, active, hsteps, hpre, hactive, hout⟩ := h.splice hpath
    have hnil : pre = [] ∧ active = [] := by
      apply List.eq_nil_of_append_eq_nil
      simpa [hstack, frameSteps] using hsteps.symm
    rcases hnil with ⟨rfl, rfl⟩
    have hanchor : anchor = start := by
      cases hpre
      rfl
    subst anchor
    simpa [Core.popState] using hout
  · simpa [Core.popState] using h.scanBalance
  · simp [Core.popState]

theorem RunInvariant.popSome {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} {current : Fin R.n} {edge : Fin R.m}
    {rest : List (Frame R.n R.m)}
    (hstack : state.stack =
      ({ incoming := some edge, vertex := current } : Frame R.n R.m) :: rest)
    (h : R.RunInvariant start scanFuel (popFuel + 1) state)
    (hpath : R.StackPath start state.stack current)
    (hnone : (R.buckets.get current)[state.cursor.get current]? = none)
    (heven : ∀ x : Fin R.n, Even (R.fullDenseDegree x)) :
    R.RunInvariant start scanFuel popFuel
      (Core.popState state rest (some (edge, current))) := by
  have hsize : (R.buckets.get current).size ≤ state.cursor.get current :=
    Array.getElem?_eq_none_iff.mp hnone
  have hcursor : state.cursor.get current = (R.buckets.get current).size := by
    have := h.cursorPrefixUsed.1 current
    omega
  have hexhausted : R.Exhausted state.used current :=
    h.cursorPrefixUsed.exhausted_of_eq (R := R) hcursor
  have hpath' : R.StackPath start
      (({ incoming := some edge, vertex := current } : Frame R.n R.m) :: rest) current := by
    simpa [hstack] using hpath
  obtain ⟨previous, hrest, hlink⟩ := hpath'.pop (R := R)
  obtain ⟨anchor, pre, active, hsteps, hpre, hactive, hout⟩ := h.splice hpath
  have hanchor : current = anchor :=
    R.exhausted_top_eq_anchor heven hsteps hpre hactive hout h.edgesNodup h.used_iff hexhausted
  subst anchor
  let nextState := Core.popState state rest (some (edge, current))
  have hcombined : R.combinedSteps nextState = R.combinedSteps state := by
    simp [nextState, Core.popState, combinedSteps, hstack, frameSteps, List.append_assoc]
  constructor
  · simpa [nextState, Core.popState] using h.cursorPrefixUsed
  · exact Or.inr ⟨previous, by simpa [nextState, Core.popState] using hrest⟩
  · intro current' hnewPath
    have hnewPath' : R.StackPath start rest current' := by
      simpa [nextState, Core.popState] using hnewPath
    have hprev : current' = previous := hnewPath'.current_unique (R := R) hrest
    subst current'
    refine ⟨previous, R.frameSteps rest, [], by simp [nextState, Core.popState],
      hrest.trail (R := R), .nil previous, ?_⟩
    exact .cons hlink hout
  · rw [hcombined]
    exact h.edgesNodup
  · intro e
    rw [hcombined]
    simpa [nextState, Core.popState] using h.used_iff e
  · intro step hs
    simp only [nextState, Core.popState, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hexhausted
    · exact h.outputExhausted step hs
  · intro hempty
    have : rest = [] := by simpa [nextState, Core.popState] using hempty
    have hrestne : rest ≠ [] := StackPath.ne_nil (R := R) hrest
    exact (hrestne this).elim
  · intro hempty
    have : rest = [] := by simpa [nextState, Core.popState] using hempty
    have hrestne : rest ≠ [] := StackPath.ne_nil (R := R) hrest
    exact (hrestne this).elim
  · simpa [nextState, Core.popState] using h.scanBalance
  · intro hne
    have hold := h.popBalance hpath.ne_nil
    have hlen : popFuel + ((edge, current) :: state.output).length = R.m + 1 := by
      simp only [List.length_cons]
      omega
    simpa [nextState, Core.popState] using hlen

theorem RunInvariant.scanFuel_pos_of_some {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start scanFuel popFuel state)
    (x : Fin R.n) {dart : Dart R.m}
    (hget : (R.buckets.get x)[state.cursor.get x]? = some dart) : 0 < scanFuel := by
  obtain ⟨hindex, _⟩ := Array.getElem?_eq_some_iff.mp hget
  have hlt : (∑ y : Fin R.n, state.cursor.get y) <
      ∑ y : Fin R.n, (R.buckets.get y).size := by
    apply Finset.sum_lt_sum
    · intro y _
      exact h.cursorPrefixUsed.1 y
    · exact ⟨x, Finset.mem_univ x, hindex⟩
  have hbalance := h.scanBalance
  simp only [incidenceCount] at hbalance
  omega

theorem RunInvariant.output_length_le {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start scanFuel popFuel state) :
    state.output.length ≤ R.m := by
  have hout : (state.output.map Prod.fst).Nodup := by
    have hall : ((R.frameSteps state.stack).map Prod.fst ++
        state.output.map Prod.fst).Nodup := by
      simpa [combinedSteps, List.map_append] using h.edgesNodup
    exact hall.of_append_right
  simpa only [List.length_map, Fintype.card_fin] using hout.length_le_card

theorem RunInvariant.popFuel_pos_of_stack {start : Fin R.n} {scanFuel popFuel : Nat}
    {state : CoreState R.n R.m} (h : R.RunInvariant start scanFuel popFuel state)
    (hne : state.stack ≠ []) : 0 < popFuel := by
  have hbalance := h.popBalance hne
  have hlen := h.output_length_le (R := R)
  omega

/-!
The semantic recursion is separated from `TimeM`.  This keeps the invariant proof term small; the
following value theorem reconnects it to the identically branching timed implementation.
-/

def logicalRun (R : CertifiedIncidenceRepresentation G) :
    (scanFuel popFuel : Nat) → CoreState R.n R.m → CoreState R.n R.m
  | scanFuel, popFuel, state =>
      match state.stack with
      | [] => state
      | top :: rest =>
          let bucket := R.buckets.get top.vertex
          let cursor := state.cursor.get top.vertex
          match bucket[cursor]? with
          | some dart =>
              match scanFuel with
              | 0 => state
              | scanFuel + 1 =>
                  let cursors := Core.setFin state.cursor top.vertex (cursor + 1)
                  if state.used.get dart.edge then
                    logicalRun R scanFuel popFuel (Core.skipState state cursors)
                  else
                    let next := Core.otherEndpoint dart.role
                      (R.ends.get dart.edge).1 (R.ends.get dart.edge).2
                    logicalRun R scanFuel popFuel
                      (Core.pushState state (Core.setFin state.used dart.edge true) cursors
                        ({ incoming := some dart.edge, vertex := next } :: state.stack))
          | none =>
              match popFuel with
              | 0 => state
              | popFuel + 1 =>
                  match top.incoming with
                  | none => logicalRun R scanFuel popFuel (Core.popState state rest none)
                  | some edge => logicalRun R scanFuel popFuel
                      (Core.popState state rest (some (edge, top.vertex)))
termination_by scanFuel popFuel _state => scanFuel + popFuel

set_option maxHeartbeats 0

@[simp] theorem run_ret_eq_logicalRun (R : CertifiedIncidenceRepresentation G) :
    ∀ scanFuel popFuel state,
      (Core.run R scanFuel popFuel state).ret = R.logicalRun scanFuel popFuel state
  | scanFuel, popFuel, state => by
      rw [Core.run, logicalRun]
      cases hstack : state.stack with
      | nil => simp [hstack]
      | cons top rest =>
          simp only [Event.ret_stackCheck, hstack, Event.ret_stackPeek,
            Event.ret_incidenceRead, Event.ret_cursorRead, Event.ret_indexLt]
          let bucket := R.buckets.get top.vertex
          let cursor := state.cursor.get top.vertex
          cases hget : bucket[cursor]? with
          | none =>
              cases popFuel with
              | zero => simp [bucket, cursor, hget]
              | succ popFuel =>
                  cases hin : top.incoming with
                  | none =>
                      have ih := run_ret_eq_logicalRun R scanFuel popFuel
                        (Core.popState state rest none)
                      simpa [bucket, cursor, hget, hin] using ih
                  | some edge =>
                      have ih := run_ret_eq_logicalRun R scanFuel popFuel
                        (Core.popState state rest (some (edge, top.vertex)))
                      simpa [bucket, cursor, hget, hin] using ih
          | some dart =>
              cases scanFuel with
              | zero => simp [bucket, cursor, hget]
              | succ scanFuel =>
                  cases hused : state.used.get dart.edge with
                  | false =>
                      have ih := run_ret_eq_logicalRun R scanFuel popFuel
                        (Core.pushState state (Core.setFin state.used dart.edge true)
                          (Core.setFin state.cursor top.vertex
                            (state.cursor.get top.vertex + 1))
                          ({ incoming := some dart.edge
                             vertex := Core.otherEndpoint dart.role
                               (R.ends.get dart.edge).1 (R.ends.get dart.edge).2 } :: top :: rest))
                      simpa [bucket, cursor, hget, hused] using ih
                  | true =>
                      have ih := run_ret_eq_logicalRun R scanFuel popFuel
                        (Core.skipState state
                          (Core.setFin state.cursor top.vertex
                            (state.cursor.get top.vertex + 1)))
                      simpa [bucket, cursor, hget, hused] using ih
termination_by scanFuel popFuel _state => scanFuel + popFuel

set_option maxHeartbeats 800000

set_option maxHeartbeats 800000 in
theorem logicalRun_final (R : CertifiedIncidenceRepresentation G)
    (heven : ∀ x : Fin R.n, Even (R.fullDenseDegree x)) :
    ∀ scanFuel popFuel state start, R.RunInvariant start scanFuel popFuel state →
      ∃ scanFuel' popFuel',
        R.RunInvariant start scanFuel' popFuel' (R.logicalRun scanFuel popFuel state) ∧
        (R.logicalRun scanFuel popFuel state).stack = []
  | scanFuel, popFuel, state, start, h => by
      rw [logicalRun]
      cases hstack : state.stack with
      | nil => exact ⟨scanFuel, popFuel, by simpa [hstack] using h, by simp [hstack]⟩
      | cons top rest =>
          obtain ⟨current, hpath⟩ := h.stackShape.resolve_left (by simp [hstack])
          rw [hstack] at hpath
          have hvertex : top.vertex = current := hpath.head_vertex (R := R)
          subst current
          have hpathState : R.StackPath start state.stack top.vertex := hstack.symm ▸ hpath
          let bucket := R.buckets.get top.vertex
          let cursor := state.cursor.get top.vertex
          cases hget : bucket[cursor]? with
          | none =>
              cases popFuel with
              | zero => exact (by
                  have := h.popFuel_pos_of_stack (R := R) (by simp [hstack]); omega)
              | succ popFuel =>
                  cases hin : top.incoming with
                  | none =>
                      have htop : top =
                          ({ incoming := none, vertex := top.vertex } : Frame R.n R.m) := by
                        cases top with
                        | mk incoming vertex => simp only at hin ⊢; subst incoming; rfl
                      have hp : R.StackPath start
                          (({ incoming := none, vertex := top.vertex } : Frame R.n R.m) :: rest)
                          top.vertex := by rw [← htop]; exact hpath
                      have hr : rest = [] := (hp.none_bottom (R := R)).2
                      subst rest
                      have hs : state.stack =
                          [({ incoming := none, vertex := top.vertex } : Frame R.n R.m)] :=
                        hstack.trans (congrArg (fun f ↦ [f]) htop)
                      have hn := RunInvariant.popNone R hs h hpathState
                        (by simpa [bucket, cursor] using hget)
                      simpa [bucket, cursor, hget, hin] using
                        logicalRun_final R heven scanFuel popFuel
                          (Core.popState state [] none) start hn
                  | some edge =>
                      have htop : top =
                          ({ incoming := some edge, vertex := top.vertex } : Frame R.n R.m) := by
                        cases top with
                        | mk incoming vertex => simp only at hin ⊢; subst incoming; rfl
                      have hs : state.stack =
                          ({ incoming := some edge, vertex := top.vertex } : Frame R.n R.m) :: rest :=
                        hstack.trans (congrArg (fun f ↦ f :: rest) htop)
                      have hn := RunInvariant.popSome R hs h hpathState
                        (by simpa [bucket, cursor] using hget) heven
                      simpa [bucket, cursor, hget, hin] using
                        logicalRun_final R heven scanFuel popFuel
                          (Core.popState state rest (some (edge, top.vertex))) start hn
          | some dart =>
              cases scanFuel with
              | zero => exact (by
                  have := h.scanFuel_pos_of_some (R := R) top.vertex
                    (by simpa [bucket, cursor] using hget); omega)
              | succ scanFuel =>
                  obtain ⟨hi, hget'⟩ := Array.getElem?_eq_some_iff.mp hget
                  have hd : dart ∈ (R.buckets.get top.vertex).toList := by
                    have : dart ∈ bucket := by rw [← hget']; exact Array.getElem_mem hi
                    simpa [bucket] using this
                  have hl := R.denseLink_otherEndpoint hd
                  cases hu : state.used.get dart.edge with
                  | false =>
                      have hn := h.push (R := R) hpathState
                        (by simpa [bucket, cursor] using hget) rfl hl hu
                      simpa [bucket, cursor, hget, hu, hstack] using
                        logicalRun_final R heven scanFuel popFuel _ start hn
                  | true =>
                      have hn := h.skip (R := R) top.vertex dart
                        (by simpa [bucket, cursor] using hget) hu
                      simpa [bucket, cursor, hget, hu] using
                        logicalRun_final R heven scanFuel popFuel _ start hn
termination_by scanFuel popFuel _state _start _h => scanFuel + popFuel

/-- The executable loop cannot reach either fuel-exhaustion fallback from a certified state. -/
theorem run_final (R : CertifiedIncidenceRepresentation G)
    (heven : ∀ x : Fin R.n, Even (R.fullDenseDegree x))
    (scanFuel popFuel : Nat) (state : CoreState R.n R.m) (start : Fin R.n)
    (h : R.RunInvariant start scanFuel popFuel state) :
    ∃ scanFuel' popFuel',
      R.RunInvariant start scanFuel' popFuel' (Core.run R scanFuel popFuel state).ret ∧
      (Core.run R scanFuel popFuel state).ret.stack = [] := by
  rw [R.run_ret_eq_logicalRun]
  exact R.logicalRun_final heven scanFuel popFuel state start h

end CertifiedIncidenceRepresentation

end Benchmarks.Hierholzer.Mathlib
