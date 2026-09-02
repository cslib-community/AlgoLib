/-
Copyright (c) 2026 AlgoLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Huang.JiangYi (co/ Claude Opus 5)
-/
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Sym.Card
import AlgoLib.Theory.Graph.Basic

/-!
# Finiteness of graphs

When the vertex set of a graph is finite, the edge set is finite as well.
This file packages those facts together with `Finset` versions of the
vertex and edge sets, and basic cardinality bounds.

## Two layers, and which one to assume

`Finite` is a `Prop` — it merely asserts that a finite enumeration exists.
`Fintype` is *data* — it carries the `Finset` of all elements. The two are
classically equivalent (`Fintype.ofFinite`), but they are not
interchangeable as hypotheses, so this file offers both and downstream files
should choose deliberately.

*The theory layer* — statements about an arbitrary graph: cardinality
bounds, connectivity, separating sets — assumes only `[Finite V(G)]`
(equivalently `[Finite G.vertexSet]`). `Finite E(G)` then follows from the
instances registered here, with no further hypotheses. Prefer this whenever
the conclusion is a `Prop`: no decidability is demanded of the caller, and
because `Finite` is proof-irrelevant, two instances are definitionally
equal, so no `Fintype` diamond can obstruct `rw` / `simp` downstream. This
is also Mathlib's convention, enforced by the `unusedFintypeInType` and
`unusedDecidableInType` linters.

*The computable layer* — anything that must actually produce or traverse a
`Finset`, such as a BFS — assumes `[Fintype V(G)]`, plus `[DecidableEq α]`
and `[DecidablePred (· ∈ E(G))]` where an edge `Finset` is built by
filtering. These are genuine extra assumptions: a graph given by a classical
predicate satisfies none of them without choice. Ask for them only in the
declarations that consume the data. In particular the vertex-side
`compute…` definitions need no edge decidability.

The two layers meet in the `computeVertexFinset_eq_vertexFinset` /
`computeEdgeFinset_eq_edgeFinset` and `coe_compute…Finset` lemmas: a result
established constructively over `Finset`s is transported to a statement
phrased with `V(G)` / `E(G)`. Note that the `Fintype E(G)` obtained
classically from `[Finite V(G)]` is *not* definitionally the one the
computable layer builds — which is precisely why those bridge lemmas are
proved rather than assumed.

## Main results

* `SimpleGraph.vertexFinset` / `SimpleDiGraph.vertexFinset` — the vertex
  set as a `Finset`.
* `SimpleGraph.edgeFinset` / `SimpleDiGraph.edgeFinset` — the edge set
  as a `Finset`.
* `SimpleGraph.instFiniteEdgeSetOfFinite` /
  `SimpleDiGraph.instFiniteEdgeSetOfFinite` — `Finite G.edgeSet` from
  `[Finite G.vertexSet]`, `Prop`-valued, no decidability. The theory layer.
* `SimpleGraph.instFiniteEdgeSet` / `SimpleDiGraph.instFiniteEdgeSet` —
  `Fintype G.edgeSet` from `[Fintype G.vertexSet]` plus decidability.
  *Data*; the computable layer. (Name kept for compatibility, despite
  producing a `Fintype`.)
* `compute…Finset` and the `coe_compute…Finset` / `…_eq_…Finset` bridge
  lemmas between the two layers.
* `SimpleGraph.card_edgeFinset_le_card_choose_two` — `|E(G)| ≤ C(|V(G)|, 2)`.
* `SimpleDiGraph.card_edgeFinset_le_two_card_choose_two` —
  `|E(G)| ≤ 2·C(|V(G)|, 2)`.
-/

namespace AlgoLib

open scoped AlgoLib

variable {α : Type*}

/-! ## Finiteness instances for edge sets -/

/-- The `{e : Sym2 α | ∀ v ∈ e, v ∈ S}` set is finite whenever `S` is. -/
private lemma sym2_of_subset_finite (S : Set α) (hS : S.Finite) :
    {e : Sym2 α | ∀ v ∈ e, v ∈ S}.Finite := by
  classical
  have hfin : Finite S := hS
  haveI : Fintype S := Fintype.ofFinite _
  haveI : Fintype (Sym2 S) := inferInstance
  -- The set is contained in the image of `Sym2 S` under `Subtype.val`.
  refine Set.Finite.subset (Set.toFinite (Sym2.map (Subtype.val : S → α) '' Set.univ)) ?_
  intro e he
  induction e with
  | h x y =>
    refine ⟨s(⟨x, he x ?_⟩, ⟨y, he y ?_⟩), trivial, by simp [Sym2.map_mk]⟩ <;> simp

instance SimpleGraph.instFiniteEdgeSet (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] :
    Fintype G.edgeSet :=
  let candidatePairs : Finset (Sym2 α) :=
    (Finset.univ : Finset G.vertexSet).sym2.image (Sym2.map Subtype.val)
  let edgeFinset : Finset (Sym2 α) :=
    candidatePairs.filter (· ∈ G.edgeSet)
  Fintype.ofFinset edgeFinset (by
    intro e
    simp only [edgeFinset, candidatePairs, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨_, he⟩
      exact he
    · intro he
      constructor
      · induction e using Sym2.ind with
        | _ x y =>
          have hx : x ∈ G.vertexSet := G.incidence' _ he x (Sym2.mem_mk_left x y)
          have hy : y ∈ G.vertexSet := G.incidence' _ he y (Sym2.mem_mk_right x y)
          exact ⟨s(⟨x, hx⟩, ⟨y, hy⟩), by simp, rfl⟩
      · exact he)

instance SimpleDiGraph.instFiniteEdgeSet (G : SimpleDiGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] :
    Fintype G.edgeSet :=
  let candidatePairs : Finset (α × α) :=
    ((Finset.univ : Finset G.vertexSet) ×ˢ (Finset.univ : Finset G.vertexSet)).image
      (fun p => (p.1.val, p.2.val))
  let edgeFinset : Finset (α × α) :=
    candidatePairs.filter (· ∈ G.edgeSet)
  Fintype.ofFinset edgeFinset (by
    intro e
    simp only [edgeFinset, candidatePairs, Finset.mem_filter, Finset.mem_image,
               Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, he⟩
      exact he
    · intro he
      constructor
      · rcases e with ⟨x, y⟩
        have hx : x ∈ G.vertexSet := (G.incidence' (x, y) he).1
        have hy : y ∈ G.vertexSet := (G.incidence' (x, y) he).2
        exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
      · exact he)

/-- Backwards-compatible named form. -/
theorem SimpleGraph.fin_vertexSet_fin_edgeSet (G : SimpleGraph α)
    (hfin : Fintype G.vertexSet) :
    Finite G.edgeSet := by
  classical
  haveI : Fintype G.vertexSet := hfin
  haveI : Fintype G.edgeSet := SimpleGraph.instFiniteEdgeSet G
  exact inferInstance

/-- Backwards-compatible named form. -/
theorem SimpleDiGraph.fin_vertexSet_fin_edgeSet (G : SimpleDiGraph α)
    (hfin : Fintype G.vertexSet) :
    Finite G.edgeSet := by
  classical
  haveI : Fintype G.vertexSet := hfin
  haveI : Fintype G.edgeSet := SimpleDiGraph.instFiniteEdgeSet G
  exact inferInstance

/-! ### Prop-level finiteness: `[Finite V(G)]` is enough

The `Fintype` instances above are *data*: building `E(G)` as a `Finset` requires
`DecidableEq α` and a decision procedure for edge membership. Those are genuine
assumptions, and theory-level statements about an arbitrary graph should not carry
them. The instances below are `Prop`-valued, so `Classical` choice may be used in
their proofs at no cost — proof irrelevance means no choice-derived data can leak
into a statement, and two such instances are definitionally equal, so no `Fintype`
diamond can arise downstream. -/

/-- Finiteness of the vertex set transfers to the edge set, with no decidability
assumptions. This is the instance the theory layer relies on. -/
instance SimpleGraph.instFiniteEdgeSetOfFinite (G : SimpleGraph α)
    [hfin : Finite G.vertexSet] :
    Finite G.edgeSet := by
  have hVfin : G.vertexSet.Finite := hfin
  have hsubset : G.edgeSet ⊆ {e : Sym2 α | ∀ v ∈ e, v ∈ G.vertexSet} :=
    fun e he v hv => G.incidence' e he v hv
  exact ((sym2_of_subset_finite G.vertexSet hVfin).subset hsubset).to_subtype

/-- Finiteness of the vertex set transfers to the edge set, with no decidability
assumptions. This is the instance the theory layer relies on. -/
instance SimpleDiGraph.instFiniteEdgeSetOfFinite (G : SimpleDiGraph α)
    [hfin : Finite G.vertexSet] :
    Finite G.edgeSet := by
  classical
  haveI : Fintype G.vertexSet := Fintype.ofFinite _
  haveI : Fintype (G.vertexSet × G.vertexSet) := inferInstance
  apply Finite.of_injective (β := G.vertexSet × G.vertexSet) fun e =>
    (⟨e.val.1, (G.incidence' _ e.property).1⟩,
     ⟨e.val.2, (G.incidence' _ e.property).2⟩)
  rintro ⟨⟨a, b⟩, ha⟩ ⟨⟨c, d⟩, hc⟩ heq
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at heq
  apply Subtype.ext
  ext <;> [exact heq.1; exact heq.2]

/-! ## Vertex finset -/

/-- The vertex set of `G` as a `Finset`, when it is finite. -/
def SimpleGraph.vertexFinset (G : SimpleGraph α) [Fintype G.vertexSet] :
    Finset α :=
  (G.vertexSet).toFinset

/-- The vertex set of `G` as a `Finset`, when it is finite. -/
def SimpleDiGraph.vertexFinset (G : SimpleDiGraph α) [Fintype G.vertexSet] :
    Finset α :=
  (G.vertexSet).toFinset

@[simp] lemma SimpleGraph.mem_vertexFinset (G : SimpleGraph α) [Fintype G.vertexSet]
    {v : α} : v ∈ G.vertexFinset ↔ v ∈ G.vertexSet := by
  simp [vertexFinset]

@[simp] lemma SimpleDiGraph.mem_vertexFinset (G : SimpleDiGraph α) [Fintype G.vertexSet]
    {v : α} : v ∈ G.vertexFinset ↔ v ∈ G.vertexSet := by
  simp [vertexFinset]

@[simp] lemma SimpleGraph.coe_vertexFinset (G : SimpleGraph α) [Fintype G.vertexSet] :
    (G.vertexFinset : Set α) = G.vertexSet := by
  ext; simp

@[simp] lemma SimpleDiGraph.coe_vertexFinset (G : SimpleDiGraph α) [Fintype G.vertexSet] :
    (G.vertexFinset : Set α) = G.vertexSet := by
  ext; simp

/-! ## Edge finset -/

def SimpleGraph.edgeFinset (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] :
    Finset (Sym2 α) :=
  (G.edgeSet).toFinset

/-- The edge set of `G` as a `Finset`. -/
def SimpleDiGraph.edgeFinset (G : SimpleDiGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] :
    Finset (α × α) :=
  (G.edgeSet).toFinset

@[simp] lemma SimpleGraph.mem_edgeFinset (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]
    {e : Sym2 α} : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet := by
  simp [edgeFinset]

@[simp] lemma SimpleDiGraph.mem_edgeFinset (G : SimpleDiGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)]
    {e : α × α} : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet := by
  simp [edgeFinset]

@[simp] lemma SimpleGraph.coe_edgeFinset (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] :
    (G.edgeFinset : Set (Sym2 α)) = G.edgeSet := by
  ext; simp

@[simp] lemma SimpleDiGraph.coe_edgeFinset (G : SimpleDiGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] :
    (G.edgeFinset : Set (α × α)) = G.edgeSet := by
  ext; simp

/-! ## Convenience: ncard and Set.Finite from Finset cardinalities -/

@[simp] lemma SimpleGraph.ncard_vertexSet (G : SimpleGraph α) [Fintype G.vertexSet] :
    Set.ncard G.vertexSet = G.vertexFinset.card := by
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  congr 1; ext; simp only [Set.toFinite_toFinset, Set.mem_toFinset, mem_vertexFinset]

@[simp] lemma SimpleDiGraph.ncard_vertexSet (G : SimpleDiGraph α)
    [Fintype G.vertexSet] :
    Set.ncard G.vertexSet = G.vertexFinset.card := by
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  congr 1; ext; simp only [Set.toFinite_toFinset, Set.mem_toFinset, mem_vertexFinset]

@[simp] lemma SimpleGraph.ncard_edgeSet (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] :
    Set.ncard G.edgeSet = G.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  congr 1; ext; simp only [Set.toFinite_toFinset, Set.mem_toFinset, mem_edgeFinset]

@[simp] lemma SimpleDiGraph.ncard_edgeSet (G : SimpleDiGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] :
    Set.ncard G.edgeSet = G.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  congr 1; ext; simp only [Set.toFinite_toFinset, Set.mem_toFinset, mem_edgeFinset]

/-! ## Cardinality bounds -/

/-- The vertex finset cardinality equals the `Fintype.card` of the vertex
subtype. -/
private lemma SimpleGraph.vertexFinset_card_eq (G : SimpleGraph α) [Finite G.vertexSet]
    [Fintype G.vertexSet] :
    G.vertexFinset.card = Fintype.card G.vertexSet := by
  simp [SimpleGraph.vertexFinset]

/-- Lift an edge of `G` to a non-diagonal `Sym2` on the vertex subtype. -/
private lemma SimpleGraph.edge_lift (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ G.edgeSet) :
    ∃ s : Sym2 G.vertexSet, ¬ s.IsDiag ∧ s.map Subtype.val = e := by
  induction e with
  | h x y =>
    refine ⟨s(⟨x, G.incidence' _ he x (by simp)⟩,
              ⟨y, G.incidence' _ he y (by simp)⟩), ?_, by simp [Sym2.map_mk]⟩
    have hne : ¬ (s(x, y) : Sym2 α).IsDiag := G.loopless' _ he
    simp only [Sym2.mk_isDiag_iff, Subtype.mk.injEq, ne_eq] at hne ⊢
    exact hne

/-- The edge set of a simple graph has size at most `C(|V|, 2)`.
The proof embeds `E(G)` into the off-diagonal `Sym2` of the vertex set. -/
theorem SimpleGraph.card_edgeFinset_le_card_choose_two
    (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] :
    G.edgeFinset.card ≤ G.vertexFinset.card.choose 2 := by
  classical
  -- Build the injection `E(G) ↪ {s : Sym2 V(G) // ¬ s.IsDiag}`.
  let f : G.edgeFinset → {s : Sym2 G.vertexSet // ¬ s.IsDiag} := fun e =>
    ⟨(G.edge_lift (G.mem_edgeFinset.mp e.property)).choose,
     (G.edge_lift (G.mem_edgeFinset.mp e.property)).choose_spec.1⟩
  have f_inj : Function.Injective f := by
    rintro ⟨e1, he1⟩ ⟨e2, he2⟩ heq
    have h1 := (G.edge_lift (G.mem_edgeFinset.mp he1)).choose_spec.2
    have h2 := (G.edge_lift (G.mem_edgeFinset.mp he2)).choose_spec.2
    apply Subtype.ext
    have hch : (G.edge_lift (G.mem_edgeFinset.mp he1)).choose =
        (G.edge_lift (G.mem_edgeFinset.mp he2)).choose := by
      have := congrArg Subtype.val heq
      simpa [f] using this
    have := congrArg (Sym2.map Subtype.val) hch
    rw [h1, h2] at this
    exact this
  calc G.edgeFinset.card
      = Fintype.card G.edgeFinset := (Fintype.card_coe _).symm
    _ ≤ Fintype.card {s : Sym2 G.vertexSet // ¬ s.IsDiag} :=
        Fintype.card_le_of_injective f f_inj
    _ = (Fintype.card G.vertexSet).choose 2 := Sym2.card_subtype_not_diag
    _ = G.vertexFinset.card.choose 2 := by rw [G.vertexFinset_card_eq]

/-- The vertex finset cardinality of a `SimpleDiGraph` equals the
`Fintype.card` of the vertex subtype. -/
private lemma SimpleDiGraph.vertexFinset_card_eq (G : SimpleDiGraph α)
    [Fintype G.vertexSet] :
    G.vertexFinset.card = Fintype.card G.vertexSet := by
  simp [SimpleDiGraph.vertexFinset]

/-- The edge set of a simple directed graph has size at most `2·C(|V|, 2)`.
The proof embeds `E(G)` into the off-diagonal of `V × V`. -/
theorem SimpleDiGraph.card_edgeFinset_le_two_card_choose_two
    (G : SimpleDiGraph α)
    [Fintype G.vertexSet] [DecidableEq α] [DecidablePred (· ∈ G.edgeSet)] :
    G.edgeFinset.card ≤ 2 * G.vertexFinset.card.choose 2 := by
  classical
  -- Build the injection `E(G) ↪ {p : V × V // p.1 ≠ p.2}`.
  let f : G.edgeFinset → {p : G.vertexSet × G.vertexSet // p.1 ≠ p.2} := fun e =>
    let he := G.mem_edgeFinset.mp e.property
    ⟨(⟨e.val.1, (G.incidence' _ he).1⟩, ⟨e.val.2, (G.incidence' _ he).2⟩), by
      simp only [ne_eq, Subtype.mk.injEq]
      exact G.loopless' _ he⟩
  have f_inj : Function.Injective f := by
    rintro ⟨⟨a, b⟩, h1⟩ ⟨⟨c, d⟩, h2⟩ heq
    simp only [f, Subtype.mk.injEq, Prod.mk.injEq, Subtype.mk.injEq] at heq
    apply Subtype.ext
    ext
    · exact heq.1
    · exact heq.2
  -- Cardinality of `{p : V × V // p.1 ≠ p.2}` is `n(n-1) = 2·C(n,2)`.
  have hcard_off :
      Fintype.card {p : G.vertexSet × G.vertexSet // p.1 ≠ p.2} =
        Fintype.card G.vertexSet * (Fintype.card G.vertexSet - 1) := by
    classical
    rw [Fintype.card_subtype]
    have hfilt :
        ((Finset.univ : Finset (G.vertexSet × G.vertexSet)).filter
            fun p => p.1 ≠ p.2) =
          (Finset.univ : Finset G.vertexSet).offDiag := by
      ext ⟨x, y⟩
      simp [Finset.mem_offDiag]
    rw [hfilt, Finset.offDiag_card]
    simp [Finset.card_univ, Nat.mul_sub_one]
  have h2c : 2 * (Fintype.card G.vertexSet).choose 2 =
      Fintype.card G.vertexSet * (Fintype.card G.vertexSet - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd]
  calc G.edgeFinset.card
      = Fintype.card G.edgeFinset := (Fintype.card_coe _).symm
    _ ≤ Fintype.card {p : G.vertexSet × G.vertexSet // p.1 ≠ p.2} :=
        Fintype.card_le_of_injective f f_inj
    _ = Fintype.card G.vertexSet * (Fintype.card G.vertexSet - 1) := hcard_off
    _ = 2 * (Fintype.card G.vertexSet).choose 2 := h2c.symm
    _ = 2 * G.vertexFinset.card.choose 2 := by rw [G.vertexFinset_card_eq]

/-! ## Computable variants

These definitions spell out the `Finset`s by explicit construction, for users
who want to `#eval` a vertex or edge list, together with equality lemmas tying
them back to `vertexFinset` / `edgeFinset`.

The vertex-side definitions need only `[Fintype V(G)]` (plus `DecidableEq α`
for downstream `Finset` operations): deciding *edge* membership is irrelevant to
building the vertex `Finset`, and demanding it there would force every consumer of
`computeVertexFinset` to carry a `DecidablePred (· ∈ E(G))` instance it never uses.

TODO. This section predates the move from `Finite` to `Fintype` in the
`vertexFinset` / `edgeFinset` definitions above, which is what used to make them
`noncomputable`. Now that both layers go through `Set.toFinset`,
`computeVertexFinset` is definitionally `vertexFinset`, and `computeEdgeFinset`
differs from `edgeFinset` only in performing the `filter` explicitly rather than
through the `Fintype` instance. Consider collapsing the duplication — but only
together with the downstream `Decidable` / `Computable` files, which name these
definitions throughout. -/

/-- Computable variant of `vertexFinset`. -/
def SimpleGraph.computeVertexFinset (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] : Finset α :=
  G.vertexSet.toFinset

/-- Computable variant of `vertexFinset`. -/
def SimpleDiGraph.computeVertexFinset (G : SimpleDiGraph α)
    [Fintype G.vertexSet] [DecidableEq α] : Finset α :=
  G.vertexSet.toFinset

@[simp] lemma SimpleGraph.mem_computeVertexFinset (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] {v : α} :
    v ∈ G.computeVertexFinset ↔ v ∈ G.vertexSet := by
  simp [computeVertexFinset]

@[simp] lemma SimpleDiGraph.mem_computeVertexFinset (G : SimpleDiGraph α)
    [Fintype G.vertexSet] [DecidableEq α] {v : α} :
    v ∈ G.computeVertexFinset ↔ v ∈ G.vertexSet := by
  simp [computeVertexFinset]

/-- The explicitly-built and the `Set.toFinset` vertex finsets agree. -/
lemma SimpleGraph.computeVertexFinset_eq_vertexFinset (G : SimpleGraph α)
    [Fintype G.vertexSet] [DecidableEq α] :
    G.computeVertexFinset = G.vertexFinset := by
  ext v; simp

/-- The explicitly-built and the `Set.toFinset` vertex finsets agree. -/
lemma SimpleDiGraph.computeVertexFinset_eq_vertexFinset (G : SimpleDiGraph α)
    [Fintype G.vertexSet] [DecidableEq α] :
    G.computeVertexFinset = G.vertexFinset := by
  ext v; simp

/-- Computable variant of `edgeFinset`. Iterates over all unordered pairs
of vertices and keeps those that lie in `E(G)`. -/
def SimpleGraph.computeEdgeFinset (G : SimpleGraph α)
    [DecidableEq α] [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)] :
    Finset (Sym2 α) :=
  (((Finset.univ : Finset G.vertexSet).sym2).image (Sym2.map Subtype.val)).filter
    (· ∈ G.edgeSet)

/-- Computable variant of `edgeFinset`. Iterates over all ordered pairs of
vertices and keeps those that lie in `E(G)`. -/
def SimpleDiGraph.computeEdgeFinset (G : SimpleDiGraph α)
    [DecidableEq α] [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)] :
    Finset (α × α) :=
  (((Finset.univ : Finset G.vertexSet) ×ˢ
      (Finset.univ : Finset G.vertexSet)).image
    (fun p => (p.1.val, p.2.val))).filter (· ∈ G.edgeSet)

@[simp] lemma SimpleGraph.mem_computeEdgeFinset (G : SimpleGraph α)
    [DecidableEq α] [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)]
    {e : Sym2 α} : e ∈ G.computeEdgeFinset ↔ e ∈ G.edgeSet := by
  classical
  simp only [computeEdgeFinset, Finset.mem_filter, Finset.mem_image,
    Finset.mem_sym2_iff, Finset.mem_univ]
  refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
  induction e with
  | h x y =>
    refine ⟨s(⟨x, G.incidence' _ he x (by simp)⟩,
              ⟨y, G.incidence' _ he y (by simp)⟩),
            ?_, by simp [Sym2.map_mk]⟩
    intro a ha
    simp only [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl <;> simp

@[simp] lemma SimpleDiGraph.mem_computeEdgeFinset (G : SimpleDiGraph α)
    [DecidableEq α] [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)]
    {e : α × α} : e ∈ G.computeEdgeFinset ↔ e ∈ G.edgeSet := by
  classical
  simp only [computeEdgeFinset, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product, Finset.mem_univ, true_and, and_true]
  refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
  refine ⟨(⟨e.1, (G.incidence' _ he).1⟩, ⟨e.2, (G.incidence' _ he).2⟩), ?_⟩
  rfl

/-- The explicitly-built and the `Set.toFinset` edge finsets agree. -/
lemma SimpleGraph.computeEdgeFinset_eq_edgeFinset (G : SimpleGraph α)
    [DecidableEq α] [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)] :
    G.computeEdgeFinset = G.edgeFinset := by
  ext e; simp

/-- The explicitly-built and the `Set.toFinset` edge finsets agree. -/
lemma SimpleDiGraph.computeEdgeFinset_eq_edgeFinset (G : SimpleDiGraph α)
    [DecidableEq α] [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)] :
    G.computeEdgeFinset = G.edgeFinset := by
  ext e; simp

/-! ### Coercions back to the sets

The `Finset` views coerce back to the very sets they were built from. These are the
lemmas that let a statement phrased with `V(G)` / `E(G)` — as every connectivity
predicate is — be discharged from the `Finset` layer, so the right-hand sides use the
notation deliberately. -/

@[simp] lemma SimpleGraph.coe_computeVertexFinset (G : SimpleGraph α)
    [DecidableEq α] [Fintype G.vertexSet] :
    (G.computeVertexFinset : Set α) = V(G) :=
  Set.ext fun _ => G.mem_computeVertexFinset

@[simp] lemma SimpleDiGraph.coe_computeVertexFinset (G : SimpleDiGraph α)
    [DecidableEq α] [Fintype G.vertexSet] :
    (G.computeVertexFinset : Set α) = V(G) :=
  Set.ext fun _ => G.mem_computeVertexFinset

@[simp] lemma SimpleGraph.coe_computeEdgeFinset (G : SimpleGraph α)
    [DecidableEq α] [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)] :
    (G.computeEdgeFinset : Set (Sym2 α)) = E(G) :=
  Set.ext fun _ => G.mem_computeEdgeFinset

@[simp] lemma SimpleDiGraph.coe_computeEdgeFinset (G : SimpleDiGraph α)
    [DecidableEq α] [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)] :
    (G.computeEdgeFinset : Set (α × α)) = E(G) :=
  Set.ext fun _ => G.mem_computeEdgeFinset

/-! ## Convenience: `[Finite V(G)]` is enough

A lemma whose conclusion is a `Prop` should need to write only
`[Finite V(G)]` (i.e. `[Finite G.vertexSet]`). That single assumption gives:

* `Finite E(G)` / `Finite G.edgeSet`, by the instances registered above.
* `Set.Finite G.vertexSet`, `Set.Finite G.edgeSet`, by the lemmas below.

It does *not* give `Fintype G.vertexSet` or the `vertexFinset` / `edgeFinset`
views. `Fintype.ofFinite` is noncomputable and deliberately not an instance:
registering it would make every `Finset` in the development choice-derived and
would clash with any `Fintype` a caller supplies by hand. A declaration that
genuinely needs the `Finset` data therefore assumes `[Fintype V(G)]` itself and
lives in the computable layer; a proof that needs it only transiently can open
`classical` and call `Fintype.ofFinite` locally, where the choice cannot escape.

The lemmas in this section let the user move freely between `Set.ncard`,
`Set.Finite.toFinset.card`, and `vertexFinset.card` / `edgeFinset.card`. -/

/-- A `[Finite V(G)]` hypothesis yields `Set.Finite V(G)`. -/
lemma SimpleGraph.vertexSet_finite (G : SimpleGraph α) [Finite G.vertexSet] :
    G.vertexSet.Finite := Set.toFinite G.vertexSet

/-- A `[Finite V(G)]` hypothesis yields `Set.Finite V(G)`. -/
lemma SimpleDiGraph.vertexSet_finite (G : SimpleDiGraph α) [Finite G.vertexSet] :
    G.vertexSet.Finite := Set.toFinite G.vertexSet

/-- A `[Finite V(G)]` hypothesis yields `Set.Finite E(G)`. No decidability is
required: this goes through `SimpleGraph.instFiniteEdgeSetOfFinite`. -/
lemma SimpleGraph.edgeSet_finite (G : SimpleGraph α) [Finite G.vertexSet] :
    G.edgeSet.Finite := Set.toFinite G.edgeSet

/-- A `[Finite V(G)]` hypothesis yields `Set.Finite E(G)`. No decidability is
required: this goes through `SimpleDiGraph.instFiniteEdgeSetOfFinite`. -/
lemma SimpleDiGraph.edgeSet_finite (G : SimpleDiGraph α) [Finite G.vertexSet] :
    G.edgeSet.Finite := Set.toFinite G.edgeSet

end AlgoLib
