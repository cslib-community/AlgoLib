/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Lattice

/-!
# Executable undirected multigraphs: cuts and contraction

Pure graph theory, used by the contraction algorithms. Nothing here
mentions randomness, cost, or `PMF`: it is Mathlib-only mathematics.

## Relation to `AlgoLib.Graph`

This file does not build on `AlgoLib.Graph α β`, for reasons of
executability rather than taste. Karger draws an edge uniformly at
random and must do so in a program, so the edge collection has to be an
ordered container with a stable `j`-th element; and the analysis counts
crossing edges *with multiplicity*, so the count must not deduplicate.
A `Finset (Sym2 α)` fails the second requirement by construction, and a
`Set` fails the first.

The definitions are nevertheless aligned with `AlgoLib.Graph` so that an
adapter stays mechanical:

* endpoints are `Sym2 α`, matching `Edge.endpoints`;
* `WF` is the `incidence` / `loopless` pair;
* our `List (Sym2 α)` is `Set (Edge α (Fin m))` with the list position
  playing the role of the edge label.

Two divergences are forced by executability, and are documented at their
definitions: multiplicity is carried by repetition in a `List` rather
than by a label over a noncomputable `Set`, and contraction merges the
two endpoints into a vertex of the same type, chosen by the caller,
rather than into a quotient of the vertex type by a `Setoid`, so that
the vertex type survives the contraction loop.

Of the two adapters, the downward one (`SimpleGraph α → MultiGraph α`,
via `computeVertexFinset` and `computeEdgeFinset.toList`) is nearly
free. The upward one needs finiteness instances and a label-preserving
edge boundary for `Graph`, neither of which exists yet. Both are left
for a follow-up.
-/

namespace AlgoLib

variable {α : Type} [DecidableEq α]

/-! ## The multigraph model -/

/-- An undirected multigraph: a vertex set plus an edge list, with
parallel edges repeated (one entry per copy) and no loops.

Endpoints are a `Sym2 α`, Mathlib's unordered pair, matching GraphLib's
`Edge.endpoints` (`GraphLib/Graph/Basic.lean`) and Weixuan's
`abbrev Edge := Sym2`. Orientation is therefore not merely irrelevant,
it is inexpressible: `s(u, v)` and `s(v, u)` are the same term.

We diverge from GraphLib on multiplicity only. GraphLib distinguishes
parallel edges by an `edgeLabel` and stores edges in a `Set`, which is
noncomputable; here an edge is repeated once per copy in a `List`, so
that drawing an edge uniformly with multiplicity is just
`randFin edges.length` and the development stays executable. Our
`List (Sym2 α)` is exactly GraphLib's `Set (Edge α (Fin m))` with the
list position playing the role of the label. -/
structure MultiGraph (α : Type) where
  /-- The finite set of vertices. -/
  verts : Finset α
  /-- The edge list; each parallel edge is listed once per copy. -/
  edges : List (Sym2 α)

namespace MultiGraph

/-- Well-formedness: every edge joins two distinct vertices of the
graph. Field names follow GraphLib's `incidence` / `loopless`. -/
structure WF (g : MultiGraph α) : Prop where
  /-- Every endpoint of an edge is a vertex. -/
  incidence : ∀ e ∈ g.edges, ∀ v ∈ e, v ∈ g.verts
  /-- No edge is a loop. -/
  loopless : ∀ e ∈ g.edges, ¬ e.IsDiag

/-! ### Cuts

Ported from GraphLib's `Cuts/Basic.lean` (`Cut`, `weight`,
`isSTCut`, `stMinCutValue`), specialized to unweighted multigraphs:
the weight of a cut is the number of crossing edges, counted with
multiplicity. -/

/-- The crossing test, as a `Bool`, built with `Sym2.lift`. The
symmetry argument is the well-definedness obligation of the lift, so
a direction-sensitive crossing predicate cannot even be written down,
this is what makes the model undirected by construction rather than by
after-the-fact proof. -/
def crossingB (S : Finset α) : Sym2 α → Bool :=
  Sym2.lift ⟨fun a b => decide (a ∈ S) != decide (b ∈ S), fun _ _ => bne_comm ..⟩

/-- Edge `e` crosses the vertex set `S` if exactly one endpoint lies
in `S`. -/
def Crossing (S : Finset α) (e : Sym2 α) : Prop := crossingB S e = true

instance (S : Finset α) : DecidablePred (Crossing S) :=
  fun e => inferInstanceAs (Decidable (crossingB S e = true))

@[simp] lemma crossing_mk (S : Finset α) (a b : α) :
    Crossing S s(a, b) ↔ ¬(a ∈ S ↔ b ∈ S) := by
  show (decide (a ∈ S) != decide (b ∈ S)) = true ↔ _
  simp only [bne_iff_ne, ne_eq, decide_eq_decide]

/-- The value of the cut induced by `S`: the number of crossing edges,
counted with multiplicity (GraphLib's `Cut.weight` with unit weights). -/
def cutValue (g : MultiGraph α) (S : Finset α) : ℕ :=
  g.edges.countP fun e => decide (Crossing S e)

/-- `S` induces a (proper, global) cut of `g`: it consists of vertices,
and both sides are nonempty. -/
structure IsCut (g : MultiGraph α) (S : Finset α) : Prop where
  /-- The cut set consists of vertices. -/
  subset : S ⊆ g.verts
  /-- The near side is nonempty. -/
  nonempty : S.Nonempty
  /-- The far side is nonempty. -/
  proper : ∃ v ∈ g.verts, v ∉ S

/-- `parts` partitions the vertices of `g` into at least two non-empty blocks.
vertex classes rather than a single side. -/
structure IsCutPartition (g : MultiGraph α) (parts : Finset (Finset α)) : Prop where
  /-- Every block consists of vertices. -/
  subset : ∀ S ∈ parts, S ⊆ g.verts
  /-- Every block is nonempty. -/
  nonempty : ∀ S ∈ parts, S.Nonempty
  /-- Every vertex lies in exactly one block. -/
  exists_unique : ∀ a ∈ g.verts, ∃! S, S ∈ parts ∧ a ∈ S
  /-- There are at least two blocks, so each one is a proper cut and
  the partition separates something. -/
  two_le : 2 ≤ parts.card

/-- The global minimum-cut value (GraphLib's `stMinCutValue` pattern:
an `sInf` over achievable cut values, quantified over all cuts instead
of `s`-`t` separators). -/
noncomputable def minCutValue (g : MultiGraph α) : ℕ :=
  sInf {c : ℕ | ∃ S : Finset α, g.IsCut S ∧ g.cutValue S = c}

/-- `S` is a minimum cut of `g`: a cut whose value is the smallest
there is. -/
structure IsMinCut (g : MultiGraph α) (S : Finset α) : Prop where
  /-- It is a cut. -/
  isCut : g.IsCut S
  /-- Its value is the minimum. -/
  value : g.cutValue S = g.minCutValue

/-- A run's output `o = (sides, value)` reports a cut of `g`: the
sides partition the vertices, and each side is a cut of exactly the
reported value. -/
structure IsCutOutput (g : MultiGraph α) (o : Finset (Finset α) × ℕ) : Prop where
  /-- The sides partition the vertices. -/
  partition : g.IsCutPartition o.1
  /-- Each side is a cut of exactly the reported value. -/
  sides : ∀ S ∈ o.1, g.IsCut S ∧ g.cutValue S = o.2

/-- A run's output reports a minimum cut of `g`: the sides
partition the vertices, and each side is a minimum cut. -/
structure IsMinCutOutput (g : MultiGraph α) (o : Finset (Finset α) × ℕ) : Prop where
  /-- The sides partition the vertices. -/
  partition : g.IsCutPartition o.1
  /-- Each side is a minimum cut. -/
  sides : ∀ S ∈ o.1, g.IsMinCut S

lemma minCutValue_le {g : MultiGraph α} {S : Finset α} (h : g.IsCut S) :
    g.minCutValue ≤ g.cutValue S :=
  Nat.sInf_le ⟨S, h, rfl⟩

omit [DecidableEq α] in
/-- Any graph with at least two vertices has a cut (a singleton). -/
lemma exists_isCut (g : MultiGraph α) (h2 : 2 ≤ g.verts.card) :
    ∃ S : Finset α, g.IsCut S := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Finset.one_lt_card_iff.mp (show 1 < g.verts.card by omega)
  refine ⟨{a}, Finset.singleton_subset_iff.mpr ha, Finset.singleton_nonempty a, b, hb, ?_⟩
  simp [hab.symm]

/-- The minimum cut value is achieved by some cut. -/
lemma exists_minCut (g : MultiGraph α) (h2 : 2 ≤ g.verts.card) :
    ∃ S : Finset α, g.IsCut S ∧ g.cutValue S = g.minCutValue := by
  obtain ⟨S, hS⟩ := exists_isCut g h2
  have hne : {c : ℕ | ∃ S : Finset α, g.IsCut S ∧ g.cutValue S = c}.Nonempty :=
    ⟨g.cutValue S, S, hS, rfl⟩
  exact Nat.sInf_mem hne

lemma cutValue_le_length (g : MultiGraph α) (S : Finset α) :
    g.cutValue S ≤ g.edges.length :=
  List.countP_le_length

/-- The minimum cut is at most the total edge count. -/
lemma minCutValue_le_length (g : MultiGraph α) (h2 : 2 ≤ g.verts.card) :
    g.minCutValue ≤ g.edges.length := by
  obtain ⟨S, hS⟩ := exists_isCut g h2
  exact le_trans (minCutValue_le hS) (cutValue_le_length g S)

/-! ### Degrees and the handshake bound

The key quantitative fact behind Karger's analysis: every vertex
degree is at least the minimum-cut value (its singleton is a cut), so
`n * minCut ≤ Σ deg = 2 * m`. Note `degree` is the incidence degree
(`v ∈ e` for the unordered edge `e`), which is why the handshake
identity below reads `2 * m` and not `m`. -/

/-- The degree of `v`: the number of incident edges, with multiplicity. -/
def degree (g : MultiGraph α) (v : α) : ℕ :=
  g.edges.countP fun e => decide (v ∈ e)

/-- In a loopless graph, the cut of a singleton is the degree. -/
lemma cutValue_singleton (g : MultiGraph α) (hwf : g.WF) (v : α) :
    g.cutValue {v} = g.degree v := by
  unfold cutValue degree
  refine List.countP_congr fun e he => ?_
  have hnd := hwf.loopless e he
  clear he
  revert hnd
  induction e with
  | _ a b =>
    intro hnd
    rw [Sym2.mk_isDiag_iff] at hnd
    simp only [crossing_mk, Finset.mem_singleton, Sym2.mem_iff]
    grind

/-- Each edge contributes exactly `2` to the sum of degrees: it has two
distinct endpoints, both vertices. -/
private lemma sum_incident_eq_two {V : Finset α} {e : Sym2 α}
    (hmem : ∀ v ∈ e, v ∈ V) (hnd : ¬ e.IsDiag) :
    (∑ v ∈ V, if v ∈ e then 1 else 0) = 2 := by
  revert hmem hnd
  induction e with
  | _ a b =>
    intro hmem hnd
    rw [Sym2.mk_isDiag_iff] at hnd
    have ha : a ∈ V := hmem a (Sym2.mem_mk_left a b)
    have hb : b ∈ V := hmem b (Sym2.mem_mk_right a b)
    have hfilter : {v ∈ V | v ∈ s(a, b)} = ({a, b} : Finset α) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Sym2.mem_iff]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro (rfl | rfl) <;> simp [ha, hb]
    simp only [Finset.sum_boole, Nat.cast_id]
    rw [hfilter, Finset.card_insert_of_notMem (by simp [hnd]),
      Finset.card_singleton]

private lemma sum_degree_aux (V : Finset α) (l : List (Sym2 α))
    (hl : ∀ e ∈ l, (∀ v ∈ e, v ∈ V) ∧ ¬ e.IsDiag) :
    (∑ v ∈ V, l.countP fun e => decide (v ∈ e)) = 2 * l.length := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have he := hl e (by simp)
    have hl' : ∀ e' ∈ l, (∀ v ∈ e', v ∈ V) ∧ ¬ e'.IsDiag :=
      fun e' he' => hl e' (by simp [he'])
    simp only [List.countP_cons, decide_eq_true_eq]
    rw [Finset.sum_add_distrib, ih hl', sum_incident_eq_two he.1 he.2,
      List.length_cons]
    omega

/-- Handshake identity: degrees sum to twice the edge count. -/
lemma sum_degree (g : MultiGraph α) (hwf : g.WF) :
    ∑ v ∈ g.verts, g.degree v = 2 * g.edges.length :=
  sum_degree_aux g.verts g.edges fun e he =>
    ⟨hwf.incidence e he, hwf.loopless e he⟩

/-- Every degree bounds the minimum cut from above. -/
lemma minCutValue_le_degree (g : MultiGraph α) (hwf : g.WF)
    (h2 : 2 ≤ g.verts.card) {v : α} (hv : v ∈ g.verts) :
    g.minCutValue ≤ g.degree v := by
  rw [← cutValue_singleton g hwf v]
  refine minCutValue_le ⟨Finset.singleton_subset_iff.mpr hv,
    Finset.singleton_nonempty v, ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Finset.one_lt_card_iff.mp (show 1 < g.verts.card by omega)
  by_cases hav : a = v
  · subst hav
    exact ⟨b, hb, by simp [hab.symm]⟩
  · exact ⟨a, ha, by simp [hav]⟩

/-- The Karger counting bound: `n * minCut ≤ 2 * m`. -/
lemma card_mul_minCutValue_le (g : MultiGraph α) (hwf : g.WF)
    (h2 : 2 ≤ g.verts.card) :
    g.verts.card * g.minCutValue ≤ 2 * g.edges.length := by
  calc g.verts.card * g.minCutValue
      = ∑ _v ∈ g.verts, g.minCutValue := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ v ∈ g.verts, g.degree v :=
        Finset.sum_le_sum fun v hv => minCutValue_le_degree g hwf h2 hv
    _ = 2 * g.edges.length := sum_degree g hwf

/-! ### Transport of cut values along an endpoint relabelling -/

/-- If membership after relabelling agrees pointwise with membership
before, relabelling every edge and dropping the resulting loops
preserves the crossing count: crossing edges are never dropped (a loop
cannot cross), and dropped edges never cross. The engine behind every
contraction lemma below. -/
private lemma countP_crossing_map_filter {g : MultiGraph α} (hwf : g.WF)
    (f : α → α) {S' S : Finset α}
    (hpt : ∀ x ∈ g.verts, (f x ∈ S' ↔ x ∈ S)) :
    ((g.edges.map (Sym2.map f)).filter fun e => !e.IsDiag).countP
      (fun e => decide (Crossing S' e)) = g.cutValue S := by
  unfold cutValue
  rw [List.countP_filter, List.countP_map]
  refine List.countP_congr fun e he => ?_
  have hnd := hwf.loopless e he
  have hmem := hwf.incidence e he
  clear he
  revert hnd hmem
  induction e with
  | _ a b =>
    intro hnd hmem
    rw [Sym2.mk_isDiag_iff] at hnd
    have h1 := hpt a (hmem a (Sym2.mem_mk_left a b))
    have h2 := hpt b (hmem b (Sym2.mem_mk_right a b))
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq,
      Sym2.map_mk, crossing_mk, Bool.not_eq_true', decide_eq_false_iff_not,
      Sym2.mk_isDiag_iff]
    grind

/-! ### Two-vertex graphs

When two vertices remain, every edge crosses every cut, so the edge
count is exactly the minimum-cut value. -/

/-- In a well-formed graph on two vertices, every cut consists of all
the edges. -/
lemma cutValue_of_card_two {g : MultiGraph α} (hwf : g.WF)
    (hcard : g.verts.card = 2) {S : Finset α} (hS : g.IsCut S) :
    g.cutValue S = g.edges.length := by
  unfold cutValue
  rw [List.countP_eq_length]
  intro e he
  have hmem := hwf.incidence e he
  have hnd := hwf.loopless e he
  clear he
  revert hmem hnd
  induction e with
  | _ a b =>
    intro hmem hnd
    rw [Sym2.mk_isDiag_iff] at hnd
    have h1 : a ∈ g.verts := hmem a (Sym2.mem_mk_left a b)
    have h2 : b ∈ g.verts := hmem b (Sym2.mem_mk_right a b)
    obtain ⟨x, y, hxy, hV⟩ := Finset.card_eq_two.mp hcard
    obtain ⟨s, hsS⟩ := hS.nonempty
    obtain ⟨w, hwV, hwS⟩ := hS.proper
    have hsV := hS.subset hsS
    rw [hV] at h1 h2 hsV hwV
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 hsV hwV
    simp only [decide_eq_true_eq, crossing_mk]
    grind

/-- On two vertices the edge count is the minimum-cut value. -/
lemma length_eq_minCutValue_of_card_two {g : MultiGraph α} (hwf : g.WF)
    (hcard : g.verts.card = 2) :
    g.edges.length = g.minCutValue := by
  obtain ⟨S, hS, hval⟩ := exists_minCut g (le_of_eq hcard.symm)
  rw [← hval, cutValue_of_card_two hwf hcard hS]

/-- A cut value only depends on which vertices lie in the cut set.
(Kept as the general weight-invariance principle of the cut tier;
Benczúr–Karger sparsification is the intended next client.) -/
lemma cutValue_congr_of_verts {g : MultiGraph α} (hwf : g.WF) {S T : Finset α}
    (h : ∀ x ∈ g.verts, (x ∈ S ↔ x ∈ T)) : g.cutValue S = g.cutValue T := by
  unfold cutValue
  refine List.countP_congr fun e he => ?_
  have hmem := hwf.incidence e he
  clear he
  revert hmem
  induction e with
  | _ a b =>
    intro hmem
    have h1 := h a (hmem a (Sym2.mem_mk_left a b))
    have h2 := h b (hmem b (Sym2.mem_mk_right a b))
    simp only [crossing_mk]
    grind

/-! ### Generic endpoint-merge (rename) contraction

Every representative-style contraction has the same shape: the two
endpoints of the contracted edge leave the vertex set, a single merged
vertex `w` enters, every edge is redirected through the merge, and the
loops this creates (the parallel copies of the contracted edge) are
dropped. The models differ only in how `w` is chosen: the smaller
endpoint under a linear order, the endpoint of smaller label under an
upfront enumeration, or a brand-new vertex.

The entire cut theory needs exactly one hypothesis about that
choice: `w` collides with no untouched vertex,
`w ∉ g.verts.filter (· ∉ e)`, since `w` may well be one of the endpoints.
Everything else (cut lifting, cut survival, preservation of the
minimum-cut value along a non-crossing contraction) is proved here
once, and each model instantiates it by discharging the freshness
obligation, which is precisely where each model pays its price. -/

section Rename

variable {β : Type} [DecidableEq β]

/-- Redirect under the merge of the endpoints of `e` into `w`: both
endpoints become `w`, everything else is unchanged. -/
def redirectTo (e : Sym2 β) (w : β) (x : β) : β :=
  if x ∈ e then w else x

/-- Contract the edge `e` into the vertex `w`: the endpoints leave,
`w` enters, every edge is redirected through `redirectTo e w` and the
resulting loops are dropped; parallel edges are kept. -/
def contractEdgeTo (g : MultiGraph β) (e : Sym2 β) (w : β) : MultiGraph β where
  verts := insert w (g.verts.filter (· ∉ e))
  edges := (g.edges.map (Sym2.map (redirectTo e w))).filter fun e' => !e'.IsDiag

@[simp] lemma verts_contractEdgeTo (g : MultiGraph β) (e : Sym2 β) (w : β) :
    (g.contractEdgeTo e w).verts = insert w (g.verts.filter (· ∉ e)) := rfl

@[simp] lemma edges_contractEdgeTo (g : MultiGraph β) (e : Sym2 β) (w : β) :
    (g.contractEdgeTo e w).edges =
      (g.edges.map (Sym2.map (redirectTo e w))).filter fun e' => !e'.IsDiag := rfl

/-- Merging removes exactly one vertex: two leave, `w` enters fresh. -/
lemma card_verts_contractEdgeTo {g : MultiGraph β} {e : Sym2 β} {w : β}
    (hfresh : w ∉ g.verts.filter (· ∉ e))
    (hmem : ∀ x ∈ e, x ∈ g.verts) (hnd : ¬ e.IsDiag) :
    (g.contractEdgeTo e w).verts.card + 1 = g.verts.card := by
  rw [verts_contractEdgeTo, Finset.card_insert_of_notMem hfresh]
  clear hfresh
  revert hmem hnd
  induction e with
  | _ a b =>
    intro hmem hnd
    rw [Sym2.mk_isDiag_iff] at hnd
    have ha := hmem a (Sym2.mem_mk_left a b)
    have hb := hmem b (Sym2.mem_mk_right a b)
    have hfil : g.verts.filter (· ∉ s(a, b)) = g.verts \ {a, b} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton, Sym2.mem_iff]
    have hsub : ({a, b} : Finset β) ⊆ g.verts :=
      Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
    have h2le : 2 ≤ g.verts.card := by
      calc 2 = ({a, b} : Finset β).card := (Finset.card_pair hnd).symm
        _ ≤ g.verts.card := Finset.card_le_card hsub
    rw [hfil, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
      Finset.card_pair hnd]
    omega

/-- Rename contraction preserves well-formedness, with no hypothesis on
`w` needed. -/
theorem WF.contractEdgeTo {g : MultiGraph β} (hwf : g.WF)
    {e : Sym2 β} {w : β} : (g.contractEdgeTo e w).WF := by
  constructor
  · intro e' he' x hx
    simp only [edges_contractEdgeTo, List.mem_filter, List.mem_map] at he'
    obtain ⟨⟨e₀, he₀, rfl⟩, -⟩ := he'
    obtain ⟨x₀, hx₀, rfl⟩ := Sym2.mem_map.mp hx
    have hxv := hwf.incidence e₀ he₀ x₀ hx₀
    rw [verts_contractEdgeTo]
    unfold redirectTo
    split_ifs with hxe
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hxv, hxe⟩)
  · intro e' he'
    simp only [edges_contractEdgeTo, List.mem_filter] at he'
    simpa using he'.2

/-- Rename contraction never increases the edge count. -/
lemma length_edges_contractEdgeTo_le (g : MultiGraph β) (e : Sym2 β) (w : β) :
    (g.contractEdgeTo e w).edges.length ≤ g.edges.length :=
  le_trans (List.length_filter_le _ _) (le_of_eq (List.length_map ..))

/-- Cut-value transport along one rename contraction: if membership in
`S'` after redirection agrees pointwise with membership in `S`, the
two cuts have the same value. -/
lemma cutValue_contractEdgeTo_of_pointwise {g : MultiGraph β} (hwf : g.WF)
    {e : Sym2 β} {w : β} {S' S : Finset β}
    (hpt : ∀ x ∈ g.verts, (redirectTo e w x ∈ S' ↔ x ∈ S)) :
    (g.contractEdgeTo e w).cutValue S' = g.cutValue S :=
  countP_crossing_map_filter hwf _ hpt

/-- Cut lifting (soundness): every cut of the contracted graph
comes from a cut of `g` with the same value. Hence rename
contraction can only increase the minimum-cut value. No hypothesis on
`w` needed. -/
lemma exists_isCut_lift_contractEdgeTo {g : MultiGraph β} (hwf : g.WF)
    {e : Sym2 β} {w : β} (hmem : ∀ x ∈ e, x ∈ g.verts)
    {S' : Finset β} (h : (g.contractEdgeTo e w).IsCut S') :
    ∃ S, g.IsCut S ∧ g.cutValue S = (g.contractEdgeTo e w).cutValue S' := by
  revert hmem
  induction e with
  | _ a b =>
    intro hmem
    have ha := hmem a (Sym2.mem_mk_left a b)
    refine ⟨g.verts.filter (redirectTo s(a, b) w · ∈ S'),
      ⟨Finset.filter_subset _ _, ?_, ?_⟩, ?_⟩
    · obtain ⟨Y, hY⟩ := h.nonempty
      have hYv := h.subset hY
      rw [verts_contractEdgeTo] at hYv
      rcases Finset.mem_insert.mp hYv with rfl | hYf
      · refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
        simpa [redirectTo, Sym2.mem_mk_left] using hY
      · obtain ⟨hYv', hYe⟩ := Finset.mem_filter.mp hYf
        refine ⟨Y, Finset.mem_filter.mpr ⟨hYv', ?_⟩⟩
        simpa [redirectTo, hYe] using hY
    · obtain ⟨W, hW, hWS⟩ := h.proper
      rw [verts_contractEdgeTo] at hW
      rcases Finset.mem_insert.mp hW with rfl | hWf
      · refine ⟨a, ha, fun hc => ?_⟩
        have := (Finset.mem_filter.mp hc).2
        rw [redirectTo, if_pos (Sym2.mem_mk_left a b)] at this
        exact hWS this
      · obtain ⟨hWv, hWe⟩ := Finset.mem_filter.mp hWf
        refine ⟨W, hWv, fun hc => ?_⟩
        have := (Finset.mem_filter.mp hc).2
        rw [redirectTo, if_neg hWe] at this
        exact hWS this
    · exact (cutValue_contractEdgeTo_of_pointwise hwf fun x hx => by
        simp [Finset.mem_filter, hx]).symm

/-- Cut survival: contracting an edge that does not cross a cut
`S` into a fresh-enough `w` keeps a merge-image of `S` a cut of the
same value. -/
lemma exists_isCut_contractEdgeTo_of_notCrossing {g : MultiGraph β}
    (hwf : g.WF) {e : Sym2 β} {w : β}
    (hfresh : w ∉ g.verts.filter (· ∉ e))
    (hmem : ∀ x ∈ e, x ∈ g.verts) (hnd : ¬ e.IsDiag)
    {S : Finset β} (hS : g.IsCut S) (hnc : ¬ Crossing S e) :
    ∃ S', (g.contractEdgeTo e w).IsCut S' ∧
      (g.contractEdgeTo e w).cutValue S' = g.cutValue S := by
  revert hmem hnd hnc hfresh
  induction e with
  | _ a b =>
    intro hfresh hmem hnd hnc
    rw [Sym2.mk_isDiag_iff] at hnd
    have ha := hmem a (Sym2.mem_mk_left a b)
    have hb := hmem b (Sym2.mem_mk_right a b)
    have hiff : a ∈ S ↔ b ∈ S := by simpa using hnc
    by_cases hain : a ∈ S
    · -- both endpoints inside: the merged vertex joins the cut
      refine ⟨insert w (S.filter (· ∉ s(a, b))),
        ⟨?_, ⟨_, Finset.mem_insert_self ..⟩, ?_⟩, ?_⟩
      · rw [verts_contractEdgeTo]
        exact Finset.insert_subset_insert _
          (Finset.filter_subset_filter _ hS.subset)
      · obtain ⟨W, hWv, hWS⟩ := hS.proper
        have hWe : W ∉ s(a, b) := by
          rw [Sym2.mem_iff]
          push Not
          exact ⟨fun hc => hWS (hc ▸ hain), fun hc => hWS (hc ▸ hiff.mp hain)⟩
        refine ⟨W, ?_, ?_⟩
        · rw [verts_contractEdgeTo]
          exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hWv, hWe⟩)
        · intro hc
          rcases Finset.mem_insert.mp hc with hcU | hcf
          · exact hfresh (hcU ▸ Finset.mem_filter.mpr ⟨hWv, hWe⟩)
          · exact hWS (Finset.mem_filter.mp hcf).1
      · refine cutValue_contractEdgeTo_of_pointwise hwf fun x hx => ?_
        by_cases hxe : x ∈ s(a, b)
        · simp only [redirectTo, if_pos hxe]
          constructor
          · intro _
            rcases Sym2.mem_iff.mp hxe with rfl | rfl
            · exact hain
            · exact hiff.mp hain
          · intro _
            exact Finset.mem_insert_self ..
        · simp only [redirectTo, if_neg hxe]
          rw [Finset.mem_insert]
          constructor
          · rintro (rfl | hxf)
            · exact absurd (Finset.mem_filter.mpr ⟨hx, hxe⟩) hfresh
            · exact (Finset.mem_filter.mp hxf).1
          · intro hxS
            exact Or.inr (Finset.mem_filter.mpr ⟨hxS, hxe⟩)
    · -- neither endpoint inside: the cut survives verbatim
      have hbin : b ∉ S := fun hc => hain (hiff.mpr hc)
      have hwnot : w ∉ S := by
        intro hc
        by_cases hwe : w ∈ s(a, b)
        · rcases Sym2.mem_iff.mp hwe with rfl | rfl
          · exact hain hc
          · exact hbin hc
        · exact hfresh (Finset.mem_filter.mpr ⟨hS.subset hc, hwe⟩)
      refine ⟨S, ⟨?_, hS.nonempty, ?_⟩, ?_⟩
      · intro Y hY
        rw [verts_contractEdgeTo]
        refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hS.subset hY, ?_⟩)
        rw [Sym2.mem_iff]
        push Not
        exact ⟨fun hc => hain (hc ▸ hY), fun hc => hbin (hc ▸ hY)⟩
      · exact ⟨w, by rw [verts_contractEdgeTo]; exact Finset.mem_insert_self ..,
          hwnot⟩
      · refine cutValue_contractEdgeTo_of_pointwise hwf fun x hx => ?_
        by_cases hxe : x ∈ s(a, b)
        · simp only [redirectTo, if_pos hxe]
          constructor
          · intro hc
            exact absurd hc hwnot
          · intro hc
            rcases Sym2.mem_iff.mp hxe with rfl | rfl
            · exact absurd hc hain
            · exact absurd hc hbin
        · simp only [redirectTo, if_neg hxe]

/-- Rename contraction never decreases the minimum-cut value. -/
lemma minCutValue_le_contractEdgeTo {g : MultiGraph β} (hwf : g.WF)
    {e : Sym2 β} {w : β} (hfresh : w ∉ g.verts.filter (· ∉ e))
    (hmem : ∀ x ∈ e, x ∈ g.verts) (hnd : ¬ e.IsDiag) (h3 : 3 ≤ g.verts.card) :
    g.minCutValue ≤ (g.contractEdgeTo e w).minCutValue := by
  have h2' : 2 ≤ (g.contractEdgeTo e w).verts.card := by
    have := card_verts_contractEdgeTo hfresh hmem hnd
    omega
  obtain ⟨S', hS', hval⟩ := exists_minCut _ h2'
  obtain ⟨S, hScut, hval2⟩ := exists_isCut_lift_contractEdgeTo hwf hmem hS'
  rw [← hval, ← hval2]
  exact minCutValue_le hScut

/-- Contracting an edge that avoids a fixed minimum cut into a
fresh-enough `w` preserves the minimum-cut value exactly, the
per-step fact of every rename-model Karger analysis. -/
lemma minCutValue_contractEdgeTo_of_notCrossing {g : MultiGraph β}
    (hwf : g.WF) {e : Sym2 β} {w : β}
    (hfresh : w ∉ g.verts.filter (· ∉ e))
    (hmem : ∀ x ∈ e, x ∈ g.verts) (hnd : ¬ e.IsDiag) (h3 : 3 ≤ g.verts.card)
    {S : Finset β} (hS : g.IsCut S)
    (hmin : g.cutValue S = g.minCutValue) (hnc : ¬ Crossing S e) :
    (g.contractEdgeTo e w).minCutValue = g.minCutValue := by
  obtain ⟨S', hcut', hval'⟩ :=
    exists_isCut_contractEdgeTo_of_notCrossing hwf hfresh hmem hnd hS hnc
  refine le_antisymm ?_ (minCutValue_le_contractEdgeTo hwf hfresh hmem hnd h3)
  calc (g.contractEdgeTo e w).minCutValue
      ≤ (g.contractEdgeTo e w).cutValue S' := minCutValue_le hcut'
    _ = g.cutValue S := hval'
    _ = g.minCutValue := hmin

end Rename

end MultiGraph

end AlgoLib
