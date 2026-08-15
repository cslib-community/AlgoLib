/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import GraphLib.Graph.Degree

/-!
# Degree sums and average degree

This file proves the undirected handshaking identities for simple and general graphs, including
parallel edges and loops, and the directed out-degree and in-degree sums. Average degree is the
rational degree sum divided by the number of vertices and therefore requires a finite nonempty
vertex set.
-/

namespace GraphLib

open scoped GraphLib BigOperators Finset

variable {α β ε : Type*}

private theorem sum_incidence_and_loops_eq_twice
    (vertices : Finset α) (edges : Finset ε) (ends : ε → Sym2 α)
    (hends : ∀ e ∈ edges, ∀ v ∈ ends e, v ∈ vertices) :
    (∑ v ∈ vertices, Set.ncard {e | e ∈ (edges : Set ε) ∧ v ∈ ends e}) +
      (∑ v ∈ vertices, Set.ncard {e | e ∈ (edges : Set ε) ∧ ends e = s(v, v)}) =
        2 * edges.card := by
  classical
  have hedge : ∀ e ∈ edges,
      (∑ v ∈ vertices, if v ∈ ends e then 1 else 0) +
        (∑ v ∈ vertices, if ends e = s(v, v) then 1 else 0) = 2 := by
    intro e he
    generalize hz : ends e = z at *
    induction z using Sym2.ind with
    | h u v =>
      have hu : u ∈ vertices := hends e he u
        (hz.symm ▸ Sym2.mem_iff.mpr (Or.inl rfl))
      have hv : v ∈ vertices := hends e he v
        (hz.symm ▸ Sym2.mem_iff.mpr (Or.inr rfl))
      by_cases huv : u = v
      · subst v
        simp [hu]
      · rw [Finset.sum_boole, Finset.sum_boole]
        have hinc : {x ∈ vertices | x ∈ s(u, v)} = {u, v} := by
          ext x
          simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · exact fun hx => hx.2
          · intro hx
            rcases hx with rfl | rfl
            · exact ⟨hu, Or.inl rfl⟩
            · exact ⟨hv, Or.inr rfl⟩
        have hloop : {x ∈ vertices | s(u, v) = s(x, x)} = ∅ := by
          ext x
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
          rintro ⟨_, hx⟩
          rcases Sym2.eq_iff.mp hx with h | h
          · exact huv (h.1.trans h.2.symm)
          · exact huv (h.1.trans h.2.symm)
        rw [hinc, hloop]
        simp [huv]
  have hinc (v : α) :
      Set.ncard {e | e ∈ (edges : Set ε) ∧ v ∈ ends e} =
        ∑ e ∈ edges, if v ∈ ends e then 1 else 0 := by
    have hset : {e | e ∈ (edges : Set ε) ∧ v ∈ ends e} =
        (edges.filter fun e => v ∈ ends e : Set ε) := by
      ext e
      simp
    rw [hset, Set.ncard_coe_finset]
    exact (Finset.sum_boole (fun e => v ∈ ends e) edges).symm
  have hloop (v : α) :
      Set.ncard {e | e ∈ (edges : Set ε) ∧ ends e = s(v, v)} =
        ∑ e ∈ edges, if ends e = s(v, v) then 1 else 0 := by
    have hset : {e | e ∈ (edges : Set ε) ∧ ends e = s(v, v)} =
        (edges.filter fun e => ends e = s(v, v) : Set ε) := by
      ext e
      simp
    rw [hset, Set.ncard_coe_finset]
    exact (Finset.sum_boole (fun e => ends e = s(v, v)) edges).symm
  calc
    (∑ v ∈ vertices, Set.ncard {e | e ∈ (edges : Set ε) ∧ v ∈ ends e}) +
        (∑ v ∈ vertices, Set.ncard {e | e ∈ (edges : Set ε) ∧ ends e = s(v, v)}) =
        (∑ v ∈ vertices, ∑ e ∈ edges, if v ∈ ends e then 1 else 0) +
          (∑ v ∈ vertices, ∑ e ∈ edges, if ends e = s(v, v) then 1 else 0) := by
            simp_rw [hinc, hloop]
    _ = ∑ e ∈ edges,
        ((∑ v ∈ vertices, if v ∈ ends e then 1 else 0) +
          (∑ v ∈ vertices, if ends e = s(v, v) then 1 else 0)) := by
            rw [Finset.sum_comm]
            simp_rw [Finset.sum_comm (s := vertices) (t := edges)]
            rw [← Finset.sum_add_distrib]
    _ = ∑ _e ∈ edges, 2 := Finset.sum_congr rfl hedge
    _ = 2 * edges.card := by simp [Nat.mul_comm]

/-! ## Undirected degree sums -/

/-- The sum of degrees of a finite general graph is twice its number of actual bundled edges.
Parallel edges are counted separately and every loop contributes two. -/
theorem Graph.sum_degrees_eq_twice_card_edges (G : Graph α β) [Finite V(G)] [Finite E(G)] :
    ∑ v ∈ G.vertexFinset, G.degree v = 2 * G.edgeFinset.card := by
  classical
  calc
    (∑ v ∈ G.vertexFinset, G.degree v) =
        (∑ v ∈ G.vertexFinset,
          Set.ncard {e | e ∈ (G.edgeFinset : Set (Edge α β)) ∧ v ∈ e.endpoints}) +
          (∑ v ∈ G.vertexFinset,
            Set.ncard {e | e ∈ (G.edgeFinset : Set (Edge α β)) ∧
              e.endpoints = s(v, v)}) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      rw [← G.card_incidenceFinset_add_card_loopFinset_eq_degree]
      have hinc : (G.incidenceFinset v : Set (Edge α β)) =
          {e | e ∈ (G.edgeFinset : Set (Edge α β)) ∧ v ∈ e.endpoints} := by
        ext e
        simp [Graph.Inc]
      have hloop : (G.loopFinset v : Set (Edge α β)) =
          {e | e ∈ (G.edgeFinset : Set (Edge α β)) ∧ e.endpoints = s(v, v)} := by
        ext e
        simp [Graph.IsLink]
      rw [← hinc, ← hloop, Set.ncard_coe_finset, Set.ncard_coe_finset]
    _ = 2 * G.edgeFinset.card :=
      sum_incidence_and_loops_eq_twice G.vertexFinset G.edgeFinset Edge.endpoints
        (fun e he v hv => G.mem_vertexFinset.mpr
          (G.endpoints_mem e (G.mem_edgeFinset.mp he) v hv))

/-- The sum of degrees of a finite simple graph is twice its number of edges. -/
theorem SimpleGraph.sum_degrees_eq_twice_card_edges (G : SimpleGraph α) [Finite V(G)] :
    ∑ v ∈ G.vertexFinset, G.degree v = 2 * G.edgeFinset.card := by
  classical
  calc
    (∑ v ∈ G.vertexFinset, G.degree v) =
        (∑ v ∈ G.vertexFinset,
          Set.ncard {e | e ∈ (G.edgeFinset : Set (Sym2 α)) ∧ v ∈ e}) +
          (∑ v ∈ G.vertexFinset,
            Set.ncard {e | e ∈ (G.edgeFinset : Set (Sym2 α)) ∧ e = s(v, v)}) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      rw [← G.card_incidenceFinset_add_card_loopFinset_eq_degree]
      have hinc : (G.incidenceFinset v : Set (Sym2 α)) =
          {e | e ∈ (G.edgeFinset : Set (Sym2 α)) ∧ v ∈ e} := by
        ext e
        simp [SimpleGraph.Inc]
      have hloop : (G.loopFinset v : Set (Sym2 α)) =
          {e | e ∈ (G.edgeFinset : Set (Sym2 α)) ∧ e = s(v, v)} := by
        ext e
        change e ∈ G.loopFinset v ↔ e ∈ G.edgeFinset ∧ e = s(v, v)
        rw [G.mem_loopFinset, G.mem_edgeFinset]
        rfl
      rw [← hinc, ← hloop, Set.ncard_coe_finset, Set.ncard_coe_finset]
    _ = 2 * G.edgeFinset.card :=
      sum_incidence_and_loops_eq_twice G.vertexFinset G.edgeFinset id
        (fun e he v hv => G.mem_vertexFinset.mpr
          (G.endpoints_mem e (G.mem_edgeFinset.mp he) v hv))

/-! ## Directed degree sums -/

private theorem card_eq_sum_source_fibers
    (vertices : Finset α) (edges : Finset ε) (source : ε → α)
    (hsource : ∀ e ∈ edges, source e ∈ vertices) :
    edges.card =
      ∑ v ∈ vertices, Set.ncard {e | e ∈ (edges : Set ε) ∧ source e = v} := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise hsource]
  apply Finset.sum_congr rfl
  intro v hv
  have hset : {e | e ∈ (edges : Set ε) ∧ source e = v} =
      (edges.filter fun e => source e = v : Set ε) := by
    ext e
    simp
  rw [hset, Set.ncard_coe_finset]

/-- The sum of out-degrees is the number of actual arcs in a finite general directed graph. -/
theorem DiGraph.sum_outDegrees_eq_card_edges (G : DiGraph α β) [Finite V(G)] [Finite E(G)] :
    ∑ v ∈ G.vertexFinset, G.outDegree v = G.edgeFinset.card := by
  classical
  calc
    (∑ v ∈ G.vertexFinset, G.outDegree v) =
        ∑ v ∈ G.vertexFinset,
          Set.ncard {a | a ∈ (G.edgeFinset : Set (Arc α β)) ∧ a.source = v} := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← G.card_outIncidenceFinset_eq_outDegree]
      have hset : (G.outIncidenceFinset v : Set (Arc α β)) =
          {a | a ∈ (G.edgeFinset : Set (Arc α β)) ∧ a.source = v} := by
        ext a
        simp
      rw [← hset, Set.ncard_coe_finset]
    _ = G.edgeFinset.card :=
      (card_eq_sum_source_fibers G.vertexFinset G.edgeFinset Arc.source
        (fun a ha => G.mem_vertexFinset.mpr (G.source_mem a (G.mem_edgeFinset.mp ha)))).symm

/-- The sum of in-degrees is the number of actual arcs in a finite general directed graph. -/
theorem DiGraph.sum_inDegrees_eq_card_edges (G : DiGraph α β) [Finite V(G)] [Finite E(G)] :
    ∑ v ∈ G.vertexFinset, G.inDegree v = G.edgeFinset.card := by
  classical
  calc
    (∑ v ∈ G.vertexFinset, G.inDegree v) =
        ∑ v ∈ G.vertexFinset,
          Set.ncard {a | a ∈ (G.edgeFinset : Set (Arc α β)) ∧ a.target = v} := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← G.card_inIncidenceFinset_eq_inDegree]
      have hset : (G.inIncidenceFinset v : Set (Arc α β)) =
          {a | a ∈ (G.edgeFinset : Set (Arc α β)) ∧ a.target = v} := by
        ext a
        simp
      rw [← hset, Set.ncard_coe_finset]
    _ = G.edgeFinset.card :=
      (card_eq_sum_source_fibers G.vertexFinset G.edgeFinset Arc.target
        (fun a ha => G.mem_vertexFinset.mpr (G.target_mem a (G.mem_edgeFinset.mp ha)))).symm

theorem DiGraph.sum_outDegrees_eq_sum_inDegrees
    (G : DiGraph α β) [Finite V(G)] [Finite E(G)] :
    (∑ v ∈ G.vertexFinset, G.outDegree v) = ∑ v ∈ G.vertexFinset, G.inDegree v := by
  rw [G.sum_outDegrees_eq_card_edges, G.sum_inDegrees_eq_card_edges]

/-- The sum of out-degrees is the number of arcs in a finite simple directed graph. -/
theorem SimpleDiGraph.sum_outDegrees_eq_card_edges (G : SimpleDiGraph α) [Finite V(G)] :
    ∑ v ∈ G.vertexFinset, G.outDegree v = G.edgeFinset.card := by
  classical
  calc
    (∑ v ∈ G.vertexFinset, G.outDegree v) =
        ∑ v ∈ G.vertexFinset,
          Set.ncard {a | a ∈ (G.edgeFinset : Set (α × α)) ∧ a.1 = v} := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← G.card_outIncidenceFinset_eq_outDegree]
      have hset : (G.outIncidenceFinset v : Set (α × α)) =
          {a | a ∈ (G.edgeFinset : Set (α × α)) ∧ a.1 = v} := by
        ext a
        simp
      rw [← hset, Set.ncard_coe_finset]
    _ = G.edgeFinset.card :=
      (card_eq_sum_source_fibers G.vertexFinset G.edgeFinset Prod.fst
        (fun a ha => G.mem_vertexFinset.mpr (G.source_mem a (G.mem_edgeFinset.mp ha)))).symm

/-- The sum of in-degrees is the number of arcs in a finite simple directed graph. -/
theorem SimpleDiGraph.sum_inDegrees_eq_card_edges (G : SimpleDiGraph α) [Finite V(G)] :
    ∑ v ∈ G.vertexFinset, G.inDegree v = G.edgeFinset.card := by
  classical
  calc
    (∑ v ∈ G.vertexFinset, G.inDegree v) =
        ∑ v ∈ G.vertexFinset,
          Set.ncard {a | a ∈ (G.edgeFinset : Set (α × α)) ∧ a.2 = v} := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← G.card_inIncidenceFinset_eq_inDegree]
      have hset : (G.inIncidenceFinset v : Set (α × α)) =
          {a | a ∈ (G.edgeFinset : Set (α × α)) ∧ a.2 = v} := by
        ext a
        simp
      rw [← hset, Set.ncard_coe_finset]
    _ = G.edgeFinset.card :=
      (card_eq_sum_source_fibers G.vertexFinset G.edgeFinset Prod.snd
        (fun a ha => G.mem_vertexFinset.mpr (G.target_mem a (G.mem_edgeFinset.mp ha)))).symm

theorem SimpleDiGraph.sum_outDegrees_eq_sum_inDegrees
    (G : SimpleDiGraph α) [Finite V(G)] :
    (∑ v ∈ G.vertexFinset, G.outDegree v) = ∑ v ∈ G.vertexFinset, G.inDegree v := by
  rw [G.sum_outDegrees_eq_card_edges, G.sum_inDegrees_eq_card_edges]

/-! ## Rational average degree -/

/-- The rational average degree of a finite nonempty general graph. -/
noncomputable def Graph.averageDegree (G : Graph α β) [Finite V(G)] [Finite E(G)]
    [Nonempty V(G)] : ℚ :=
  (∑ v ∈ G.vertexFinset, (G.degree v : ℚ)) / G.vertexFinset.card

/-- The rational average degree of a finite nonempty simple graph. -/
noncomputable def SimpleGraph.averageDegree (G : SimpleGraph α) [Finite V(G)]
    [Nonempty V(G)] : ℚ :=
  (∑ v ∈ G.vertexFinset, (G.degree v : ℚ)) / G.vertexFinset.card

/-- The average degree is twice the number of actual edges divided by the number of vertices. -/
theorem Graph.averageDegree_eq_two_mul_card_edgeFinset_div_card_vertexFinset
    (G : Graph α β) [Finite V(G)] [Finite E(G)] [Nonempty V(G)] :
    G.averageDegree = (2 * G.edgeFinset.card : ℚ) / G.vertexFinset.card := by
  rw [averageDegree, ← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
  norm_num

/-- The average degree is twice the number of edges divided by the number of vertices. -/
theorem SimpleGraph.averageDegree_eq_two_mul_card_edgeFinset_div_card_vertexFinset
    (G : SimpleGraph α) [Finite V(G)] [Nonempty V(G)] :
    G.averageDegree = (2 * G.edgeFinset.card : ℚ) / G.vertexFinset.card := by
  rw [averageDegree, ← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
  norm_num

end GraphLib
