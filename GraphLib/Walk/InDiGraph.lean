/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Delete
import GraphLib.Graph.Reverse
import GraphLib.Walk.Cycle

/-!
# General directed walk realization

Realization checks reconstructed full `Arc` values. Reversing raw walk data transports
realization to the reversed digraph.
-/

namespace GraphLib

variable {α β γ δ : Type*}

open scoped GraphLib

namespace DiGraph

/-- A raw general walk realized in a directed graph. -/
inductive IsWalkIn (G : DiGraph α β) : Walk α β → Prop
  | singleton (v : α) (hv : v ∈ V(G)) : G.IsWalkIn (.singleton v)
  | cons (w : Walk α β) (v : α) (t : β) (hw : G.IsWalkIn w)
      (harc : G.IsArc ⟨t, (w.tail, v)⟩ w.tail v) : G.IsWalkIn (w.cons v t)

namespace IsWalkIn

@[simp] theorem singleton_iff (G : DiGraph α β) (v : α) :
    G.IsWalkIn (.singleton v) ↔ v ∈ V(G) := by
  constructor
  · intro h
    cases h
    assumption
  · exact .singleton v

@[simp] theorem cons_iff (G : DiGraph α β) (w : Walk α β) (v : α) (t : β) :
    G.IsWalkIn (w.cons v t) ↔
      G.IsWalkIn w ∧ G.IsArc ⟨t, (w.tail, v)⟩ w.tail v := by
  constructor
  · intro h
    cases h with
    | cons _ _ _ hw ha => exact ⟨hw, ha⟩
  · rintro ⟨hw, ha⟩
    exact .cons w v t hw ha

theorem head_mem {G : DiGraph α β} {w : Walk α β} (h : G.IsWalkIn w) :
    w.head ∈ V(G) := by
  induction h with
  | singleton v hv => exact hv
  | cons w v t hw ha ih => exact ih

theorem tail_mem {G : DiGraph α β} {w : Walk α β} (h : G.IsWalkIn w) :
    w.tail ∈ V(G) := by
  cases h with
  | singleton v hv => exact hv
  | cons w v t hw ha => exact ha.target_mem

theorem vertex_mem {G : DiGraph α β} {w : Walk α β} (h : G.IsWalkIn w)
    {v : α} (hv : v ∈ w.vertices) : v ∈ V(G) := by
  induction h with
  | singleton u hu =>
      simp only [Walk.vertices_singleton, List.mem_singleton] at hv
      exact hv ▸ hu
  | cons w u t hw ha ih =>
      simp only [Walk.vertices_cons, List.concat_eq_append, List.mem_append,
        List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact ih hv
      · exact ha.target_mem

theorem arc_mem {G : DiGraph α β} {w : Walk α β} (h : G.IsWalkIn w)
    {a : Arc α β} (ha : a ∈ w.arcs) : a ∈ E(G) := by
  induction h with
  | singleton v hv => simp at ha
  | cons w v t hw harc ih =>
      simp only [Walk.arcs_cons, List.concat_eq_append, List.mem_append,
        List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact ih ha
      · exact harc.edge_mem

/-- Directed realization is exactly head membership plus all reconstructed actual arcs. -/
theorem iff_arcs (G : DiGraph α β) (w : Walk α β) :
    G.IsWalkIn w ↔ w.head ∈ V(G) ∧ ∀ a ∈ w.arcs, a ∈ E(G) := by
  constructor
  · intro h
    exact ⟨h.head_mem, fun _ ha => h.arc_mem ha⟩
  · rintro ⟨hhead, harcs⟩
    induction w with
    | singleton v => exact .singleton v hhead
    | cons w v t ih =>
        have hprefix : ∀ a ∈ w.arcs, a ∈ E(G) := by
          intro a ha
          exact harcs a (by simp [Walk.arcs, List.concat_eq_append, ha])
        have hw := ih hhead hprefix
        have hlast : Arc.mk t (w.tail, v) ∈ E(G) :=
          harcs _ (by simp [Walk.arcs, List.concat_eq_append])
        exact .cons w v t hw ⟨hlast, rfl, rfl⟩

/-- Realization depends only on the ambient vertex and actual-arc sets. -/
theorem congr {G H : DiGraph α β} {w : Walk α β}
    (hV : V(G) = V(H)) (hE : E(G) = E(H)) : G.IsWalkIn w ↔ H.IsWalkIn w := by
  rw [iff_arcs G w, iff_arcs H w, hV, hE]

theorem mono {G H : DiGraph α β} {w : Walk α β} (h : G.IsWalkIn w) (hGH : G ≤ H) :
    H.IsWalkIn w := by
  rw [IsWalkIn.iff_arcs H w]
  exact ⟨hGH.vertexSet_subset h.head_mem,
    fun _ ha => hGH.edgeSet_subset (h.arc_mem ha)⟩

theorem toDiGraph_le {G : DiGraph α β} {w : Walk α β} (h : G.IsWalkIn w) :
    w.toDiGraph ≤ G :=
  ⟨fun _ hv => h.vertex_mem hv, fun _ ha => h.arc_mem ha⟩

theorem of_toDiGraph_le (G : DiGraph α β) (w : Walk α β) (h : w.toDiGraph ≤ G) :
    G.IsWalkIn w := by
  rw [IsWalkIn.iff_arcs G w]
  exact ⟨h.vertexSet_subset (by exact w.head_mem),
    fun _ ha => h.edgeSet_subset ha⟩

theorem iff_toDiGraph_le (G : DiGraph α β) (w : Walk α β) :
    G.IsWalkIn w ↔ w.toDiGraph ≤ G :=
  ⟨toDiGraph_le, IsWalkIn.of_toDiGraph_le G w⟩

/-- Directed reversal transports realization to the reversed graph. -/
theorem reverse {G : DiGraph α β} {w : Walk α β} (h : G.IsWalkIn w) :
    G.reverse.IsWalkIn w.reverse := by
  rw [IsWalkIn.iff_arcs G.reverse w.reverse]
  refine ⟨by simpa using h.tail_mem, ?_⟩
  intro a ha
  rw [Walk.arcs_reverse] at ha
  rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
  rw [G.mem_edgeSet_reverse]
  simpa using h.arc_mem (List.mem_reverse.mp hb)

theorem dropTail {G : DiGraph α β} {w : Walk α β} (h : G.IsWalkIn w) :
    G.IsWalkIn w.dropTail := by
  cases h with
  | singleton v hv => exact .singleton v hv
  | cons w v t hw harc => exact hw

theorem dropHead {G : DiGraph α β} {w : Walk α β} (h : G.IsWalkIn w) :
    G.IsWalkIn w.dropHead := by
  induction h with
  | singleton v hv => exact .singleton v hv
  | cons w v t hw harc ih =>
      cases w with
      | singleton u => exact .singleton v harc.target_mem
      | cons q u s =>
          apply DiGraph.IsWalkIn.cons (Walk.dropHead (q.cons u s)) v t ih
          simpa using harc

theorem prefixUntil [DecidableEq α] {G : DiGraph α β} {w : Walk α β}
    (h : G.IsWalkIn w) (v : α) (hv : v ∈ w) : G.IsWalkIn (w.prefixUntil v hv) := by
  rw [iff_arcs]
  exact ⟨by simpa using h.head_mem,
    fun _ ha => h.arc_mem (Walk.arcs_prefixUntil_subset w v hv ha)⟩

theorem suffixFrom [DecidableEq α] {G : DiGraph α β} {w : Walk α β}
    (h : G.IsWalkIn w) (v : α) (hv : v ∈ w) : G.IsWalkIn (w.suffixFrom v hv) := by
  rw [iff_arcs]
  exact ⟨by simpa using h.vertex_mem (show v ∈ w.vertices from hv),
    fun _ ha => h.arc_mem (Walk.arcs_suffixFrom_subset w v hv ha)⟩

theorem append {G : DiGraph α β} {p q : Walk α β} (hp : G.IsWalkIn p)
    (hq : G.IsWalkIn q) (t : β)
    (hbridge : G.IsArc ⟨t, (p.tail, q.head)⟩ p.tail q.head) :
    G.IsWalkIn (p.append q t) := by
  induction hq with
  | singleton v hv => exact .cons p v t hp hbridge
  | cons q v s hq hlast ih =>
      exact .cons (p.append q t) v s (ih hbridge) (by simpa using hlast)

theorem glue {G : DiGraph α β} {p q : Walk α β} (hp : G.IsWalkIn p)
    (hq : G.IsWalkIn q) (hends : p.tail = q.head) : G.IsWalkIn (p.glue q hends) := by
  cases hp with
  | singleton v hv => simpa [Walk.glue] using hq
  | cons p v t hp hlast =>
      apply append hp hq t
      have hvq : v = q.head := by simpa using hends
      simpa [hvq] using hlast

theorem induce_iff (G : DiGraph α β) (S : Set α) (w : Walk α β) :
    (G.induce S).IsWalkIn w ↔ G.IsWalkIn w ∧ ∀ v ∈ w.vertices, v ∈ S := by
  constructor
  · intro h
    exact ⟨h.mono (G.induce_le S), fun v hv =>
      ((G.mem_vertexSet_induce S v).1 (h.vertex_mem hv)).1⟩
  · rintro ⟨hG, hS⟩
    rw [IsWalkIn.iff_arcs (G.induce S) w]
    refine ⟨(G.mem_vertexSet_induce S w.head).2 ⟨hS _ w.head_mem, hG.head_mem⟩, ?_⟩
    intro a ha
    rw [G.mem_edgeSet_induce]
    exact ⟨hG.arc_mem ha,
      hS _ (w.toDiGraph.source_mem a ha), hS _ (w.toDiGraph.target_mem a ha)⟩

/-- Restricting actual arcs preserves exactly the walks whose reconstructed arcs survive. -/
theorem restrictEdges_iff (G : DiGraph α β) (F : Set (Arc α β)) (w : Walk α β) :
    (G.restrictEdges F).IsWalkIn w ↔ G.IsWalkIn w ∧ ∀ a ∈ w.arcs, a ∈ F := by
  simp only [iff_arcs, G.mem_vertexSet_restrictEdges, G.mem_edgeSet_restrictEdges]
  aesop

/-- Deleting actual arcs preserves exactly the walks avoiding those arcs. -/
theorem deleteEdges_iff (G : DiGraph α β) (F : Set (Arc α β)) (w : Walk α β) :
    (G.deleteEdges F).IsWalkIn w ↔ G.IsWalkIn w ∧ ∀ a ∈ w.arcs, a ∉ F := by
  simp only [iff_arcs, G.vertexSet_deleteEdges, G.mem_edgeSet_deleteEdges]
  aesop

/-- Deleting vertices preserves exactly the walks avoiding the deleted set. -/
theorem deleteVerts_iff (G : DiGraph α β) (S : Set α) (w : Walk α β) :
    (G.deleteVerts S).IsWalkIn w ↔ G.IsWalkIn w ∧ ∀ v ∈ w.vertices, v ∉ S := by
  simpa [Set.mem_compl_iff] using induce_iff G Sᶜ w

/-- Vertex relabeling transports a directed realized walk. -/
theorem relabelVertices {G : DiGraph α β} {w : Walk α β} (f : α ≃ γ)
    (h : G.IsWalkIn w) : (G.relabelVertices f).IsWalkIn (w.mapVertices f) := by
  induction h with
  | singleton v hv => exact DiGraph.IsWalkIn.singleton (f v) ⟨v, hv, rfl⟩
  | cons w v t hw harc ih =>
      apply DiGraph.IsWalkIn.cons (w.mapVertices f) (f v) t ih
      simpa [Arc.relabelVertices] using
        (G.relabelVertices_isArc f ⟨t, (w.tail, v)⟩ w.tail v).2 harc

/-- Tag relabeling transports a directed realized walk. -/
theorem relabelTags {G : DiGraph α β} {w : Walk α β} (g : β ≃ δ)
    (h : G.IsWalkIn w) : (G.relabelTags g).IsWalkIn (w.mapTags g) := by
  induction h with
  | singleton v hv => exact DiGraph.IsWalkIn.singleton v (by simpa using hv)
  | cons w v t hw harc ih =>
      apply DiGraph.IsWalkIn.cons (w.mapTags g) v (g t) ih
      simpa [Arc.relabelTags] using
        (G.relabelTags_isArc g ⟨t, (w.tail, v)⟩ w.tail v).2 harc

end IsWalkIn

def IsTrailIn (G : DiGraph α β) (t : DiTrail α β) : Prop := G.IsWalkIn t.val
def IsPathIn (G : DiGraph α β) (p : Path α β) : Prop := G.IsWalkIn p.val
def IsCircuitIn (G : DiGraph α β) (c : DiCircuit α β) : Prop := G.IsTrailIn c.val
def IsCycleIn (G : DiGraph α β) (c : DiCycle α β) : Prop := G.IsWalkIn c.val

namespace IsTrailIn
theorem isWalkIn {G : DiGraph α β} {t : DiTrail α β} (h : G.IsTrailIn t) : G.IsWalkIn t.val := h
theorem reverse {G : DiGraph α β} {t : DiTrail α β} (h : G.IsTrailIn t) :
    G.reverse.IsTrailIn t.reverse := DiGraph.IsWalkIn.reverse h
end IsTrailIn

namespace IsPathIn
theorem isWalkIn {G : DiGraph α β} {p : Path α β} (h : G.IsPathIn p) : G.IsWalkIn p.val := h
theorem reverse {G : DiGraph α β} {p : Path α β} (h : G.IsPathIn p) :
    G.reverse.IsPathIn p.reverse := DiGraph.IsWalkIn.reverse h
end IsPathIn

namespace IsCircuitIn
theorem isTrailIn {G : DiGraph α β} {c : DiCircuit α β} (h : G.IsCircuitIn c) :
    G.IsTrailIn c.val := h
theorem reverse {G : DiGraph α β} {c : DiCircuit α β} (h : G.IsCircuitIn c) :
    G.reverse.IsCircuitIn c.reverse := DiGraph.IsTrailIn.reverse h
end IsCircuitIn

namespace IsCycleIn
theorem isWalkIn {G : DiGraph α β} {c : DiCycle α β} (h : G.IsCycleIn c) : G.IsWalkIn c.val := h
theorem reverse {G : DiGraph α β} {c : DiCycle α β} (h : G.IsCycleIn c) :
    G.reverse.IsCycleIn c.reverse := DiGraph.IsWalkIn.reverse h
end IsCycleIn

end DiGraph

end GraphLib
