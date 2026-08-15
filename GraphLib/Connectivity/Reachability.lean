/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.InDiGraph
import GraphLib.Walk.InGraph
import GraphLib.Walk.InSimpleDiGraph.Path
import GraphLib.Walk.InSimpleGraph.Path

/-!
# Reachability

Reachability is existence of a realized path between two ambient vertex values. Reflexivity is
therefore restricted to vertices of the graph. Equivalent walk and reflexive-transitive
adjacency-closure views are provided for proofs and later algorithm correctness statements.
-/

namespace GraphLib

open scoped GraphLib

variable {α β γ δ : Type*}

namespace SimpleGraph

/-- Two vertices are reachable in a simple graph when they are the endpoints of a realized
simple path. -/
def Reachable (G : SimpleGraph α) (u v : α) : Prop :=
  ∃ p : SimplePath α, G.IsSimplePathIn p ∧ p.head = u ∧ p.tail = v

theorem reachable_iff_exists_simplePath (G : SimpleGraph α) (u v : α) :
    G.Reachable u v ↔
      ∃ p : SimplePath α, G.IsSimplePathIn p ∧ p.head = u ∧ p.tail = v :=
  Iff.rfl

/-- A simple-graph reachability witness may equivalently be any realized simple walk. -/
theorem reachable_iff_exists_walk (G : SimpleGraph α) (u v : α) :
    G.Reachable u v ↔
      ∃ w : SimpleWalk α, G.IsSimpleWalkIn w ∧ w.head = u ∧ w.tail = v := by
  constructor
  · rintro ⟨p, hp, hhead, htail⟩
    exact ⟨p.val, hp, hhead, htail⟩
  · rintro ⟨w, hw, hhead, htail⟩
    classical
    exact ⟨SimplePath.cycleErase w, IsSimpleWalkIn.cycleErase G hw,
      by simpa using hhead, by simpa using htail⟩

namespace Reachable

/-- Every graph vertex is reachable from itself. -/
@[refl] theorem refl {G : SimpleGraph α} {u : α} (hu : u ∈ V(G)) : G.Reachable u u :=
  ⟨SimplePath.singleton u, IsSimplePathIn.singleton G hu, rfl, rfl⟩

/-- The initial endpoint of a reachability witness belongs to the graph. -/
theorem left_mem {G : SimpleGraph α} {u v : α} (h : G.Reachable u v) : u ∈ V(G) := by
  obtain ⟨p, hp, rfl, _⟩ := h
  exact IsSimpleWalkIn.head_mem G hp

/-- The final endpoint of a reachability witness belongs to the graph. -/
theorem right_mem {G : SimpleGraph α} {u v : α} (h : G.Reachable u v) : v ∈ V(G) := by
  obtain ⟨p, hp, _, rfl⟩ := h
  exact IsSimpleWalkIn.tail_mem G hp

/-- Reachability is transitive. -/
@[trans] theorem trans {G : SimpleGraph α} {u v w : α}
    (huv : G.Reachable u v) (hvw : G.Reachable v w) : G.Reachable u w := by
  rw [reachable_iff_exists_walk] at huv hvw ⊢
  obtain ⟨p, hp, hpu, hpv⟩ := huv
  obtain ⟨q, hq, hqv, hqw⟩ := hvw
  have hends : p.tail = q.head := hpv.trans hqv.symm
  exact ⟨p.glue q hends, IsSimpleWalkIn.glue G hp hq hends,
    by simpa only [SimpleWalk.head_glue] using hpu,
    by simpa only [SimpleWalk.tail_glue] using hqw⟩

/-- Undirected reachability is symmetric. -/
@[symm] theorem symm {G : SimpleGraph α} {u v : α}
    (h : G.Reachable u v) : G.Reachable v u := by
  rw [reachable_iff_exists_walk] at h ⊢
  obtain ⟨w, hw, hhead, htail⟩ := h
  exact ⟨w.reverse, IsSimpleWalkIn.reverse G hw,
    by simpa using htail, by simpa using hhead⟩

/-- Reachability is monotone when the ambient graph grows. -/
theorem mono {G H : SimpleGraph α} {u v : α}
    (h : G.Reachable u v) (hGH : G ≤ H) : H.Reachable u v := by
  obtain ⟨p, hp, hhead, htail⟩ := h
  exact ⟨p, IsSimpleWalkIn.mono H G hp hGH, hhead, htail⟩

end Reachable

/-- Adjacent vertices are reachable. -/
theorem Adj.reachable {G : SimpleGraph α} {u v : α} (h : G.Adj u v) :
    G.Reachable u v := by
  let p : SimplePath α := SimplePath.singleton u
  have hv : v ∉ p.vertices := by
    intro hv
    have hvu : v = u := by
      simpa [p, VertexSeq.mem_def, VertexSeq.toList] using hv
    exact h.ne hvu.symm
  exact ⟨p.extendTail v hv,
    IsSimplePathIn.extendTail G (IsSimplePathIn.singleton G h.left_mem) h hv,
    by simp [p], by simp⟩

private theorem isVertexSeqIn_reflTransGen {G : SimpleGraph α} {w : VertexSeq α}
    (h : G.IsVertexSeqIn w) : Relation.ReflTransGen G.Adj w.head w.tail := by
  induction h with
  | singleton => exact .refl
  | cons _ _ _ hadj ih => exact ih.tail hadj

/-- Reachability is the reflexive-transitive adjacency closure, restricted at its reflexive
base to vertices of the graph. -/
theorem reachable_iff_mem_and_reflTransGen (G : SimpleGraph α) (u v : α) :
    G.Reachable u v ↔ u ∈ V(G) ∧ Relation.ReflTransGen G.Adj u v := by
  constructor
  · intro h
    obtain ⟨w, hw, hhead, htail⟩ :=
      (G.reachable_iff_exists_walk u v).1 h
    exact ⟨h.left_mem, hhead ▸ htail ▸ isVertexSeqIn_reflTransGen hw⟩
  · rintro ⟨hu, huv⟩
    induction huv with
    | refl => exact .refl hu
    | tail _ hadj ih => exact ih.trans hadj.reachable

/-- Relabeling vertices transports simple-graph reachability. -/
theorem Reachable.relabelVertices {G : SimpleGraph α} {u v : α}
    (h : G.Reachable u v) (f : α ≃ γ) :
    (G.relabelVertices f).Reachable (f u) (f v) := by
  rw [reachable_iff_exists_walk] at h ⊢
  obtain ⟨w, hw, hhead, htail⟩ := h
  refine ⟨SimpleWalk.map f f.injective w, IsSimpleWalkIn.relabelVertices f hw, ?_, ?_⟩
  · simpa using congrArg f hhead
  · simpa using congrArg f htail

@[simp] theorem relabelVertices_reachable (G : SimpleGraph α) (f : α ≃ γ) (u v : α) :
    (G.relabelVertices f).Reachable (f u) (f v) ↔ G.Reachable u v := by
  constructor
  · intro h
    simpa using h.relabelVertices f.symm
  · exact fun h => h.relabelVertices f

end SimpleGraph

namespace SimpleDiGraph

/-- Directed reachability in a simple digraph is existence of a realized directed simple path. -/
def Reachable (G : SimpleDiGraph α) (u v : α) : Prop :=
  ∃ p : SimplePath α, G.IsSimplePathIn p ∧ p.head = u ∧ p.tail = v

theorem reachable_iff_exists_simplePath (G : SimpleDiGraph α) (u v : α) :
    G.Reachable u v ↔
      ∃ p : SimplePath α, G.IsSimplePathIn p ∧ p.head = u ∧ p.tail = v :=
  Iff.rfl

/-- Directed reachability may equivalently be witnessed by any realized simple walk. -/
theorem reachable_iff_exists_walk (G : SimpleDiGraph α) (u v : α) :
    G.Reachable u v ↔
      ∃ w : SimpleWalk α, G.IsSimpleWalkIn w ∧ w.head = u ∧ w.tail = v := by
  constructor
  · rintro ⟨p, hp, hhead, htail⟩
    exact ⟨p.val, hp, hhead, htail⟩
  · rintro ⟨w, hw, hhead, htail⟩
    classical
    exact ⟨SimplePath.cycleErase w, IsSimpleWalkIn.cycleErase G hw,
      by simpa using hhead, by simpa using htail⟩

namespace Reachable

@[refl] theorem refl {G : SimpleDiGraph α} {u : α} (hu : u ∈ V(G)) : G.Reachable u u :=
  ⟨SimplePath.singleton u, IsVertexSeqIn.singleton u hu, rfl, rfl⟩

theorem left_mem {G : SimpleDiGraph α} {u v : α} (h : G.Reachable u v) : u ∈ V(G) := by
  obtain ⟨p, hp, rfl, _⟩ := h
  exact IsSimpleWalkIn.head_mem G hp

theorem right_mem {G : SimpleDiGraph α} {u v : α} (h : G.Reachable u v) : v ∈ V(G) := by
  obtain ⟨p, hp, _, rfl⟩ := h
  exact IsSimpleWalkIn.tail_mem G hp

@[trans] theorem trans {G : SimpleDiGraph α} {u v w : α}
    (huv : G.Reachable u v) (hvw : G.Reachable v w) : G.Reachable u w := by
  rw [reachable_iff_exists_walk] at huv hvw ⊢
  obtain ⟨p, hp, hpu, hpv⟩ := huv
  obtain ⟨q, hq, hqv, hqw⟩ := hvw
  have hends : p.tail = q.head := hpv.trans hqv.symm
  exact ⟨p.glue q hends, IsSimpleWalkIn.glue G hp hq hends,
    by simpa only [SimpleWalk.head_glue] using hpu,
    by simpa only [SimpleWalk.tail_glue] using hqw⟩

theorem mono {G H : SimpleDiGraph α} {u v : α}
    (h : G.Reachable u v) (hGH : G ≤ H) : H.Reachable u v := by
  obtain ⟨p, hp, hhead, htail⟩ := h
  exact ⟨p, IsSimplePathIn.mono H G hp hGH, hhead, htail⟩

/-- Reversing a directed graph reverses the direction of reachability. -/
theorem reverse {G : SimpleDiGraph α} {u v : α}
    (h : G.Reachable u v) : G.reverse.Reachable v u := by
  obtain ⟨p, hp, hhead, htail⟩ := h
  exact ⟨p.reverse, IsSimplePathIn.reverse hp,
    by simpa using htail, by simpa using hhead⟩

theorem relabelVertices {G : SimpleDiGraph α} {u v : α}
    (h : G.Reachable u v) (f : α ≃ γ) :
    (G.relabelVertices f).Reachable (f u) (f v) := by
  rw [reachable_iff_exists_walk] at h ⊢
  obtain ⟨w, hw, hhead, htail⟩ := h
  refine ⟨SimpleWalk.map f f.injective w, IsSimpleWalkIn.relabelVertices f hw, ?_, ?_⟩
  · simpa using congrArg f hhead
  · simpa using congrArg f htail

end Reachable

theorem Adj.reachable {G : SimpleDiGraph α} {u v : α} (h : G.Adj u v) :
    G.Reachable u v := by
  let p : SimplePath α := SimplePath.singleton u
  have hv : v ∉ p.vertices := by
    intro hv
    have hvu : v = u := by
      simpa [p, VertexSeq.mem_def, VertexSeq.toList] using hv
    exact h.ne hvu.symm
  exact ⟨p.extendTail v hv,
    show G.IsSimpleWalkIn (p.extendTail v hv).val from
      IsVertexSeqIn.cons p.vertices v (IsVertexSeqIn.singleton u h.source_mem) h,
    by simp [p], by simp⟩

private theorem isVertexSeqIn_reflTransGen {G : SimpleDiGraph α} {w : VertexSeq α}
    (h : G.IsVertexSeqIn w) : Relation.ReflTransGen G.Adj w.head w.tail := by
  induction h with
  | singleton => exact .refl
  | cons _ _ _ hadj ih => exact ih.tail hadj

theorem reachable_iff_mem_and_reflTransGen (G : SimpleDiGraph α) (u v : α) :
    G.Reachable u v ↔ u ∈ V(G) ∧ Relation.ReflTransGen G.Adj u v := by
  constructor
  · intro h
    obtain ⟨w, hw, hhead, htail⟩ :=
      (G.reachable_iff_exists_walk u v).1 h
    exact ⟨h.left_mem, hhead ▸ htail ▸ isVertexSeqIn_reflTransGen hw⟩
  · rintro ⟨hu, huv⟩
    induction huv with
    | refl => exact .refl hu
    | tail _ hadj ih => exact ih.trans hadj.reachable

/-- Reachability in a reversed simple digraph is reachability in the opposite direction. -/
@[simp] theorem reverse_reachable (G : SimpleDiGraph α) (u v : α) :
    G.reverse.Reachable u v ↔ G.Reachable v u := by
  constructor
  · intro h
    simpa using h.reverse
  · exact fun h => h.reverse

@[simp] theorem relabelVertices_reachable (G : SimpleDiGraph α) (f : α ≃ γ) (u v : α) :
    (G.relabelVertices f).Reachable (f u) (f v) ↔ G.Reachable u v := by
  constructor
  · intro h
    simpa using h.relabelVertices f.symm
  · exact fun h => h.relabelVertices f

end SimpleDiGraph

namespace Graph

/-- Two vertices are reachable in a general graph when they are endpoints of a realized path
whose steps retain their actual bundled-edge identity. -/
def Reachable (G : Graph α β) (u v : α) : Prop :=
  ∃ p : Path α β, G.IsPathIn p ∧ p.head = u ∧ p.tail = v

theorem reachable_iff_exists_path (G : Graph α β) (u v : α) :
    G.Reachable u v ↔ ∃ p : Path α β, G.IsPathIn p ∧ p.head = u ∧ p.tail = v :=
  Iff.rfl

/-- General-graph reachability may equivalently be witnessed by any realized walk. -/
theorem reachable_iff_exists_walk (G : Graph α β) (u v : α) :
    G.Reachable u v ↔ ∃ w : Walk α β, G.IsWalkIn w ∧ w.head = u ∧ w.tail = v := by
  constructor
  · rintro ⟨p, hp, hhead, htail⟩
    exact ⟨p.val, hp, hhead, htail⟩
  · rintro ⟨w, hw, hhead, htail⟩
    classical
    exact ⟨w.toPath, hw.cycleErase, by simpa using hhead, by simpa using htail⟩

namespace Reachable

@[refl] theorem refl {G : Graph α β} {u : α} (hu : u ∈ V(G)) : G.Reachable u u :=
  ⟨Path.singleton u, IsWalkIn.singleton u hu, rfl, rfl⟩

theorem left_mem {G : Graph α β} {u v : α} (h : G.Reachable u v) : u ∈ V(G) := by
  obtain ⟨p, hp, rfl, _⟩ := h
  exact hp.head_mem

theorem right_mem {G : Graph α β} {u v : α} (h : G.Reachable u v) : v ∈ V(G) := by
  obtain ⟨p, hp, _, rfl⟩ := h
  exact hp.tail_mem

@[trans] theorem trans {G : Graph α β} {u v w : α}
    (huv : G.Reachable u v) (hvw : G.Reachable v w) : G.Reachable u w := by
  rw [reachable_iff_exists_walk] at huv hvw ⊢
  obtain ⟨p, hp, hpu, hpv⟩ := huv
  obtain ⟨q, hq, hqv, hqw⟩ := hvw
  have hends : p.tail = q.head := hpv.trans hqv.symm
  exact ⟨p.glue q hends, hp.glue hq hends,
    by simpa using hpu, by simpa using hqw⟩

@[symm] theorem symm {G : Graph α β} {u v : α} (h : G.Reachable u v) :
    G.Reachable v u := by
  obtain ⟨p, hp, hhead, htail⟩ := h
  exact ⟨p.reverse, hp.reverse, by simpa using htail, by simpa using hhead⟩

theorem mono {G H : Graph α β} {u v : α}
    (h : G.Reachable u v) (hGH : G ≤ H) : H.Reachable u v := by
  obtain ⟨p, hp, hhead, htail⟩ := h
  exact ⟨p, hp.isWalkIn.mono hGH, hhead, htail⟩

theorem relabelVertices {G : Graph α β} {u v : α}
    (h : G.Reachable u v) (f : α ≃ γ) :
    (G.relabelVertices f).Reachable (f u) (f v) := by
  rw [reachable_iff_exists_walk] at h ⊢
  obtain ⟨w, hw, hhead, htail⟩ := h
  exact ⟨w.mapVertices f, hw.relabelVertices f,
    by simpa using congrArg f hhead, by simpa using congrArg f htail⟩

/-- Relabeling raw tags transports general-graph reachability without changing endpoints. -/
theorem relabelTags {G : Graph α β} {u v : α}
    (h : G.Reachable u v) (g : β ≃ δ) : (G.relabelTags g).Reachable u v := by
  rw [reachable_iff_exists_walk] at h ⊢
  obtain ⟨w, hw, hhead, htail⟩ := h
  exact ⟨w.mapTags g, hw.relabelTags g, by simpa using hhead, by simpa using htail⟩

end Reachable

theorem Adj.reachable {G : Graph α β} {u v : α} (h : G.Adj u v) :
    G.Reachable u v := by
  obtain ⟨⟨t, ends⟩, he, hends⟩ := h
  change ends = s(u, v) at hends
  subst ends
  rw [reachable_iff_exists_walk]
  exact ⟨(Walk.singleton u).cons v t,
    IsWalkIn.cons _ _ _ (IsWalkIn.singleton u (G.endpoints_mem _ he u (by simp))) ⟨he, rfl⟩,
    rfl, rfl⟩

private theorem isWalkIn_reflTransGen {G : Graph α β} {w : Walk α β}
    (h : G.IsWalkIn w) : Relation.ReflTransGen G.Adj w.head w.tail := by
  induction h with
  | singleton => exact .refl
  | cons _ _ _ _ hlink ih => exact ih.tail hlink.adj

theorem reachable_iff_mem_and_reflTransGen (G : Graph α β) (u v : α) :
    G.Reachable u v ↔ u ∈ V(G) ∧ Relation.ReflTransGen G.Adj u v := by
  constructor
  · intro h
    obtain ⟨w, hw, hhead, htail⟩ := (G.reachable_iff_exists_walk u v).1 h
    exact ⟨h.left_mem, hhead ▸ htail ▸ isWalkIn_reflTransGen hw⟩
  · rintro ⟨hu, huv⟩
    induction huv with
    | refl => exact .refl hu
    | tail _ hadj ih => exact ih.trans hadj.reachable

@[simp] theorem relabelVertices_reachable (G : Graph α β) (f : α ≃ γ) (u v : α) :
    (G.relabelVertices f).Reachable (f u) (f v) ↔ G.Reachable u v := by
  constructor
  · intro h
    simpa using h.relabelVertices f.symm
  · exact fun h => h.relabelVertices f

@[simp] theorem relabelTags_reachable (G : Graph α β) (g : β ≃ δ) (u v : α) :
    (G.relabelTags g).Reachable u v ↔ G.Reachable u v := by
  constructor
  · intro h
    simpa using h.relabelTags g.symm
  · exact fun h => h.relabelTags g

end Graph

namespace DiGraph

/-- Directed reachability in a general digraph is existence of a realized path retaining actual
bundled-arc identity. -/
def Reachable (G : DiGraph α β) (u v : α) : Prop :=
  ∃ p : Path α β, G.IsPathIn p ∧ p.head = u ∧ p.tail = v

theorem reachable_iff_exists_path (G : DiGraph α β) (u v : α) :
    G.Reachable u v ↔ ∃ p : Path α β, G.IsPathIn p ∧ p.head = u ∧ p.tail = v :=
  Iff.rfl

/-- Directed reachability may equivalently be witnessed by any realized walk. -/
theorem reachable_iff_exists_walk (G : DiGraph α β) (u v : α) :
    G.Reachable u v ↔ ∃ w : Walk α β, G.IsWalkIn w ∧ w.head = u ∧ w.tail = v := by
  constructor
  · rintro ⟨p, hp, hhead, htail⟩
    exact ⟨p.val, hp, hhead, htail⟩
  · rintro ⟨w, hw, hhead, htail⟩
    classical
    exact ⟨w.toPath, hw.cycleErase, by simpa using hhead, by simpa using htail⟩

namespace Reachable

@[refl] theorem refl {G : DiGraph α β} {u : α} (hu : u ∈ V(G)) : G.Reachable u u :=
  ⟨Path.singleton u, IsWalkIn.singleton u hu, rfl, rfl⟩

theorem left_mem {G : DiGraph α β} {u v : α} (h : G.Reachable u v) : u ∈ V(G) := by
  obtain ⟨p, hp, rfl, _⟩ := h
  exact hp.head_mem

theorem right_mem {G : DiGraph α β} {u v : α} (h : G.Reachable u v) : v ∈ V(G) := by
  obtain ⟨p, hp, _, rfl⟩ := h
  exact hp.tail_mem

@[trans] theorem trans {G : DiGraph α β} {u v w : α}
    (huv : G.Reachable u v) (hvw : G.Reachable v w) : G.Reachable u w := by
  rw [reachable_iff_exists_walk] at huv hvw ⊢
  obtain ⟨p, hp, hpu, hpv⟩ := huv
  obtain ⟨q, hq, hqv, hqw⟩ := hvw
  have hends : p.tail = q.head := hpv.trans hqv.symm
  exact ⟨p.glue q hends, hp.glue hq hends,
    by simpa using hpu, by simpa using hqw⟩

theorem mono {G H : DiGraph α β} {u v : α}
    (h : G.Reachable u v) (hGH : G ≤ H) : H.Reachable u v := by
  obtain ⟨p, hp, hhead, htail⟩ := h
  exact ⟨p, hp.isWalkIn.mono hGH, hhead, htail⟩

theorem reverse {G : DiGraph α β} {u v : α}
    (h : G.Reachable u v) : G.reverse.Reachable v u := by
  obtain ⟨p, hp, hhead, htail⟩ := h
  exact ⟨p.reverse, hp.reverse, by simpa using htail, by simpa using hhead⟩

theorem relabelVertices {G : DiGraph α β} {u v : α}
    (h : G.Reachable u v) (f : α ≃ γ) :
    (G.relabelVertices f).Reachable (f u) (f v) := by
  rw [reachable_iff_exists_walk] at h ⊢
  obtain ⟨w, hw, hhead, htail⟩ := h
  exact ⟨w.mapVertices f, hw.relabelVertices f,
    by simpa using congrArg f hhead, by simpa using congrArg f htail⟩

theorem relabelTags {G : DiGraph α β} {u v : α}
    (h : G.Reachable u v) (g : β ≃ δ) : (G.relabelTags g).Reachable u v := by
  rw [reachable_iff_exists_walk] at h ⊢
  obtain ⟨w, hw, hhead, htail⟩ := h
  exact ⟨w.mapTags g, hw.relabelTags g, by simpa using hhead, by simpa using htail⟩

end Reachable

theorem Adj.reachable {G : DiGraph α β} {u v : α} (h : G.Adj u v) :
    G.Reachable u v := by
  obtain ⟨⟨t, x, y⟩, he, hs, ht⟩ := h
  change x = u at hs
  change y = v at ht
  subst x
  subst y
  rw [reachable_iff_exists_walk]
  exact ⟨(Walk.singleton u).cons v t,
    IsWalkIn.cons _ _ _ (IsWalkIn.singleton u (G.source_mem _ he)) ⟨he, rfl, rfl⟩,
    rfl, rfl⟩

private theorem isWalkIn_reflTransGen {G : DiGraph α β} {w : Walk α β}
    (h : G.IsWalkIn w) : Relation.ReflTransGen G.Adj w.head w.tail := by
  induction h with
  | singleton => exact .refl
  | cons _ _ _ _ harc ih => exact ih.tail harc.adj

theorem reachable_iff_mem_and_reflTransGen (G : DiGraph α β) (u v : α) :
    G.Reachable u v ↔ u ∈ V(G) ∧ Relation.ReflTransGen G.Adj u v := by
  constructor
  · intro h
    obtain ⟨w, hw, hhead, htail⟩ := (G.reachable_iff_exists_walk u v).1 h
    exact ⟨h.left_mem, hhead ▸ htail ▸ isWalkIn_reflTransGen hw⟩
  · rintro ⟨hu, huv⟩
    induction huv with
    | refl => exact .refl hu
    | tail _ hadj ih => exact ih.trans hadj.reachable

@[simp] theorem reverse_reachable (G : DiGraph α β) (u v : α) :
    G.reverse.Reachable u v ↔ G.Reachable v u := by
  constructor
  · intro h
    simpa using h.reverse
  · exact fun h => h.reverse

@[simp] theorem relabelVertices_reachable (G : DiGraph α β) (f : α ≃ γ) (u v : α) :
    (G.relabelVertices f).Reachable (f u) (f v) ↔ G.Reachable u v := by
  constructor
  · intro h
    simpa using h.relabelVertices f.symm
  · exact fun h => h.relabelVertices f

@[simp] theorem relabelTags_reachable (G : DiGraph α β) (g : β ≃ δ) (u v : α) :
    (G.relabelTags g).Reachable u v ↔ G.Reachable u v := by
  constructor
  · intro h
    simpa using h.relabelTags g.symm
  · exact fun h => h.relabelTags g

end DiGraph

end GraphLib
