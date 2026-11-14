/-
Copyright (c) 2026 AlgoLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import AlgoLib.Theory.Graph.Structures.Forest

/-!
# Parent trees

A `ParentTree` is a finite forest represented by a parent pointer and a natural
number level at every vertex. Roots point to themselves; every other vertex
has a parent at a strictly lower level. The representation may contain several
roots (or no vertices), so its underlying simple graph is a forest, not
necessarily a connected tree.
-/

namespace AlgoLib

/-- A finite parent-pointer forest. The fields outside `vertexSet` are irrelevant. -/
structure ParentTree (α : Type*) where
  vertexSet : Finset α
  parent : α → α
  level : α → ℕ
  incidence : ∀ v ∈ vertexSet, parent v ∈ vertexSet
  ordering : ∀ v ∈ vertexSet, 0 < level v → level (parent v) < level v
  root : ∀ v ∈ vertexSet, level v = 0 ↔ v = parent v

namespace ParentTree

variable {α : Type*}

/-- The undirected graph obtained by joining each nonroot vertex to its parent. -/
def toSimpleGraph (G : ParentTree α) : SimpleGraph α where
  vertexSet := ↑G.vertexSet
  edgeSet := {e | ∃ v ∈ G.vertexSet, v ≠ G.parent v ∧ e = s(v, G.parent v)}
  incidence' := by
    rintro e ⟨v, hv, _, rfl⟩ x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact hv
    · exact G.incidence v hv
  loopless' := by
    rintro e ⟨v, _, hne, rfl⟩
    simpa only [Sym2.mk_isDiag_iff] using hne

@[simp] theorem mem_vertexSet_toSimpleGraph (G : ParentTree α) (v : α) :
    v ∈ G.toSimpleGraph.vertexSet ↔ v ∈ G.vertexSet := Iff.rfl

theorem mem_edgeSet_toSimpleGraph (G : ParentTree α) (e : Sym2 α) :
    e ∈ G.toSimpleGraph.edgeSet ↔
      ∃ v ∈ G.vertexSet, v ≠ G.parent v ∧ e = s(v, G.parent v) := Iff.rfl

/-- Adjacent vertices are related by a parent pointer in one direction. -/
theorem adj_iff (G : ParentTree α) {u v : α} :
    G.toSimpleGraph.Adj u v ↔
      u ≠ v ∧ ((u ∈ G.vertexSet ∧ G.parent u = v) ∨
        (v ∈ G.vertexSet ∧ G.parent v = u)) := by
  constructor
  · intro h
    have hne : u ≠ v := h.ne
    obtain ⟨w, hw, _, he⟩ := (G.mem_edgeSet_toSimpleGraph _).mp h
    rcases Sym2.eq_iff.mp he with ⟨rfl, hp⟩ | ⟨hp, rfl⟩
    · exact ⟨hne, Or.inl ⟨hw, hp.symm⟩⟩
    · exact ⟨hne, Or.inr ⟨hw, hp.symm⟩⟩
  · rintro ⟨hne, ⟨hu, hp⟩ | ⟨hv, hp⟩⟩
    · exact (G.mem_edgeSet_toSimpleGraph _).mpr
        ⟨u, hu, by simpa [hp] using hne, by simp [hp]⟩
    · exact (G.mem_edgeSet_toSimpleGraph _).mpr
        ⟨v, hv, by simpa [hp] using hne.symm, by simp [hp, Sym2.eq_swap]⟩

/-- Attach new vertices as leaves to existing vertices. -/
def appendNodes [DecidableEq α] (G : ParentTree α) (newNodes : Finset α)
    (attach : α → α) (hattach : ∀ v ∈ newNodes, attach v ∈ G.vertexSet) :
    ParentTree α where
  vertexSet := G.vertexSet ∪ newNodes
  parent := fun v => if v ∈ G.vertexSet then G.parent v else attach v
  level := fun v => if v ∈ G.vertexSet then G.level v else G.level (attach v) + 1
  incidence := by
    intro v hv
    by_cases hV : v ∈ G.vertexSet
    · simp [hV, G.incidence v hV]
    · have hnew : v ∈ newNodes := (Finset.mem_union.mp hv).resolve_left hV
      simp [hV, Finset.mem_union, hattach v hnew]
  ordering := by
    intro v hv hpos
    by_cases hV : v ∈ G.vertexSet
    · simp only [hV, ↓reduceIte] at hpos ⊢
      have hp : G.parent v ∈ G.vertexSet := G.incidence v hV
      simpa [hp] using G.ordering v hV hpos
    · simp only [hV, ↓reduceIte] at hpos ⊢
      have hnew : v ∈ newNodes := (Finset.mem_union.mp hv).resolve_left hV
      have hp : attach v ∈ G.vertexSet := hattach v hnew
      simp [hp]
  root := by
    intro v hv
    by_cases hV : v ∈ G.vertexSet
    · simpa [hV] using G.root v hV
    · have hnew : v ∈ newNodes := (Finset.mem_union.mp hv).resolve_left hV
      have hp : attach v ∈ G.vertexSet := hattach v hnew
      have hne : v ≠ attach v := fun heq => hV (heq.symm ▸ hp)
      simp [hV, hne]

end ParentTree
end AlgoLib
