/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.Circuit
import GraphLib.Walk.Path

/-!
# General cycles

General cycles admit a loop of length one. An undirected length-two cycle is valid precisely
when its two reconstructed bundled edges are distinct; a directed length-two cycle uses two
distinct actual arcs.
-/

namespace GraphLib

variable {α β γ δ : Type*}

/-- A nonempty closed general walk with a vertex-simple interior and no repeated actual edge. -/
def Cycle (α β : Type*) := {w : Walk α β //
  0 < w.length ∧ w.closed ∧ w.dropTail.vertices.Nodup ∧ w.edges.Nodup}

/-- A nonempty closed directed walk with a vertex-simple interior and no repeated actual arc. -/
def DiCycle (α β : Type*) := {w : Walk α β //
  0 < w.length ∧ w.closed ∧ w.dropTail.vertices.Nodup ∧ w.arcs.Nodup}

namespace Cycle

abbrev walk (c : Cycle α β) := c.val
abbrev vertices (c : Cycle α β) := c.val.vertices
abbrev tags (c : Cycle α β) := c.val.tags
abbrev edges (c : Cycle α β) := c.val.edges
abbrev arcs (c : Cycle α β) := c.val.arcs
abbrev head (c : Cycle α β) := c.val.head
abbrev tail (c : Cycle α β) := c.val.tail
abbrev length (c : Cycle α β) := c.val.length

theorem length_pos (c : Cycle α β) : 0 < c.length := c.property.1
theorem closed (c : Cycle α β) : c.val.closed := c.property.2.1
theorem interior_nodup (c : Cycle α β) : c.val.dropTail.vertices.Nodup := c.property.2.2.1
theorem edges_nodup (c : Cycle α β) : c.edges.Nodup := c.property.2.2.2

@[ext] theorem ext {c d : Cycle α β} (h : c.val = d.val) : c = d := Subtype.ext h

/-- The vertex-simple interior obtained by dropping the repeated closing vertex. -/
def interior (c : Cycle α β) : Path α β := ⟨c.val.dropTail, c.interior_nodup⟩

/-- Relabel the vertices of a general cycle. -/
def relabelVertices (c : Cycle α β) (f : α ≃ γ) : Cycle γ β := by
  refine ⟨c.val.mapVertices f, ?_⟩
  refine ⟨by simpa using c.length_pos, by simpa [Walk.closed] using congrArg f c.closed,
    ?_, ?_⟩
  · rw [Walk.dropTail_mapVertices, Walk.vertices_mapVertices]
    exact c.interior_nodup.map f.injective
  · rw [Walk.edges_mapVertices]
    apply c.edges_nodup.map
    intro e d h
    apply Edge.ext
    · exact congrArg (fun x : Edge γ β => x.tag) h
    · exact Sym2.map.injective f.injective
        (congrArg (fun x : Edge γ β => x.endpoints) h)

/-- Relabel the tags of a general cycle. -/
def relabelTags (c : Cycle α β) (g : β ≃ δ) : Cycle α δ := by
  refine ⟨c.val.mapTags g, ?_⟩
  refine ⟨by simpa using c.length_pos, by simpa [Walk.closed] using c.closed, ?_, ?_⟩
  · simpa [Walk.dropTail_mapTags] using c.interior_nodup
  · rw [Walk.edges_mapTags]
    apply c.edges_nodup.map
    intro e d h
    apply Edge.ext
    · exact g.injective (congrArg (fun x : Edge α δ => x.tag) h)
    · exact congrArg (fun x : Edge α δ => x.endpoints) h

@[simp] theorem val_relabelVertices (c : Cycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).val = c.val.mapVertices f := rfl

@[simp] theorem val_relabelTags (c : Cycle α β) (g : β ≃ δ) :
    (c.relabelTags g).val = c.val.mapTags g := rfl

@[simp] theorem head_relabelVertices (c : Cycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).head = f c.head := Walk.head_mapVertices c.val f

@[simp] theorem tail_relabelVertices (c : Cycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).tail = f c.tail := Walk.tail_mapVertices c.val f

@[simp] theorem length_relabelVertices (c : Cycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).length = c.length := Walk.length_mapVertices c.val f

@[simp] theorem vertices_relabelVertices (c : Cycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).vertices = c.vertices.map f := Walk.vertices_mapVertices c.val f

@[simp] theorem tags_relabelVertices (c : Cycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).tags = c.tags := Walk.tags_mapVertices c.val f

@[simp] theorem edges_relabelVertices (c : Cycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).edges =
      c.edges.map (fun e => Edge.mk e.tag (Sym2.map f e.endpoints)) :=
  Walk.edges_mapVertices c.val f

@[simp] theorem arcs_relabelVertices (c : Cycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).arcs =
      c.arcs.map (fun a => Arc.mk a.tag (f a.source, f a.target)) :=
  Walk.arcs_mapVertices c.val f

@[simp] theorem head_relabelTags (c : Cycle α β) (g : β ≃ δ) :
    (c.relabelTags g).head = c.head := Walk.head_mapTags c.val g

@[simp] theorem tail_relabelTags (c : Cycle α β) (g : β ≃ δ) :
    (c.relabelTags g).tail = c.tail := Walk.tail_mapTags c.val g

@[simp] theorem length_relabelTags (c : Cycle α β) (g : β ≃ δ) :
    (c.relabelTags g).length = c.length := Walk.length_mapTags c.val g

@[simp] theorem vertices_relabelTags (c : Cycle α β) (g : β ≃ δ) :
    (c.relabelTags g).vertices = c.vertices := Walk.vertices_mapTags c.val g

@[simp] theorem tags_relabelTags (c : Cycle α β) (g : β ≃ δ) :
    (c.relabelTags g).tags = c.tags.map g := Walk.tags_mapTags c.val g

@[simp] theorem edges_relabelTags (c : Cycle α β) (g : β ≃ δ) :
    (c.relabelTags g).edges =
      c.edges.map (fun e => Edge.mk (g e.tag) e.endpoints) :=
  Walk.edges_mapTags c.val g

@[simp] theorem arcs_relabelTags (c : Cycle α β) (g : β ≃ δ) :
    (c.relabelTags g).arcs =
      c.arcs.map (fun a => Arc.mk (g a.tag) a.endpoints) :=
  Walk.arcs_mapTags c.val g

@[simp] theorem relabelVertices_id (c : Cycle α β) :
    c.relabelVertices (Equiv.refl α) = c := by
  apply Cycle.ext
  exact Walk.mapVertices_id c.val

@[simp] theorem relabelVertices_comp {η : Type*} (c : Cycle α β)
    (f : α ≃ γ) (g : γ ≃ η) :
    (c.relabelVertices f).relabelVertices g = c.relabelVertices (f.trans g) := by
  apply Cycle.ext
  simpa only [val_relabelVertices] using Walk.mapVertices_comp c.val f g

@[simp] theorem relabelVertices_inverse (c : Cycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).relabelVertices f.symm = c := by simp

@[simp] theorem relabelTags_id (c : Cycle α β) :
    c.relabelTags (Equiv.refl β) = c := by
  apply Cycle.ext
  exact Walk.mapTags_id c.val

@[simp] theorem relabelTags_comp {η : Type*} (c : Cycle α β)
    (f : β ≃ δ) (g : δ ≃ η) :
    (c.relabelTags f).relabelTags g = c.relabelTags (f.trans g) := by
  apply Cycle.ext
  simpa only [val_relabelTags] using Walk.mapTags_comp c.val f g

@[simp] theorem relabelTags_inverse (c : Cycle α β) (g : β ≃ δ) :
    (c.relabelTags g).relabelTags g.symm = c := by simp

/-- Forget the vertex-simplicity condition and retain the circuit. -/
def toCircuit (c : Cycle α β) : Circuit α β :=
  ⟨⟨c.val, c.edges_nodup⟩, c.length_pos, c.closed⟩

instance : Coe (Cycle α β) (Circuit α β) := ⟨toCircuit⟩

/-- Reverse an undirected cycle. -/
def reverse (c : Cycle α β) : Cycle α β := by
  refine ⟨c.val.reverse, by
    refine ⟨by simpa using c.length_pos, by simpa [Walk.closed, eq_comm] using c.closed, ?_, ?_⟩
    · have hclosed : c.val.toVertexSeq.closed := (Walk.toVertexSeq_closed c.val).2 c.closed
      have hinterior : c.val.toVertexSeq.dropTail.nodup := by
        rw [← Walk.toVertexSeq_dropTail, Walk.toVertexSeq_nodup]
        exact c.interior_nodup
      have hrev := VertexSeq.nodup_reverse_dropTail_of_closed c.val.toVertexSeq
        hclosed hinterior
      have hwalk : c.val.reverse.dropTail.toVertexSeq.nodup := by simpa using hrev
      exact (Walk.toVertexSeq_nodup c.val.reverse.dropTail).1 hwalk
    · simpa using (List.nodup_reverse.mpr c.edges_nodup)⟩

@[simp] theorem val_reverse (c : Cycle α β) : c.reverse.val = c.val.reverse := rfl
@[simp] theorem reverse_reverse (c : Cycle α β) : c.reverse.reverse = c := by
  apply Subtype.ext
  exact Walk.reverse_reverse c.val

end Cycle

namespace DiCycle

abbrev walk (c : DiCycle α β) := c.val
abbrev vertices (c : DiCycle α β) := c.val.vertices
abbrev tags (c : DiCycle α β) := c.val.tags
abbrev edges (c : DiCycle α β) := c.val.edges
abbrev arcs (c : DiCycle α β) := c.val.arcs
abbrev head (c : DiCycle α β) := c.val.head
abbrev tail (c : DiCycle α β) := c.val.tail
abbrev length (c : DiCycle α β) := c.val.length

theorem length_pos (c : DiCycle α β) : 0 < c.length := c.property.1
theorem closed (c : DiCycle α β) : c.val.closed := c.property.2.1
theorem interior_nodup (c : DiCycle α β) : c.val.dropTail.vertices.Nodup := c.property.2.2.1
theorem arcs_nodup (c : DiCycle α β) : c.arcs.Nodup := c.property.2.2.2

@[ext] theorem ext {c d : DiCycle α β} (h : c.val = d.val) : c = d := Subtype.ext h

/-- The vertex-simple interior obtained by dropping the repeated closing vertex. -/
def interior (c : DiCycle α β) : Path α β := ⟨c.val.dropTail, c.interior_nodup⟩

/-- Relabel the vertices of a directed general cycle. -/
def relabelVertices (c : DiCycle α β) (f : α ≃ γ) : DiCycle γ β := by
  refine ⟨c.val.mapVertices f, ?_⟩
  refine ⟨by simpa using c.length_pos, by simpa [Walk.closed] using congrArg f c.closed,
    ?_, ?_⟩
  · rw [Walk.dropTail_mapVertices, Walk.vertices_mapVertices]
    exact c.interior_nodup.map f.injective
  · rw [Walk.arcs_mapVertices]
    apply c.arcs_nodup.map
    intro a b h
    apply Arc.ext
    · exact congrArg (fun x : Arc γ β => x.tag) h
    · have hend := congrArg (fun x : Arc γ β => x.endpoints) h
      apply Prod.ext
      · exact f.injective (congrArg Prod.fst hend)
      · exact f.injective (congrArg Prod.snd hend)

/-- Relabel the tags of a directed general cycle. -/
def relabelTags (c : DiCycle α β) (g : β ≃ δ) : DiCycle α δ := by
  refine ⟨c.val.mapTags g, ?_⟩
  refine ⟨by simpa using c.length_pos, by simpa [Walk.closed] using c.closed, ?_, ?_⟩
  · simpa [Walk.dropTail_mapTags] using c.interior_nodup
  · rw [Walk.arcs_mapTags]
    apply c.arcs_nodup.map
    intro a b h
    apply Arc.ext
    · exact g.injective (congrArg (fun x : Arc α δ => x.tag) h)
    · exact congrArg (fun x : Arc α δ => x.endpoints) h

@[simp] theorem val_relabelVertices (c : DiCycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).val = c.val.mapVertices f := rfl

@[simp] theorem val_relabelTags (c : DiCycle α β) (g : β ≃ δ) :
    (c.relabelTags g).val = c.val.mapTags g := rfl

@[simp] theorem head_relabelVertices (c : DiCycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).head = f c.head := Walk.head_mapVertices c.val f

@[simp] theorem tail_relabelVertices (c : DiCycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).tail = f c.tail := Walk.tail_mapVertices c.val f

@[simp] theorem length_relabelVertices (c : DiCycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).length = c.length := Walk.length_mapVertices c.val f

@[simp] theorem vertices_relabelVertices (c : DiCycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).vertices = c.vertices.map f := Walk.vertices_mapVertices c.val f

@[simp] theorem tags_relabelVertices (c : DiCycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).tags = c.tags := Walk.tags_mapVertices c.val f

@[simp] theorem edges_relabelVertices (c : DiCycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).edges =
      c.edges.map (fun e => Edge.mk e.tag (Sym2.map f e.endpoints)) :=
  Walk.edges_mapVertices c.val f

@[simp] theorem arcs_relabelVertices (c : DiCycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).arcs =
      c.arcs.map (fun a => Arc.mk a.tag (f a.source, f a.target)) :=
  Walk.arcs_mapVertices c.val f

@[simp] theorem head_relabelTags (c : DiCycle α β) (g : β ≃ δ) :
    (c.relabelTags g).head = c.head := Walk.head_mapTags c.val g

@[simp] theorem tail_relabelTags (c : DiCycle α β) (g : β ≃ δ) :
    (c.relabelTags g).tail = c.tail := Walk.tail_mapTags c.val g

@[simp] theorem length_relabelTags (c : DiCycle α β) (g : β ≃ δ) :
    (c.relabelTags g).length = c.length := Walk.length_mapTags c.val g

@[simp] theorem vertices_relabelTags (c : DiCycle α β) (g : β ≃ δ) :
    (c.relabelTags g).vertices = c.vertices := Walk.vertices_mapTags c.val g

@[simp] theorem tags_relabelTags (c : DiCycle α β) (g : β ≃ δ) :
    (c.relabelTags g).tags = c.tags.map g := Walk.tags_mapTags c.val g

@[simp] theorem edges_relabelTags (c : DiCycle α β) (g : β ≃ δ) :
    (c.relabelTags g).edges =
      c.edges.map (fun e => Edge.mk (g e.tag) e.endpoints) :=
  Walk.edges_mapTags c.val g

@[simp] theorem arcs_relabelTags (c : DiCycle α β) (g : β ≃ δ) :
    (c.relabelTags g).arcs =
      c.arcs.map (fun a => Arc.mk (g a.tag) a.endpoints) :=
  Walk.arcs_mapTags c.val g

@[simp] theorem relabelVertices_id (c : DiCycle α β) :
    c.relabelVertices (Equiv.refl α) = c := by
  apply DiCycle.ext
  exact Walk.mapVertices_id c.val

@[simp] theorem relabelVertices_comp {η : Type*} (c : DiCycle α β)
    (f : α ≃ γ) (g : γ ≃ η) :
    (c.relabelVertices f).relabelVertices g = c.relabelVertices (f.trans g) := by
  apply DiCycle.ext
  simpa only [val_relabelVertices] using Walk.mapVertices_comp c.val f g

@[simp] theorem relabelVertices_inverse (c : DiCycle α β) (f : α ≃ γ) :
    (c.relabelVertices f).relabelVertices f.symm = c := by simp

@[simp] theorem relabelTags_id (c : DiCycle α β) :
    c.relabelTags (Equiv.refl β) = c := by
  apply DiCycle.ext
  exact Walk.mapTags_id c.val

@[simp] theorem relabelTags_comp {η : Type*} (c : DiCycle α β)
    (f : β ≃ δ) (g : δ ≃ η) :
    (c.relabelTags f).relabelTags g = c.relabelTags (f.trans g) := by
  apply DiCycle.ext
  simpa only [val_relabelTags] using Walk.mapTags_comp c.val f g

@[simp] theorem relabelTags_inverse (c : DiCycle α β) (g : β ≃ δ) :
    (c.relabelTags g).relabelTags g.symm = c := by simp

/-- Forget the vertex-simplicity condition and retain the directed circuit. -/
def toCircuit (c : DiCycle α β) : DiCircuit α β :=
  ⟨⟨c.val, c.arcs_nodup⟩, c.length_pos, c.closed⟩

instance : Coe (DiCycle α β) (DiCircuit α β) := ⟨toCircuit⟩

/-- Reverse a directed cycle as raw data. Realization moves to the reversed digraph. -/
def reverse (c : DiCycle α β) : DiCycle α β := by
  refine ⟨c.val.reverse, by
    refine ⟨by simpa using c.length_pos, by simpa [Walk.closed, eq_comm] using c.closed, ?_, ?_⟩
    · have hclosed : c.val.toVertexSeq.closed := (Walk.toVertexSeq_closed c.val).2 c.closed
      have hinterior : c.val.toVertexSeq.dropTail.nodup := by
        rw [← Walk.toVertexSeq_dropTail, Walk.toVertexSeq_nodup]
        exact c.interior_nodup
      have hrev := VertexSeq.nodup_reverse_dropTail_of_closed c.val.toVertexSeq
        hclosed hinterior
      have hwalk : c.val.reverse.dropTail.toVertexSeq.nodup := by simpa using hrev
      exact (Walk.toVertexSeq_nodup c.val.reverse.dropTail).1 hwalk
    · exact (DiTrail.reverse (⟨c.val, c.arcs_nodup⟩ : DiTrail α β)).property⟩

@[simp] theorem val_reverse (c : DiCycle α β) : c.reverse.val = c.val.reverse := rfl
@[simp] theorem reverse_reverse (c : DiCycle α β) : c.reverse.reverse = c := by
  apply Subtype.ext
  exact Walk.reverse_reverse c.val

end DiCycle

end GraphLib
