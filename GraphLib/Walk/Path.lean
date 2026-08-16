/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.Walk

/-!
# General paths

A `Path` is direction-independent combinatorial data: an alternating walk with no repeated
vertex. Realization in an undirected or directed graph is supplied separately.
-/

namespace GraphLib

variable {α β : Type*}

/-- A general alternating walk whose visited vertices have no repetitions. -/
def Path (α β : Type*) := {w : Walk α β // w.vertices.Nodup}

namespace Walk

/-- Erase cycles from a walk to obtain a path with the same final vertex. -/
def toPath [DecidableEq α] (w : Walk α β) : Path α β :=
  ⟨w.cycleErase, by
    change w.cycleErase.nodup
    rw [← Walk.toVertexSeq_nodup, Walk.toVertexSeq_cycleErase]
    exact VertexSeq.nodup_cycleErase w.toVertexSeq⟩

@[simp] theorem val_toPath [DecidableEq α] (w : Walk α β) : w.toPath.val = w.cycleErase := rfl
@[simp] theorem head_toPath [DecidableEq α] (w : Walk α β) : w.toPath.val.head = w.head := by
  rw [val_toPath, Walk.head_cycleErase]
@[simp] theorem tail_toPath [DecidableEq α] (w : Walk α β) : w.toPath.val.tail = w.tail := by
  rw [val_toPath, ← Walk.toVertexSeq_tail, Walk.toVertexSeq_cycleErase,
    VertexSeq.tail_cycleErase, Walk.toVertexSeq_tail]

end Walk

namespace Path

instance : Coe (Path α β) (Walk α β) := ⟨Subtype.val⟩

@[simp] theorem vertices_nodup (p : Path α β) : p.val.vertices.Nodup := p.property

abbrev walk (p : Path α β) := p.val
abbrev vertices (p : Path α β) := p.val.vertices
abbrev tags (p : Path α β) := p.val.tags
abbrev edges (p : Path α β) := p.val.edges
abbrev arcs (p : Path α β) := p.val.arcs
abbrev head (p : Path α β) := p.val.head
abbrev tail (p : Path α β) := p.val.tail
abbrev length (p : Path α β) := p.val.length

@[ext] theorem ext {p q : Path α β} (h : p.val = q.val) : p = q := Subtype.ext h

/-- The one-vertex path. -/
def singleton (v : α) : Path α β := ⟨Walk.singleton v, by simp⟩

@[simp] theorem val_singleton (v : α) : (singleton v : Path α β).val = .singleton v := rfl
@[simp] theorem head_singleton (v : α) : (singleton v : Path α β).head = v := rfl
@[simp] theorem tail_singleton (v : α) : (singleton v : Path α β).tail = v := rfl
@[simp] theorem length_singleton (v : α) : (singleton v : Path α β).length = 0 := rfl

/-- Drop the first vertex of a path. -/
def dropHead (p : Path α β) : Path α β :=
  ⟨p.val.dropHead, by
    change p.val.dropHead.nodup
    rw [← Walk.toVertexSeq_nodup, Walk.toVertexSeq_dropHead]
    exact VertexSeq.nodup_dropHead p.val.toVertexSeq
      ((Walk.toVertexSeq_nodup p.val).2 p.property)⟩

/-- Drop the last vertex of a path. -/
def dropTail (p : Path α β) : Path α β :=
  ⟨p.val.dropTail, by
    change p.val.dropTail.nodup
    rw [← Walk.toVertexSeq_nodup, Walk.toVertexSeq_dropTail]
    exact VertexSeq.nodup_dropTail p.val.toVertexSeq
      ((Walk.toVertexSeq_nodup p.val).2 p.property)⟩

/-- The prefix of a path ending at a visited vertex. -/
def prefixUntil [DecidableEq α] (p : Path α β) (v : α) (h : v ∈ p.val) : Path α β :=
  ⟨p.val.prefixUntil v h, by
    change (p.val.prefixUntil v h).nodup
    rw [← Walk.toVertexSeq_nodup, Walk.toVertexSeq_prefixUntil]
    exact VertexSeq.nodup_prefixUntil p.val.toVertexSeq v
      (by simpa using h) ((Walk.toVertexSeq_nodup p.val).2 p.property)⟩

/-- The suffix of a path starting at a visited vertex. -/
def suffixFrom [DecidableEq α] (p : Path α β) (v : α) (h : v ∈ p.val) : Path α β :=
  ⟨p.val.suffixFrom v h, by
    change (p.val.suffixFrom v h).nodup
    rw [← Walk.toVertexSeq_nodup, Walk.toVertexSeq_suffixFrom]
    exact VertexSeq.nodup_suffixFrom p.val.toVertexSeq v
      (by simpa using h) ((Walk.toVertexSeq_nodup p.val).2 p.property)⟩

@[simp] theorem val_dropHead (p : Path α β) : p.dropHead.val = p.val.dropHead := rfl
@[simp] theorem val_dropTail (p : Path α β) : p.dropTail.val = p.val.dropTail := rfl
@[simp] theorem val_prefixUntil [DecidableEq α] (p : Path α β) (v : α) (h : v ∈ p.val) :
    (p.prefixUntil v h).val = p.val.prefixUntil v h := rfl
@[simp] theorem val_suffixFrom [DecidableEq α] (p : Path α β) (v : α) (h : v ∈ p.val) :
    (p.suffixFrom v h).val = p.val.suffixFrom v h := rfl

/-- Append two vertex-disjoint paths using a new tagged connecting step. -/
def append (p q : Path α β) (t : β)
    (hdisj : ∀ v ∈ p.vertices, v ∈ q.vertices → False) : Path α β :=
  ⟨p.val.append q.val t, by
    rw [Walk.vertices_append, List.nodup_append]
    refine ⟨p.property, q.property, ?_⟩
    intro a ha b hb hab
    subst b
    exact hdisj a ha hb⟩

@[simp] theorem val_append (p q : Path α β) (t : β)
    (hdisj : ∀ v ∈ p.vertices, v ∈ q.vertices → False) :
    (p.append q t hdisj).val = p.val.append q.val t := rfl

/-- Glue two paths meeting at one endpoint, retaining every existing tagged step. -/
def glue (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) : Path α β :=
  ⟨p.val.glue q.val h, by
    rw [Walk.vertices_glue, List.nodup_append]
    exact ⟨p.property.sublist (List.dropLast_sublist _), q.property,
      fun v hv _ hvq heq => hdisj v hv (heq ▸ hvq)⟩⟩

@[simp] theorem val_glue (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    (p.glue q h hdisj).val = p.val.glue q.val h := rfl

@[simp] theorem head_glue (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    (p.glue q h hdisj).head = p.head := Walk.head_glue p.val q.val h

@[simp] theorem tail_glue (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    (p.glue q h hdisj).tail = q.tail := Walk.tail_glue p.val q.val h

@[simp] theorem length_glue (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    (p.glue q h hdisj).length = p.length + q.length := Walk.length_glue p.val q.val h

@[simp] theorem vertices_glue (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    (p.glue q h hdisj).vertices = p.vertices.dropLast ++ q.vertices :=
  Walk.vertices_glue p.val q.val h

@[simp] theorem tags_glue (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    (p.glue q h hdisj).tags = p.tags ++ q.tags := Walk.tags_glue p.val q.val h

@[simp] theorem edges_glue (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    (p.glue q h hdisj).edges = p.edges ++ q.edges := Walk.edges_glue p.val q.val h

@[simp] theorem arcs_glue (p q : Path α β) (h : p.tail = q.head)
    (hdisj : ∀ v ∈ p.vertices.dropLast, v ∈ q.vertices → False) :
    (p.glue q h hdisj).arcs = p.arcs ++ q.arcs := Walk.arcs_glue p.val q.val h

/-- Map path vertices through an injective function. -/
def mapVertices {γ : Type*} (p : Path α β) (f : α → γ) (hf : Function.Injective f) :
    Path γ β :=
  ⟨p.val.mapVertices f, by simpa using p.property.map hf⟩

/-- Map the raw tags of a path. Vertex distinctness is unchanged. -/
def mapTags {δ : Type*} (p : Path α β) (g : β → δ) : Path α δ :=
  ⟨p.val.mapTags g, by simpa using p.property⟩

/-- Relabel path vertices through an equivalence. -/
def relabelVertices {γ : Type*} (p : Path α β) (f : α ≃ γ) : Path γ β :=
  p.mapVertices f f.injective

/-- Relabel path tags through an equivalence. -/
def relabelTags {δ : Type*} (p : Path α β) (g : β ≃ δ) : Path α δ :=
  p.mapTags g

@[simp] theorem val_mapVertices {γ : Type*} (p : Path α β) (f : α → γ)
    (hf : Function.Injective f) : (p.mapVertices f hf).val = p.val.mapVertices f := rfl

@[simp] theorem val_mapTags {δ : Type*} (p : Path α β) (g : β → δ) :
    (p.mapTags g).val = p.val.mapTags g := rfl

@[simp] theorem val_relabelVertices {γ : Type*} (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).val = p.val.mapVertices f := rfl

@[simp] theorem val_relabelTags {δ : Type*} (p : Path α β) (g : β ≃ δ) :
    (p.relabelTags g).val = p.val.mapTags g := rfl

@[simp] theorem head_relabelVertices {γ : Type*} (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).head = f p.head := Walk.head_mapVertices p.val f

@[simp] theorem tail_relabelVertices {γ : Type*} (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).tail = f p.tail := Walk.tail_mapVertices p.val f

@[simp] theorem length_relabelVertices {γ : Type*} (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).length = p.length := Walk.length_mapVertices p.val f

@[simp] theorem vertices_relabelVertices {γ : Type*} (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).vertices = p.vertices.map f := Walk.vertices_mapVertices p.val f

@[simp] theorem tags_relabelVertices {γ : Type*} (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).tags = p.tags := Walk.tags_mapVertices p.val f

@[simp] theorem edges_relabelVertices {γ : Type*} (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).edges =
      p.edges.map (fun e => Edge.mk e.tag (Sym2.map f e.endpoints)) :=
  Walk.edges_mapVertices p.val f

@[simp] theorem arcs_relabelVertices {γ : Type*} (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).arcs =
      p.arcs.map (fun a => Arc.mk a.tag (f a.source, f a.target)) :=
  Walk.arcs_mapVertices p.val f

@[simp] theorem head_relabelTags {δ : Type*} (p : Path α β) (g : β ≃ δ) :
    (p.relabelTags g).head = p.head := Walk.head_mapTags p.val g

@[simp] theorem tail_relabelTags {δ : Type*} (p : Path α β) (g : β ≃ δ) :
    (p.relabelTags g).tail = p.tail := Walk.tail_mapTags p.val g

@[simp] theorem length_relabelTags {δ : Type*} (p : Path α β) (g : β ≃ δ) :
    (p.relabelTags g).length = p.length := Walk.length_mapTags p.val g

@[simp] theorem vertices_relabelTags {δ : Type*} (p : Path α β) (g : β ≃ δ) :
    (p.relabelTags g).vertices = p.vertices := Walk.vertices_mapTags p.val g

@[simp] theorem tags_relabelTags {δ : Type*} (p : Path α β) (g : β ≃ δ) :
    (p.relabelTags g).tags = p.tags.map g := Walk.tags_mapTags p.val g

@[simp] theorem edges_relabelTags {δ : Type*} (p : Path α β) (g : β ≃ δ) :
    (p.relabelTags g).edges =
      p.edges.map (fun e => Edge.mk (g e.tag) e.endpoints) :=
  Walk.edges_mapTags p.val g

@[simp] theorem arcs_relabelTags {δ : Type*} (p : Path α β) (g : β ≃ δ) :
    (p.relabelTags g).arcs =
      p.arcs.map (fun a => Arc.mk (g a.tag) a.endpoints) :=
  Walk.arcs_mapTags p.val g

@[simp] theorem relabelVertices_id (p : Path α β) :
    p.relabelVertices (Equiv.refl α) = p := by
  apply Path.ext
  exact Walk.mapVertices_id p.val

@[simp] theorem relabelVertices_comp {γ η : Type*} (p : Path α β)
    (f : α ≃ γ) (g : γ ≃ η) :
    (p.relabelVertices f).relabelVertices g = p.relabelVertices (f.trans g) := by
  apply Path.ext
  simpa only [val_relabelVertices] using Walk.mapVertices_comp p.val f g

@[simp] theorem relabelVertices_inverse {γ : Type*} (p : Path α β) (f : α ≃ γ) :
    (p.relabelVertices f).relabelVertices f.symm = p := by simp

@[simp] theorem relabelTags_id (p : Path α β) :
    p.relabelTags (Equiv.refl β) = p := by
  apply Path.ext
  exact Walk.mapTags_id p.val

@[simp] theorem relabelTags_comp {δ η : Type*} (p : Path α β)
    (f : β ≃ δ) (g : δ ≃ η) :
    (p.relabelTags f).relabelTags g = p.relabelTags (f.trans g) := by
  apply Path.ext
  simpa only [val_relabelTags] using Walk.mapTags_comp p.val f g

@[simp] theorem relabelTags_inverse {δ : Type*} (p : Path α β) (g : β ≃ δ) :
    (p.relabelTags g).relabelTags g.symm = p := by simp

/-- Reverse a path. -/
def reverse (p : Path α β) : Path α β :=
  ⟨p.val.reverse, by simpa using (List.nodup_reverse.mpr p.property)⟩

@[simp] theorem val_reverse (p : Path α β) : p.reverse.val = p.val.reverse := rfl
@[simp] theorem reverse_reverse (p : Path α β) : p.reverse.reverse = p := by
  apply Subtype.ext
  exact Walk.reverse_reverse p.val
@[simp] theorem head_reverse (p : Path α β) : p.reverse.head = p.tail :=
  Walk.head_reverse p.val
@[simp] theorem tail_reverse (p : Path α β) : p.reverse.tail = p.head :=
  Walk.tail_reverse p.val
@[simp] theorem length_reverse (p : Path α β) : p.reverse.length = p.length :=
  Walk.length_reverse p.val
@[simp] theorem edges_reverse (p : Path α β) : p.reverse.edges = p.edges.reverse :=
  Walk.edges_reverse p.val

/-- Every path is non-stalling. -/
theorem nonstalling (p : Path α β) : p.val.nonstalling := by
  rw [← Walk.toVertexSeq_nonstalling]
  exact VertexSeq.nonstalling_of_nodup p.val.toVertexSeq
    ((Walk.toVertexSeq_nodup p.val).2 p.property)

end Path

end GraphLib
