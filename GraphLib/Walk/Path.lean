/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.Trail

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
