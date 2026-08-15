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

variable {α β : Type*}

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
