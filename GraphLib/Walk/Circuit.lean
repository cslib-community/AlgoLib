/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.Trail

/-! # General circuits -/

namespace GraphLib

variable {α β : Type*}

/-- A nonempty closed undirected trail. -/
def Circuit (α β : Type*) := {t : Trail α β // 0 < t.length ∧ t.closed}

/-- A nonempty closed directed trail. -/
def DiCircuit (α β : Type*) := {t : DiTrail α β // 0 < t.length ∧ t.closed}

namespace Circuit

instance : Coe (Circuit α β) (Trail α β) := ⟨Subtype.val⟩

abbrev trail (c : Circuit α β) := c.val
abbrev walk (c : Circuit α β) := c.val.val
abbrev vertices (c : Circuit α β) := c.val.vertices
abbrev tags (c : Circuit α β) := c.val.tags
abbrev edges (c : Circuit α β) := c.val.edges
abbrev arcs (c : Circuit α β) := c.val.arcs
abbrev head (c : Circuit α β) := c.val.head
abbrev tail (c : Circuit α β) := c.val.tail
abbrev length (c : Circuit α β) := c.val.length

theorem length_pos (c : Circuit α β) : 0 < c.length := c.property.1
theorem closed (c : Circuit α β) : c.val.closed := c.property.2

@[ext] theorem ext {c d : Circuit α β} (h : c.val = d.val) : c = d := Subtype.ext h

/-- Reverse an undirected circuit. -/
def reverse (c : Circuit α β) : Circuit α β :=
  ⟨c.val.reverse, by
    exact ⟨by simpa using c.property.1,
      by simpa [Walk.closed, eq_comm] using c.property.2⟩⟩

@[simp] theorem val_reverse (c : Circuit α β) : c.reverse.val = c.val.reverse := rfl
@[simp] theorem reverse_reverse (c : Circuit α β) : c.reverse.reverse = c := by
  apply Subtype.ext
  exact Trail.reverse_reverse c.val

end Circuit

namespace DiCircuit

instance : Coe (DiCircuit α β) (DiTrail α β) := ⟨Subtype.val⟩

abbrev trail (c : DiCircuit α β) := c.val
abbrev walk (c : DiCircuit α β) := c.val.val
abbrev vertices (c : DiCircuit α β) := c.val.vertices
abbrev tags (c : DiCircuit α β) := c.val.tags
abbrev edges (c : DiCircuit α β) := c.val.edges
abbrev arcs (c : DiCircuit α β) := c.val.arcs
abbrev head (c : DiCircuit α β) := c.val.head
abbrev tail (c : DiCircuit α β) := c.val.tail
abbrev length (c : DiCircuit α β) := c.val.length

theorem length_pos (c : DiCircuit α β) : 0 < c.length := c.property.1
theorem closed (c : DiCircuit α β) : c.val.closed := c.property.2

@[ext] theorem ext {c d : DiCircuit α β} (h : c.val = d.val) : c = d := Subtype.ext h

/-- Reverse a directed circuit as raw data. Realization moves to the reversed digraph. -/
def reverse (c : DiCircuit α β) : DiCircuit α β :=
  ⟨c.val.reverse, by
    exact ⟨by simpa using c.property.1,
      by simpa [Walk.closed, eq_comm] using c.property.2⟩⟩

@[simp] theorem val_reverse (c : DiCircuit α β) : c.reverse.val = c.val.reverse := rfl
@[simp] theorem reverse_reverse (c : DiCircuit α β) : c.reverse.reverse = c := by
  apply Subtype.ext
  exact DiTrail.reverse_reverse c.val

end DiCircuit

end GraphLib
