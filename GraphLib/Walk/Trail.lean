/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.Walk

/-!
# Trails

Undirected and directed trails must be distinct: antiparallel same-tag steps reconstruct the
same undirected edge but distinct directed arcs.
-/

namespace GraphLib

variable {α β : Type*}

/-- A general undirected walk with no repeated actual bundled edge. -/
def Trail (α β : Type*) := {w : Walk α β // w.edges.Nodup}

/-- A general directed walk with no repeated actual bundled arc. -/
def DiTrail (α β : Type*) := {w : Walk α β // w.arcs.Nodup}

namespace Trail

instance : Coe (Trail α β) (Walk α β) := ⟨Subtype.val⟩

@[simp] theorem edges_nodup (t : Trail α β) : t.val.edges.Nodup := t.property

abbrev walk (t : Trail α β) := t.val
abbrev vertices (t : Trail α β) := t.val.vertices
abbrev tags (t : Trail α β) := t.val.tags
abbrev edges (t : Trail α β) := t.val.edges
abbrev arcs (t : Trail α β) := t.val.arcs
abbrev head (t : Trail α β) := t.val.head
abbrev tail (t : Trail α β) := t.val.tail
abbrev length (t : Trail α β) := t.val.length
abbrev closed (t : Trail α β) := t.val.closed

@[ext] theorem ext {s t : Trail α β} (h : s.val = t.val) : s = t := Subtype.ext h

/-- The one-vertex undirected trail. -/
def singleton (v : α) : Trail α β := ⟨Walk.singleton v, by simp⟩

@[simp] theorem val_singleton (v : α) : (singleton v : Trail α β).val = .singleton v := rfl

/-- Drop the final step of an undirected trail. -/
def dropTail : Trail α β → Trail α β
  | ⟨.singleton v, _⟩ => singleton v
  | ⟨.cons w v tag, h⟩ => ⟨w, by
      apply List.Nodup.of_append_left
      simpa [Walk.edges, List.concat_eq_append] using h⟩

/-- Drop the initial step of an undirected trail. -/
def dropHead (t : Trail α β) : Trail α β :=
  ⟨t.val.dropHead, by
    rw [Walk.edges_dropHead]
    exact t.property.tail⟩

@[simp] theorem val_dropTail (t : Trail α β) : t.dropTail.val = t.val.dropTail := by
  rcases t with ⟨w, h⟩
  cases w <;> rfl
@[simp] theorem val_dropHead (t : Trail α β) : t.dropHead.val = t.val.dropHead := rfl

/-- Reverse an undirected trail. -/
def reverse (t : Trail α β) : Trail α β :=
  ⟨t.val.reverse, by simpa using (List.nodup_reverse.mpr t.property)⟩

@[simp] theorem val_reverse (t : Trail α β) : t.reverse.val = t.val.reverse := rfl
@[simp] theorem reverse_reverse (t : Trail α β) : t.reverse.reverse = t := by
  apply Subtype.ext
  exact Walk.reverse_reverse t.val
@[simp] theorem head_reverse (t : Trail α β) : t.reverse.head = t.tail :=
  Walk.head_reverse t.val
@[simp] theorem tail_reverse (t : Trail α β) : t.reverse.tail = t.head :=
  Walk.tail_reverse t.val
@[simp] theorem length_reverse (t : Trail α β) : t.reverse.length = t.length :=
  Walk.length_reverse t.val
@[simp] theorem edges_reverse (t : Trail α β) : t.reverse.edges = t.edges.reverse :=
  Walk.edges_reverse t.val

end Trail

namespace DiTrail

instance : Coe (DiTrail α β) (Walk α β) := ⟨Subtype.val⟩

@[simp] theorem arcs_nodup (t : DiTrail α β) : t.val.arcs.Nodup := t.property

abbrev walk (t : DiTrail α β) := t.val
abbrev vertices (t : DiTrail α β) := t.val.vertices
abbrev tags (t : DiTrail α β) := t.val.tags
abbrev edges (t : DiTrail α β) := t.val.edges
abbrev arcs (t : DiTrail α β) := t.val.arcs
abbrev head (t : DiTrail α β) := t.val.head
abbrev tail (t : DiTrail α β) := t.val.tail
abbrev length (t : DiTrail α β) := t.val.length
abbrev closed (t : DiTrail α β) := t.val.closed

@[ext] theorem ext {s t : DiTrail α β} (h : s.val = t.val) : s = t := Subtype.ext h

/-- The one-vertex directed trail. -/
def singleton (v : α) : DiTrail α β := ⟨Walk.singleton v, by simp⟩

@[simp] theorem val_singleton (v : α) : (singleton v : DiTrail α β).val = .singleton v := rfl

/-- Drop the final step of a directed trail. -/
def dropTail : DiTrail α β → DiTrail α β
  | ⟨.singleton v, _⟩ => singleton v
  | ⟨.cons w v tag, h⟩ => ⟨w, by
      apply List.Nodup.of_append_left
      simpa [Walk.arcs, List.concat_eq_append] using h⟩

/-- Drop the initial step of a directed trail. -/
def dropHead (t : DiTrail α β) : DiTrail α β :=
  ⟨t.val.dropHead, by
    rw [Walk.arcs_dropHead]
    exact t.property.tail⟩

@[simp] theorem val_dropTail (t : DiTrail α β) : t.dropTail.val = t.val.dropTail := by
  rcases t with ⟨w, h⟩
  cases w <;> rfl
@[simp] theorem val_dropHead (t : DiTrail α β) : t.dropHead.val = t.val.dropHead := rfl

private theorem reverseArc_injective :
    Function.Injective (fun a : Arc α β => Arc.mk a.tag (a.target, a.source)) := by
  intro a b h
  rcases a with ⟨atag, ⟨asource, atarget⟩⟩
  rcases b with ⟨btag, ⟨bsource, btarget⟩⟩
  simp only [Arc.target, Arc.source, Arc.mk.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

/-- Reverse a directed trail as raw data. Its realization belongs in the reversed digraph. -/
def reverse (t : DiTrail α β) : DiTrail α β :=
  ⟨t.val.reverse, by
    rw [Walk.arcs_reverse]
    exact (List.nodup_reverse.mpr t.property).map reverseArc_injective⟩

@[simp] theorem val_reverse (t : DiTrail α β) : t.reverse.val = t.val.reverse := rfl
@[simp] theorem reverse_reverse (t : DiTrail α β) : t.reverse.reverse = t := by
  apply Subtype.ext
  exact Walk.reverse_reverse t.val
@[simp] theorem head_reverse (t : DiTrail α β) : t.reverse.head = t.tail :=
  Walk.head_reverse t.val
@[simp] theorem tail_reverse (t : DiTrail α β) : t.reverse.tail = t.head :=
  Walk.tail_reverse t.val
@[simp] theorem length_reverse (t : DiTrail α β) : t.reverse.length = t.length :=
  Walk.length_reverse t.val

end DiTrail

end GraphLib
