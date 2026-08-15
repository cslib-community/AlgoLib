/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Walk.VertexSeq.Basic

/-!
# Vertex sequences: structural predicates

The three predicates that classify the shape of a vertex sequence:

* `VertexSeq.nodup` — no repeated vertex.
* `VertexSeq.nonstalling` — no two consecutive vertices are equal.
* `VertexSeq.closed` — the first and last vertex coincide.

This file states their definitions together with the preservation lemmas that
only involve the endpoint-dropping operations of `Basic`; preservation under
`append`, `reverse`, the subsequence operations, etc. lives alongside those
operations in their own files.

## Main definitions

* `VertexSeq.nodup`, `VertexSeq.nonstalling`, `VertexSeq.closed`.
-/

namespace GraphLib

variable {α : Type*}

namespace VertexSeq

/-! ## Definitions -/

/-- The sequence has no repeated vertex. -/
@[grind] def nodup : VertexSeq α → Prop
  | .singleton _ => True
  | .cons w v    => w.nodup ∧ v ∉ w

/-- The sequence never stalls: no two consecutive vertices are equal. -/
@[grind] def nonstalling : VertexSeq α → Prop
  | .singleton _ => True
  | .cons w v    => w.nonstalling ∧ w.tail ≠ v

/-- A vertex sequence is *closed* when its first and last vertex coincide. -/
@[grind] def closed (w : VertexSeq α) : Prop := w.head = w.tail

/-! ## Implications between the predicates -/

/-- A duplicate-free sequence never stalls: a stall would repeat a vertex. -/
@[grind] lemma nonstalling_of_nodup (w : VertexSeq α) (h : w.nodup) :
    w.nonstalling := by induction w <;> grind

/-- A closed `nodup` sequence has length zero: a repeated endpoint forces a
duplicate unless the sequence is a single vertex. -/
@[grind] lemma length_zero_of_nodup_closed (w : VertexSeq α)
    (hnd : w.nodup) (hclosed : w.closed) : w.length = 0 := by
  cases w <;> grind

/-! ## Nodup preservation under dropHead, dropTail -/

/-- Dropping the first vertex preserves `nodup`. -/
@[grind] lemma nodup_dropHead (w : VertexSeq α) (h : w.nodup) :
    w.dropHead.nodup := by
  induction w <;> grind [dropHead_subset]

/-- Dropping the last vertex preserves `nodup`. -/
@[grind] lemma nodup_dropTail (w : VertexSeq α) (h : w.nodup) :
    w.dropTail.nodup := by
  cases w <;> grind

/-- In a non-trivial `nodup` sequence, the head does not reappear after dropping
it. -/
@[grind] lemma head_not_mem_dropHead_of_nodup (w : VertexSeq α)
    (hnd : w.nodup) (hpos : w.length ≠ 0) : w.head ∉ w.dropHead := by
  induction w <;> grind [dropHead_subset]

/-- In a non-trivial `nodup` sequence, the tail does not reappear after dropping
it. -/
@[grind] lemma tail_not_mem_dropTail_of_nodup (w : VertexSeq α)
    (hnd : w.nodup) (hpos : w.length ≠ 0) : w.tail ∉ w.dropTail := by
  cases w with
  | singleton u => simp [length] at hpos
  | cons w u =>
      simp only [dropTail, tail_cons]
      simpa [nodup] using hnd.2

/-- For a closed sequence with a `nodup` interior (drop the repeated tail), the
opposite interior (drop the repeated head) is also `nodup`. -/
@[grind] lemma nodup_dropHead_of_closed_dropTail (w : VertexSeq α)
    (hclosed : w.closed) (hnodup : w.dropTail.nodup) :
    w.dropHead.nodup := by
  cases w with
  | singleton v => grind [dropHead]
  | cons w v =>
      cases w <;>
        grind [dropHead, nodup, closed, head_not_mem_dropHead_of_nodup, nodup_dropHead]

/-! ## Non-stalling preservation under dropHead, dropTail -/

/-- Dropping the first vertex preserves non-stalling. -/
@[grind] lemma nonstalling_dropHead (w : VertexSeq α) (h : w.nonstalling) :
    w.dropHead.nonstalling := by
  fun_induction dropHead w <;> grind

/-- Dropping the last vertex preserves non-stalling. -/
@[grind] lemma nonstalling_dropTail (w : VertexSeq α) (h : w.nonstalling) :
    w.dropTail.nonstalling := by
  cases w <;> grind

/-! ## Nodup and the underlying list -/

/-- `nodup` is exactly `Nodup` of the underlying list. -/
lemma nodup_iff_toList_nodup (w : VertexSeq α) :
    w.nodup ↔ w.toList.Nodup := by
  induction w <;>
    simp_all [nodup, toList, List.concat_eq_append, List.nodup_append, mem_def]
  all_goals grind

end VertexSeq

end GraphLib
