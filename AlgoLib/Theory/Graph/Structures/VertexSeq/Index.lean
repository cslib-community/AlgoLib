/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import AlgoLib.Theory.Graph.Structures.VertexSeq.Basic

/-!
# Vertex sequences: indexing and insertion

Positional access into a vertex sequence via the underlying list, and insertion
of a vertex at a given index.

## Main definitions

* `GetElem (VertexSeq α) ℕ α` — index into the visited vertices.
* `VertexSeq.insert` — insert a vertex at a position.

`insert` currently has no lemmas and no clients inside AlgoLib; it is kept as the
one positional *editing* operation the carrier is expected to offer.
-/

variable {α : Type*}

namespace VertexSeq

/-! ## Indexing -/

instance : GetElem (VertexSeq α) ℕ α (fun w i ↦ i < w.toList.length) where
  getElem w i h := w.toList[i]

/-- Indexing position zero returns the head vertex. -/
lemma getElem_zero_eq_head (w : VertexSeq α) :
    w.toList[0]'(by rw [length_toList]; omega) = w.head := by
  induction w <;> grind [toList, head, List.getElem_append_left, length_toList]

/-- For a nontrivial sequence, the head after `dropHead` is the vertex at
index one. -/
lemma head_dropHead_eq_getElem_one (w : VertexSeq α)
    (h : w.length ≠ 0) :
    w.dropHead.head = w.toList[1]'(by rw [length_toList]; omega) := by
  induction w <;>
    grind [toList, head, dropHead, length_toList, List.getElem_append_left,
      head_dropHead_cons, eq_singleton_of_length_zero]

/-- If the vertex list starts `a :: b :: _`, then the head after `dropHead` is `b`.
The index-free face of `head_dropHead_eq_getElem_one`. -/
lemma head_dropHead_of_toList_eq_cons_cons (w : VertexSeq α) (a b : α) (rest : List α)
    (h : w.toList = a :: b :: rest) : w.dropHead.head = b := by
  have hpos : w.length ≠ 0 := by
    have := length_toList w
    grind
  rw [head_dropHead_eq_getElem_one w hpos]
  grind

/-! ## insert -/

/-- Insert the vertex `v` at index `i`, shifting later vertices one position
to the right. If `i` exceeds `w.toList.length`, `v` is appended at the end. -/
@[grind] def insert : VertexSeq α → ℕ → α → VertexSeq α
  | .singleton x, 0, v => .cons (.singleton v) x
  | .singleton x, _ + 1, v => .cons (.singleton x) v
  | .cons q x, i, v =>
    if i ≤ q.length then .cons (insert q i v) x
    else if i = q.length + 1 then .cons (q :+ v) x
    else .cons (q :+ x) v

end VertexSeq
