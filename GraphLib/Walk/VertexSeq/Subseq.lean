/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Walk.VertexSeq.Append

/-!
# Vertex sequences: subsequence operations

Operations that carve a contiguous piece out of a vertex sequence, together
with their head/tail/length/subset laws and the preservation of `nodup` and
`nonstalling`.

## Main definitions

* `VertexSeq.prefixUntil`, `VertexSeq.suffixFrom` — the prefix/suffix cut at a
  chosen vertex.
* `VertexSeq.takeWhile`, `VertexSeq.dropWhile` — the prefix/suffix cut at the
  first vertex failing a predicate.
* `VertexSeq.splitAt` — split into pieces at every occurrence of a vertex.
-/

namespace GraphLib

variable {α : Type*}

namespace VertexSeq

/-! ## prefixUntil, suffixFrom -/

/-- The prefix of `w` ending at the first occurrence of the vertex `v`,
inclusive of that vertex. The hypothesis guarantees such a vertex exists. -/
@[grind] def prefixUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2 then prefixUntil w2 v h2
    else w2 :+ x

/-- The suffix of `w` starting at the first occurrence of the vertex `v`,
inclusive of that vertex. The hypothesis guarantees such a vertex exists. -/
@[grind] def suffixFrom [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2 then .cons (suffixFrom w2 v h2) x
    else .singleton x

@[simp] lemma length_prefixUntil_le [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).length ≤ w.length := by
  fun_induction prefixUntil w v h <;> grind

@[simp] lemma length_suffixFrom_le [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).length ≤ w.length := by
  fun_induction suffixFrom w v h <;> grind

@[simp] lemma head_prefixUntil [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).head = w.head := by
  fun_induction prefixUntil w v h <;> grind

@[simp] lemma tail_prefixUntil [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).tail = v := by
  fun_induction prefixUntil w v h <;> grind

@[simp] lemma prefixUntil_subset [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h) ⊆ w := by
  fun_induction prefixUntil <;> grind

/-- A `suffixFrom` result is contained in the original sequence. -/
@[simp] lemma suffixFrom_subset [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h) ⊆ w := by
  fun_induction suffixFrom w v h <;> grind[mem_cons]

@[simp] lemma head_suffixFrom [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).head = v := by
  fun_induction suffixFrom w v h <;> grind

@[simp] lemma tail_suffixFrom [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).tail = w.tail := by
  fun_induction suffixFrom w v h <;> grind

/-- For a sequence without repeated vertices, cutting a suffix at the vertex
at index `i` agrees on lists with dropping the first `i` entries. -/
lemma toList_suffixFrom_eq_drop [DecidableEq α] (w : VertexSeq α)
    (hw : w.nodup) (i : ℕ) (hi : i < w.toList.length) :
    (w.suffixFrom w.toList[i] (List.getElem_mem hi)).toList = w.toList.drop i := by
  induction w generalizing i <;>
    grind [toList, suffixFrom, length_toList, List.getElem_append_left, List.drop_append]

/-- If the vertex list of `w` splits as `u ++ a :: v`, then the suffix starting at
`a` is exactly `a :: v`.

This is the index-free face of `toList_suffixFrom_eq_drop`: callers describe the
cut by a list splitting instead of an index, so no dependent `getElem` bound has
to be carried around. -/
lemma toList_suffixFrom_eq_of_split [DecidableEq α] (w : VertexSeq α) (hw : w.nodup)
    (a : α) (ha : a ∈ w) (u v : List α) (h : w.toList = u ++ a :: v) :
    (w.suffixFrom a ha).toList = a :: v := by
  have hi : u.length < w.toList.length := by grind
  have hget : w.toList[u.length] = a := by grind [List.getElem_append_right]
  subst hget
  have hdrop := toList_suffixFrom_eq_drop w hw u.length hi
  grind [List.drop_left]

/-- Cutting a nontrivial prefix does not change the head remaining after
`dropHead`. -/
lemma head_dropHead_prefixUntil [DecidableEq α] (w : VertexSeq α)
    (b : α) (hb : b ∈ w) (hpos : (w.prefixUntil b hb).length ≠ 0) :
    (w.prefixUntil b hb).dropHead.head = w.dropHead.head := by
  induction w <;> grind

/-- A `prefixUntil` cut at a vertex other than the head is non-trivial: its head is
the original head and its tail is the cut point, so a length-zero cut would force
them to coincide. -/
lemma length_prefixUntil_ne_zero [DecidableEq α] (w : VertexSeq α) (v : α) (h : v ∈ w)
    (hne : v ≠ w.head) : (w.prefixUntil v h).length ≠ 0 := fun hz =>
  hne (((tail_prefixUntil w v h).symm.trans
    (head_eq_tail_of_length_zero _ hz).symm).trans (head_prefixUntil w v h))

/-- If the `prefixUntil` cut at `v` has length one, then `v` is the second vertex:
it is what remains at the head after dropping the original head. -/
lemma head_dropHead_prefixUntil_of_length_one [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) (h1 : (w.prefixUntil v h).length = 1) : w.dropHead.head = v :=
  (head_dropHead_prefixUntil w v h (by omega)).symm.trans
    ((head_dropHead_eq_tail_of_length_one _ h1).trans (tail_prefixUntil w v h))

/-- If the suffix from `v` has length at most one, then `v` is the last or the
second-to-last (penultimate) vertex of `w`. The disjunctive conclusion makes a
poor automatic rule, so this is left untagged and used by name. -/
lemma eq_tail_or_eq_penultimate_of_length_suffixFrom_le_one [DecidableEq α]
    (w : VertexSeq α) {v : α} (hv : v ∈ w) (hpos : w.length ≠ 0)
    (h : (w.suffixFrom v hv).length ≤ 1) :
    v = w.tail ∨ v = w.dropTail.tail := by
  cases w <;> grind

/-! ## takeWhile, dropWhile -/

/-- Take every vertex of `w` satisfying `p`, plus the first failure (if any).
If every vertex satisfies `p`, the whole sequence is returned. -/
@[grind] def takeWhile (w : VertexSeq α) (p : α → Prop) [DecidablePred p] :
    VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons q x =>
    if ∃ v ∈ q.toList, ¬ p v then takeWhile q p
    else q :+ x

/-- Drop the longest prefix of `w` on which `p` holds; the result starts at
the first failure. The hypothesis ensures a failure exists. -/
@[grind] def dropWhile (w : VertexSeq α) (p : α → Prop) [DecidablePred p]
    (h : ∃ v ∈ w.toList, ¬ p v) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons q x =>
    if hq : ∃ v ∈ q.toList, ¬ p v then (dropWhile q p hq) :+ x
    else .singleton x

/-- `dropWhile` returns a suffix ending at the original tail, so it preserves
the tail. -/
@[simp, grind =] lemma tail_dropWhile (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (h : ∃ v ∈ w.toList, ¬ p v) :
    (w.dropWhile p h).tail = w.tail := by
  fun_induction dropWhile w p h <;> grind

/-- A `dropWhile` result is a suffix of the original sequence. -/
@[grind] lemma dropWhile_subset (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (h : ∃ v ∈ w.toList, ¬ p v) : (w.dropWhile p h) ⊆ w := by
  intro y hy
  fun_induction dropWhile w p h <;> grind

/-- The head remaining after `dropWhile` does not satisfy the dropped
predicate. -/
lemma not_pred_head_dropWhile (w : VertexSeq α) (pred : α → Prop)
    [DecidablePred pred] (h : ∃ z ∈ w.toList, ¬ pred z) :
    ¬ pred (w.dropWhile pred h).head := by
  fun_induction dropWhile w pred h <;> grind

/-- A vertex in the prefix ending at the first vertex that fails `pred` is
either that endpoint or satisfies `pred`. -/
lemma eq_head_dropWhile_or_pred_of_mem_prefixUntil [DecidableEq α]
    (w : VertexSeq α) (pred : α → Prop) [DecidablePred pred]
    (h : ∃ z ∈ w.toList, ¬ pred z) {z : α}
    (hz : z ∈ w.prefixUntil (w.dropWhile pred h).head
      (dropWhile_subset w pred h _ (head_mem _))) :
    z = (w.dropWhile pred h).head ∨ pred z := by
  fun_induction dropWhile w pred h <;> grind [prefixUntil]

/-! ## splitAt -/

/-- Split `w` into a list of pieces at every occurrence of the vertex `v`.
The split point `v` is *duplicated*: it appears as the tail of one piece and
the head of the next, so that re-concatenating the pieces recovers `w`. -/
@[grind] def splitAt [DecidableEq α] : VertexSeq α → α → List (VertexSeq α)
  | .singleton x, _ => [.singleton x]
  | .cons q x, v =>
    if x = v then appendToLast (splitAt q v) v ++ [.singleton v]
    else appendToLast (splitAt q v) x
where
  appendToLast : List (VertexSeq α) → α → List (VertexSeq α)
    | [], _ => []
    | [w], x => [w :+ x]
    | p :: ps, x => p :: appendToLast ps x

/-- If every piece of `L` is contained in `w`, then every piece of
`appendToLast L x` is contained in `w :+ x`. -/
@[grind] lemma appendToLast_subset (L : List (VertexSeq α)) (x : α)
    (w : VertexSeq α) (hL : ∀ p ∈ L, p ⊆ w) {q : VertexSeq α}
    (hq : q ∈ splitAt.appendToLast L x) : q ⊆ w :+ x := by
  revert q
  induction L with
  | nil => grind [splitAt.appendToLast]
  | cons p ps ih =>
      cases ps <;> grind [splitAt.appendToLast, mem_cons, hL p (by simp)]

/-- Every piece produced by `splitAt` is contained in the original sequence. -/
@[grind] lemma splitAt_subset [DecidableEq α] (w : VertexSeq α) (v : α)
    {p : VertexSeq α} (hp : p ∈ w.splitAt v) : p ⊆ w := by
  revert p
  fun_induction splitAt w v <;> grind [appendToLast_subset]

/-- `appendToLast` extends the final piece, so the last piece becomes the old
last piece with `x` appended. -/
@[simp, grind =] lemma getLast?_appendToLast (L : List (VertexSeq α)) (x : α) :
    (splitAt.appendToLast L x).getLast? = (L.getLast?).map (· :+ x) := by
  fun_induction splitAt.appendToLast L x <;> grind

/-- Every piece produced by `splitAt` ends at the original tail. -/
@[grind] lemma tail_getLast?_splitAt [DecidableEq α] (w : VertexSeq α) (v : α)
    {p : VertexSeq α} (hp : p ∈ (w.splitAt v).getLast?) : p.tail = w.tail := by
  revert p
  fun_induction splitAt w v <;> grind

/-! ## Reassembling a sequence from its cut at a vertex -/

/-- Cutting at an interior vertex `v` and re-gluing the prefix (with its
duplicated `v` dropped) to the suffix recovers the original sequence. -/
@[simp, grind →] lemma dropTail_prefixUntil_append_suffixFrom [DecidableEq α]
    (w : VertexSeq α) (v : α) (h : v ∈ w) (hne : v ≠ w.head) :
    (w.prefixUntil v h).dropTail.append (w.suffixFrom v h) = w := by
  fun_induction prefixUntil w v h <;>
    grind [suffixFrom, append, dropTail, mem_cons]

/-! ## Nodup preservation -/

/-- A `prefixUntil` of a `nodup` sequence is `nodup`. -/
@[grind] lemma nodup_prefixUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) (hw : w.nodup) : (w.prefixUntil v h).nodup := by
  fun_induction prefixUntil w v h <;> grind

/-- A `suffixFrom` of a `nodup` sequence is `nodup`. -/
@[grind] lemma nodup_suffixFrom [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) (hw : w.nodup) : (w.suffixFrom v h).nodup := by
  fun_induction suffixFrom w v h <;> grind [suffixFrom_subset]

/-- `takeWhile` preserves `nodup`. -/
@[grind] lemma nodup_takeWhile (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (hw : w.nodup) : (w.takeWhile p).nodup := by
  fun_induction takeWhile w p <;> grind

/-- `dropWhile` preserves `nodup`. -/
@[grind] lemma nodup_dropWhile (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (h : ∃ v ∈ w.toList, ¬ p v) (hw : w.nodup) :
    (w.dropWhile p h).nodup := by
  fun_induction dropWhile w p h <;> grind [dropWhile_subset]

/-- If every piece of `L` is nodup and avoids `x`, then `appendToLast L x`
has only nodup pieces. -/
@[grind] lemma nodup_appendToLast (L : List (VertexSeq α)) (x : α)
    (hL : ∀ p ∈ L, p.nodup) (havoid : ∀ p ∈ L, x ∉ p) {q : VertexSeq α}
    (hq : q ∈ splitAt.appendToLast L x) : q.nodup := by
  revert q
  induction L with
  | nil => grind [splitAt.appendToLast]
  | cons p ps ih => cases ps <;> grind [splitAt.appendToLast]

/-- Each piece of a `splitAt` of a `nodup` sequence is `nodup`. -/
@[grind] lemma nodup_splitAt [DecidableEq α] (w : VertexSeq α)
    (hw : w.nodup) (v : α) {p : VertexSeq α} (hp : p ∈ w.splitAt v) : p.nodup := by
  revert p
  induction w with
  | singleton x => grind
  | cons q x ih =>
      have havoid : ∀ s ∈ q.splitAt v, x ∉ s := fun s hs hsx =>
        hw.2 (splitAt_subset q v hs x hsx)
      have hkey : ∀ s ∈ splitAt.appendToLast (q.splitAt v) x, s.nodup :=
        fun s hs => nodup_appendToLast (q.splitAt v) x
          (fun t ht => ih hw.1 ht) havoid hs
      grind

/-! ## Non-stalling preservation -/

/-- A `prefixUntil` of a non-stalling sequence is non-stalling. -/
@[grind] lemma nonstalling_prefixUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) (hw : w.nonstalling) : (w.prefixUntil v h).nonstalling := by
  fun_induction prefixUntil w v h <;> grind

/-- A `suffixFrom` of a non-stalling sequence is non-stalling. -/
@[grind] lemma nonstalling_suffixFrom [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) (hw : w.nonstalling) : (w.suffixFrom v h).nonstalling := by
  fun_induction suffixFrom w v h <;> grind

/-- `takeWhile` preserves non-stalling. -/
@[grind] lemma nonstalling_takeWhile (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (hw : w.nonstalling) : (w.takeWhile p).nonstalling := by
  fun_induction takeWhile w p <;> grind

/-- `dropWhile` preserves non-stalling. -/
@[grind] lemma nonstalling_dropWhile (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (h : ∃ v ∈ w.toList, ¬ p v) (hw : w.nonstalling) :
    (w.dropWhile p h).nonstalling := by
  fun_induction dropWhile w p h <;> grind

/-- If every piece of `L` is non-stalling and the final piece does not end at
`x`, then every piece of `appendToLast L x` is non-stalling. -/
@[grind] lemma nonstalling_appendToLast (L : List (VertexSeq α)) (x : α)
    (hL : ∀ p ∈ L, p.nonstalling) (hlast : ∀ p ∈ L.getLast?, p.tail ≠ x)
    {q : VertexSeq α} (hq : q ∈ splitAt.appendToLast L x) : q.nonstalling := by
  revert q
  fun_induction splitAt.appendToLast L x <;> grind

/-- Each piece of a `splitAt` of a non-stalling sequence is non-stalling. -/
@[grind] lemma nonstalling_splitAt [DecidableEq α] (w : VertexSeq α)
    (hw : w.nonstalling) (v : α) {p : VertexSeq α}
    (hp : p ∈ w.splitAt v) : p.nonstalling := by
  revert p
  fun_induction splitAt w v <;> grind

/-! ## First vertex satisfying a predicate -/

/-- Scanning `q` from its head, the first vertex satisfying `P` other than the
head yields a `prefixUntil` cut whose only `P`-vertices are its two endpoints:
the cut point `b` itself (the tail of the prefix) and `q.head` (its head).

This is the vertex-sequence analogue of locating the first predicate hit; it is
used to isolate a minimal prefix that meets a given set only at its two ends. -/
lemma exists_prefixUntil_pred_eq_head_or_tail [DecidableEq α] (P : α → Prop)
    (q : VertexSeq α) (hz : ∃ z ∈ q, P z ∧ z ≠ q.head) :
    ∃ b, ∃ hb : b ∈ q, P b ∧ b ≠ q.head ∧
      ∀ z ∈ q.prefixUntil b hb, P z → z = b ∨ z = q.head := by
  classical
  set p : α → Prop := fun z => ¬ (P z ∧ z ≠ q.head) with hp
  have h : ∃ z ∈ q.toList, ¬ p z := by grind
  refine ⟨_, dropWhile_subset q p h _ (head_mem _), ?_, ?_, ?_⟩ <;>
    grind [not_pred_head_dropWhile, eq_head_dropWhile_or_pred_of_mem_prefixUntil]

end VertexSeq

end GraphLib
