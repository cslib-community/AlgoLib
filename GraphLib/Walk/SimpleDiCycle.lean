/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.SimpleCycle

/-!
# Directed simple cycles

Unlike the undirected `SimpleCycle`, a directed simple cycle may have length two. Length one is
excluded because simple directed graphs have no loops.
-/

namespace GraphLib

variable {α : Type*}

namespace SimpleWalk

/-- Directed simple-cycle convention: at least two arcs, closed, with a duplicate-free interior. -/
@[grind] def IsDiCycle (w : SimpleWalk α) : Prop :=
  2 ≤ w.length ∧ w.closed ∧ w.dropTail.nodup

namespace IsDiCycle

theorem reverse (w : SimpleWalk α) (h : w.IsDiCycle) : w.reverse.IsDiCycle := by
  obtain ⟨hlen, hclosed, hnodup⟩ := h
  exact ⟨by simpa using hlen, by simpa [VertexSeq.closed] using hclosed.symm,
    VertexSeq.nodup_reverse_dropTail_of_closed w.val hclosed hnodup⟩

end IsDiCycle

end SimpleWalk

/-- A directed simple cycle, admitting directed two-cycles. -/
def SimpleDiCycle (α : Type*) := {w : SimpleWalk α // w.IsDiCycle}

namespace SimpleDiCycle

abbrev val (c : SimpleDiCycle α) : SimpleWalk α := c.1
abbrev vertices (c : SimpleDiCycle α) : VertexSeq α := c.val.val
abbrev support (c : SimpleDiCycle α) : List α := c.vertices.toList
abbrev edges (c : SimpleDiCycle α) : List (Sym2 α) := c.vertices.edges
abbrev arcs (c : SimpleDiCycle α) : List (α × α) := c.vertices.arcs
abbrev head (c : SimpleDiCycle α) : α := c.vertices.head
abbrev tail (c : SimpleDiCycle α) : α := c.vertices.tail
abbrev length (c : SimpleDiCycle α) : ℕ := c.vertices.length

instance : Coe (SimpleDiCycle α) (SimpleWalk α) := ⟨val⟩

theorem two_le_length (c : SimpleDiCycle α) : 2 ≤ c.length := c.2.1
theorem closed (c : SimpleDiCycle α) : c.val.closed := c.2.2.1

/-- The vertex-simple interior. -/
def interior (c : SimpleDiCycle α) : SimplePath α := ⟨c.val.dropTail, c.2.2.2⟩

/-- Reverse the raw orientation of a directed simple cycle. -/
def reverse (c : SimpleDiCycle α) : SimpleDiCycle α :=
  ⟨c.val.reverse, SimpleWalk.IsDiCycle.reverse c.val c.2⟩

@[simp] theorem val_reverse (c : SimpleDiCycle α) : (reverse c).val = c.val.reverse := rfl
@[simp] theorem reverse_reverse (c : SimpleDiCycle α) : c.reverse.reverse = c := by
  apply Subtype.ext
  apply Subtype.ext
  exact VertexSeq.reverse_reverse c.vertices

/-! ## Closing a path -/

private def walkOfPathClosing (p : SimplePath α) (hlen : 1 ≤ p.length) : SimpleWalk α :=
  ⟨p.vertices.cons p.head, ⟨p.val.nonstalling, fun h => by
    change 1 ≤ p.vertices.length at hlen
    have hzero := VertexSeq.length_zero_of_nodup_closed p.vertices p.nodup
      (show p.vertices.closed from h.symm)
    omega⟩⟩

private theorem isDiCycle_ofPathClosing (p : SimplePath α) (hlen : 1 ≤ p.length) :
    (walkOfPathClosing p hlen).IsDiCycle := by
  change 1 ≤ p.vertices.length at hlen
  change 2 ≤ (p.vertices.cons p.head).length ∧
    (p.vertices.cons p.head).closed ∧ (p.vertices.cons p.head).dropTail.nodup
  refine ⟨?_, by simp [VertexSeq.closed], by simpa using p.nodup⟩
  change 2 ≤ 1 + p.vertices.length
  omega

/-- Close a nontrivial simple path by adding a directed arc from its tail to its head. -/
def ofPathClosing (p : SimplePath α) (hlen : 1 ≤ p.length) : SimpleDiCycle α :=
  ⟨walkOfPathClosing p hlen, isDiCycle_ofPathClosing p hlen⟩

/-! ## Rerooting -/

private theorem tail_suffixFrom_eq_head_prefixUntil [DecidableEq α]
    (c : SimpleDiCycle α) (u : α) (hu : u ∈ c.vertices) :
    (c.val.suffixFrom u hu).val.tail = (c.val.prefixUntil u hu).val.head := by
  simpa using c.closed.symm

private theorem isDiCycle_reroot_glue [DecidableEq α] (c : SimpleDiCycle α) (u : α)
    (hu : u ∈ c.vertices) (hhead : u ≠ c.head) :
    ((c.val.suffixFrom u hu).glue (c.val.prefixUntil u hu)
      (tail_suffixFrom_eq_head_prefixUntil c u hu)).IsDiCycle := by
  have hsplit := VertexSeq.dropTail_prefixUntil_append_suffixFrom c.vertices u hu hhead
  let pre := c.vertices.prefixUntil u hu
  let suf := c.vertices.suffixFrom u hu
  have hpre_pos : pre.length ≠ 0 := fun hz =>
    hhead (by simpa [pre] using (VertexSeq.head_eq_tail_of_length_zero pre hz).symm)
  have hsuf_pos : suf.length ≠ 0 := by
    intro hz
    have huTail : u = c.vertices.tail := by
      simpa [suf] using VertexSeq.head_eq_tail_of_length_zero suf hz
    exact hhead (huTail.trans c.closed.symm)
  have hsplit' : pre.dropTail.append suf = c.vertices := by simpa [pre, suf] using hsplit
  have hleft : (pre.dropTail.append suf.dropTail).nodup := by
    rw [← VertexSeq.dropTail_append pre.dropTail suf hsuf_pos,
      congrArg VertexSeq.dropTail hsplit']
    exact c.2.2.2
  have hsuf_pos' : (c.val.suffixFrom u hu).val.length ≠ 0 := by simpa [suf] using hsuf_pos
  have hlenAll : pre.dropTail.length + suf.length + 1 = c.vertices.length := by
    simpa [VertexSeq.length_append] using congrArg VertexSeq.length hsplit'
  have hpreLen := VertexSeq.length_dropTail_succ pre hpre_pos
  have hsufLen := VertexSeq.length_dropTail_succ suf hsuf_pos
  simp only [SimpleWalk.IsDiCycle, SimpleWalk.glue, hsuf_pos']
  refine ⟨?_, ?_, ?_⟩
  · change 2 ≤ (suf.dropTail.append pre).length
    rw [VertexSeq.length_append]
    omega
  · change (suf.dropTail.append pre).closed
    simp [VertexSeq.closed, pre, suf]
  · change (suf.dropTail.append pre).dropTail.nodup
    rw [VertexSeq.dropTail_append suf.dropTail pre hpre_pos]
    exact VertexSeq.nodup_append_comm pre.dropTail suf.dropTail hleft

/-- Re-root a directed simple cycle at any visited vertex. -/
def reroot [DecidableEq α] (c : SimpleDiCycle α) (u : α) (hu : u ∈ c.vertices) :
    SimpleDiCycle α :=
  if hhead : u = c.head then c
  else
    ⟨(c.val.suffixFrom u hu).glue (c.val.prefixUntil u hu)
        (tail_suffixFrom_eq_head_prefixUntil c u hu),
      isDiCycle_reroot_glue c u hu hhead⟩

@[simp] theorem length_arcs (c : SimpleDiCycle α) : c.arcs.length = c.length :=
  VertexSeq.length_arcs c.vertices

theorem arcs_eq_interior_concat (c : SimpleDiCycle α) :
    c.arcs = c.interior.arcs ++ [(c.interior.tail, c.tail)] := by
  have hpos : c.vertices.length ≠ 0 := by
    have hlen : 2 ≤ c.vertices.length := c.2.1
    exact Nat.ne_of_gt (by omega)
  simpa [List.concat_eq_append] using VertexSeq.arcs_eq_dropTail_concat c.vertices hpos

private theorem closing_arc_not_mem (w : VertexSeq α) (hnodup : w.nodup)
    (hpos : 0 < w.length) : (w.tail, w.head) ∉ w.arcs := by
  intro hmem
  have hle := VertexSeq.length_le_one_of_closing_arc_mem w hnodup hmem
  have hlen : w.length = 1 := by omega
  cases w with
  | singleton v => simp [VertexSeq.length] at hpos
  | cons w v =>
      cases w with
      | singleton u =>
          simp [VertexSeq.arcs, VertexSeq.tail, VertexSeq.head] at hmem
          simp [VertexSeq.nodup, VertexSeq.mem_def, VertexSeq.toList] at hnodup
          exact hnodup hmem.1
      | cons w u => simp [VertexSeq.length] at hlen

/-- A directed simple cycle traverses each arc at most once. -/
theorem arcs_nodup (c : SimpleDiCycle α) : c.arcs.Nodup := by
  rw [arcs_eq_interior_concat, List.nodup_append]
  refine ⟨c.interior.arcs_nodup, by simp, ?_⟩
  have hclosedTail : c.tail = c.interior.head := by
    simpa [interior] using c.closed.symm
  have hcpos : c.vertices.length ≠ 0 := Nat.ne_of_gt (by
    have hlen : 2 ≤ c.vertices.length := c.2.1
    omega)
  have hdrop := VertexSeq.length_dropTail_succ c.vertices hcpos
  have hinteriorPos : 0 < c.interior.length := by
    change 0 < c.vertices.dropTail.length
    have hlen : 2 ≤ c.vertices.length := c.2.1
    omega
  intro a ha b hb hab
  simp only [List.mem_singleton] at hb
  subst b
  subst a
  apply closing_arc_not_mem c.interior.vertices c.interior.nodup hinteriorPos
  simpa [hclosedTail] using ha

@[simp] theorem arcs_reverse (c : SimpleDiCycle α) :
    c.reverse.arcs = c.arcs.reverse.map (fun a : α × α => (a.2, a.1)) :=
  VertexSeq.arcs_reverse c.vertices

end SimpleDiCycle

end GraphLib
