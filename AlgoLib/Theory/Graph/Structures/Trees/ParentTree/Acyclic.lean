/-
Copyright (c) 2026 AlgoLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import AlgoLib.Theory.Graph.Structures.Trees.ParentTree.Basic
import Mathlib.Data.Finset.Max

/-!
# Acyclicity of parent trees

The two edges of a cycle incident to a maximum-level vertex would both have
to lead to its parent. This contradicts the distinctness of the two cycle
neighbors.
-/

namespace AlgoLib
namespace ParentTree

variable {α : Type*}

/-- A neighbor of no greater level than `u` must be the parent of `u`. -/
private theorem parent_eq_of_adj_le (G : ParentTree α) {u v : α}
    (_hu : u ∈ G.vertexSet) (hadj : G.toSimpleGraph.Adj u v)
    (hle : G.level v ≤ G.level u) : G.parent u = v := by
  rcases (G.adj_iff.mp hadj) with ⟨hne, h | h⟩
  · exact h.2
  · obtain ⟨hv, hp⟩ := h
    have hvpos : 0 < G.level v := by
      by_contra hn
      have hz : G.level v = 0 := by omega
      have hroot : v = G.parent v := (G.root v hv).mp hz
      exact hne (hroot.trans hp).symm
    have hlt : G.level u < G.level v := by
      simpa only [hp] using G.ordering v hv hvpos
    omega

private theorem first_ne_penultimate (w : VertexSeq α)
    (hnd : w.dropTail.nodup) (hlen : 3 ≤ w.length) :
    w.dropHead.head ≠ w.dropTail.tail := by
  cases w with
  | singleton v => simp [VertexSeq.length] at hlen
  | cons p v =>
      have hpLen : 2 ≤ p.length := by
        simp only [VertexSeq.length] at hlen
        omega
      have hpPos : p.length ≠ 0 := by omega
      have hfirst : (p.cons v).dropHead.head = p.dropHead.head :=
        VertexSeq.head_dropHead_cons p v hpPos
      have hmem : p.dropHead.head ∈ p.dropTail := by
        cases p with
        | singleton u => simp [VertexSeq.length] at hpLen
        | cons q u =>
            have hqPos : q.length ≠ 0 := by
              simp only [VertexSeq.length] at hpLen
              omega
            have hqmem : q.dropHead.head ∈ q :=
              (VertexSeq.dropHead_subset q) q.dropHead.head
                (VertexSeq.head_mem q.dropHead)
            simpa [VertexSeq.dropTail, VertexSeq.head_dropHead_cons q u hqPos]
              using hqmem
      have hnot : p.tail ∉ p.dropTail :=
        VertexSeq.tail_not_mem_dropTail_of_nodup p hnd hpPos
      intro heq
      have heq' : p.dropHead.head = p.tail := by
        simpa [hfirst, VertexSeq.dropTail] using heq
      exact hnot (heq' ▸ hmem)

private theorem adj_penultimate (H : SimpleGraph α) (w : VertexSeq α)
    (hw : H.IsVertexSeqIn w) (hpos : 0 < w.length) :
    H.Adj w.dropTail.tail w.tail := by
  cases w with
  | singleton v => simp [VertexSeq.length] at hpos
  | cons p v => exact (SimpleGraph.IsVertexSeqIn.cons_iff H p v).mp hw |>.2

private theorem adj_first (H : SimpleGraph α) (w : VertexSeq α)
    (hw : H.IsVertexSeqIn w) (hpos : 0 < w.length) :
    H.Adj w.head w.dropHead.head := by
  have hr : H.IsVertexSeqIn w.reverse := SimpleGraph.IsVertexSeqIn.reverse H hw
  have hposr : 0 < w.reverse.length := by simpa using hpos
  have h := adj_penultimate H w.reverse hr hposr
  simpa [VertexSeq.dropTail_reverse] using h.symm

private theorem reroot_mem (c : SimpleCycle α) [DecidableEq α]
    (u : α) (hu : u ∈ c.vertices) {x : α}
    (hx : x ∈ (c.reroot u hu).vertices) : x ∈ c.vertices := by
  unfold SimpleCycle.reroot at hx
  split at hx
  · exact hx
  · unfold SimpleWalk.glue at hx
    split at hx
    · exact (VertexSeq.prefixUntil_subset c.vertices u hu) x hx
    · rcases (VertexSeq.mem_append x _ _).mp hx with hleft | hright
      · exact (VertexSeq.suffixFrom_subset c.vertices u hu) x
          ((VertexSeq.dropTail_subset _) x hleft)
      · exact (VertexSeq.prefixUntil_subset c.vertices u hu) x hright

private theorem reroot_head (c : SimpleCycle α) [DecidableEq α]
    (u : α) (hu : u ∈ c.vertices) : (c.reroot u hu).head = u := by
  unfold SimpleCycle.reroot
  split
  · simp [*]
  · simp [SimpleWalk.head_glue, VertexSeq.head_suffixFrom]

private theorem isCycleIn_reroot (H : SimpleGraph α) (c : SimpleCycle α)
    [DecidableEq α] (hc : H.IsSimpleCycleIn c) (u : α)
    (hu : u ∈ c.vertices) : H.IsSimpleCycleIn (c.reroot u hu) := by
  unfold SimpleCycle.reroot
  split
  · exact hc
  · have hjoin : (c.val.suffixFrom u hu).val.tail =
          (c.val.prefixUntil u hu).val.head := by
      simpa using c.closed.symm
    exact SimpleGraph.IsSimpleWalkIn.glue H
      (SimpleGraph.IsSimpleWalkIn.suffixFrom H hc u hu)
      (SimpleGraph.IsSimpleWalkIn.prefixUntil H hc u hu) hjoin

/-- The simple graph induced by any finite parent-pointer forest is acyclic. -/
theorem isAcyclic (G : ParentTree α) :
    G.toSimpleGraph.IsAcyclic := by
  classical
  rintro ⟨c, hc⟩
  have hs : c.support.toFinset.Nonempty := by
    refine ⟨c.head, ?_⟩
    simp [SimpleCycle.support, SimpleCycle.head, VertexSeq.head_mem]
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image c.support.toFinset G.level hs
  have hvc : v ∈ c.vertices := by simpa [SimpleCycle.support] using hv
  let d := c.reroot v hvc
  have hd : G.toSimpleGraph.IsSimpleCycleIn d := isCycleIn_reroot G.toSimpleGraph c hc v hvc
  have hvd : d.head = v := reroot_head c v hvc
  let a := d.vertices.dropHead.head
  let b := d.vertices.dropTail.tail
  have hlen : 0 < d.vertices.length := by
    have hthree : 3 ≤ d.vertices.length := d.2.1
    omega
  have hwa : G.toSimpleGraph.Adj d.head a :=
    adj_first G.toSimpleGraph d.vertices hd hlen
  have hwb : G.toSimpleGraph.Adj b d.tail :=
    adj_penultimate G.toSimpleGraph d.vertices hd hlen
  have hclosed : d.head = d.tail := d.closed
  have ha : a ∈ d.vertices :=
    (VertexSeq.dropHead_subset d.vertices) a
      (VertexSeq.head_mem d.vertices.dropHead)
  have hb : b ∈ d.vertices :=
    (VertexSeq.dropTail_subset d.vertices) b
      (VertexSeq.tail_mem d.vertices.dropTail)
  have haOrig : a ∈ c.vertices := reroot_mem c v hvc ha
  have hbOrig : b ∈ c.vertices := reroot_mem c v hvc hb
  have haLe : G.level a ≤ G.level v := hmax a (by simpa [SimpleCycle.support] using haOrig)
  have hbLe : G.level b ≤ G.level v := hmax b (by simpa [SimpleCycle.support] using hbOrig)
  have hvMem : v ∈ G.vertexSet := by
    have h := SimpleGraph.IsSimpleWalkIn.head_mem G.toSimpleGraph hd
    simpa [hvd] using h
  have hpa : G.parent v = a := parent_eq_of_adj_le G hvMem (hvd ▸ hwa) haLe
  have hpb : G.parent v = b :=
    parent_eq_of_adj_le G hvMem (by simpa [← hvd, ← hclosed] using hwb.symm) hbLe
  have hab : a ≠ b := first_ne_penultimate d.vertices d.2.2.2 d.2.1
  exact hab (hpa.symm.trans hpb)

theorem isForest (G : ParentTree α) :
    G.toSimpleGraph.IsForest := G.isAcyclic

end ParentTree
end AlgoLib
