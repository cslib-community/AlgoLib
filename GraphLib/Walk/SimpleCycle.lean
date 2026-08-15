/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Walk.SimplePath

/-!
# Simple cycles

A `SimpleCycle α` is a closed `SimpleWalk α` of length at least three whose
interior (the walk with its final repeated vertex dropped) is a simple path.
It is represented as a subtype of `SimpleWalk`.

The length-≥-3 bound is the *undirected* convention; the directed notion
(which admits length-two cycles) will get its own `SimpleDiCycle`. The `arcs`
API here only reflects a chosen traversal orientation and is not canonical.

## Main definitions

* `SimpleWalk.IsCycle` — a closed simple walk whose dropped-tail walk is a path.
* `SimpleCycle` — a simple walk bundled with a proof of `SimpleWalk.IsCycle`.
* `SimpleCycle.interior` — the simple path obtained by dropping the repeated endpoint.
* `SimpleCycle.reverse`, `SimpleCycle.reroot` — change the chosen traversal or root.
* `SimpleCycle.ofPathClosing` — close one path to form a cycle.
* `SimpleCycle.ofInternallyDisjointPaths` — form a cycle from internally disjoint paths.
* `SimpleCycle.ofTwoPaths` — select a cycle from two distinct paths with common endpoints.

## Main results

* `SimpleCycle.edges_nodup` — a simple cycle traverses no edge twice.
* `SimpleCycle.length_ofTwoPaths` — the selected cycle is no longer than the input paths.
* `SimpleCycle.head_ofTwoPaths_mem_left` — the selected root lies on the first path.
* `SimpleCycle.edges_ofTwoPaths_subset` — every selected edge comes from an input path.
-/

namespace GraphLib

variable {α : Type*}

namespace SimpleWalk

/-- A simple walk is a cycle when it is closed, has length at least three,
and its dropped-tail walk is a path. -/
@[grind] def IsCycle (w : SimpleWalk α) : Prop :=
  3 ≤ w.length ∧ w.closed ∧ w.dropTail.nodup

namespace IsCycle

/-- Reversal preserves the simple-cycle property. -/
lemma reverse (w : SimpleWalk α) (h : IsCycle w) :
    IsCycle w.reverse := by
  obtain ⟨hlen, hclosed, hnodup⟩ := h
  exact ⟨by simpa using hlen, by simpa [VertexSeq.closed] using hclosed.symm,
    VertexSeq.nodup_reverse_dropTail_of_closed w.val hclosed hnodup⟩

end IsCycle

end SimpleWalk

/-- A simple cycle is a simple walk that is a cycle. -/
def SimpleCycle (α : Type*) :=
  { w : SimpleWalk α // SimpleWalk.IsCycle w }

namespace SimpleCycle

/-! ## Basic accessors -/

/-- The underlying simple walk. -/
abbrev val (c : SimpleCycle α) : SimpleWalk α := c.1

/-- The underlying vertex sequence. -/
abbrev vertices (c : SimpleCycle α) : VertexSeq α := c.val.val

/-- The list of vertices visited by the cycle. -/
abbrev support (c : SimpleCycle α) : List α := (vertices c).toList

/-- The unordered edges traversed by the cycle. -/
abbrev edges (c : SimpleCycle α) : List (Sym2 α) := (vertices c).edges

/-- The directed arcs traversed by the cycle. -/
abbrev arcs (c : SimpleCycle α) : List (α × α) := (vertices c).arcs

/-- The first vertex of the cycle. -/
abbrev head (c : SimpleCycle α) : α := (vertices c).head

/-- The last vertex of the cycle (equal to its head, since a cycle is closed). -/
abbrev tail (c : SimpleCycle α) : α := (vertices c).tail

/-- The number of edges in the cycle. -/
abbrev length (c : SimpleCycle α) : ℕ := (vertices c).length

/-- A cycle is closed: its first and last vertex coincide. -/
lemma closed (c : SimpleCycle α) : c.val.closed := c.2.2.1

/-- A simple cycle is, in particular, a simple walk. -/
instance : Coe (SimpleCycle α) (SimpleWalk α) :=
  ⟨val⟩

/-! ## interior -/

/-- The interior of the cycle: the vertex sequence with its final (repeated)
vertex dropped. -/
def interior (c : SimpleCycle α) : SimplePath α :=
  ⟨c.val.dropTail, c.2.2.2⟩

attribute [simp, grind] SimpleCycle.val SimpleCycle.vertices SimpleCycle.support
  SimpleCycle.edges SimpleCycle.arcs SimpleCycle.head SimpleCycle.tail SimpleCycle.length
  SimpleCycle.interior

/-! ## Constructors -/

/-! ### ofPathClosing -/

/-- The simple walk obtained by appending the starting vertex to a path of
length at least two. -/
private def walkOfPathClosing (p : SimplePath α) (hlen : 2 ≤ p.vertices.length) :
    SimpleWalk α :=
  ⟨VertexSeq.cons p.vertices p.head, ⟨p.val.nonstalling, fun h => by
    have hzero := VertexSeq.length_zero_of_nodup_closed p.vertices p.nodup
      (show p.vertices.closed from h.symm)
    omega⟩⟩

/-- Closing a path of length at least two satisfies the cycle conditions. -/
private lemma isCycle_ofPathClosing (p : SimplePath α)
    (hlen : 2 ≤ p.vertices.length) :
    SimpleWalk.IsCycle (walkOfPathClosing p hlen) := by
  change 3 ≤ (VertexSeq.cons p.vertices p.head).length ∧
    (VertexSeq.cons p.vertices p.head).closed ∧
    (VertexSeq.cons p.vertices p.head).dropTail.nodup
  refine ⟨?_, by simp [VertexSeq.closed], by simpa using p.nodup⟩
  simp [VertexSeq.length] at hlen ⊢
  omega

/-- Close a simple path by adding an edge from its tail back to its head. -/
def ofPathClosing (p : SimplePath α)
    (hlen : 2 ≤ (SimplePath.vertices p).length) :
    SimpleCycle α :=
  ⟨walkOfPathClosing p hlen, isCycle_ofPathClosing p hlen⟩

/-! ### ofInternallyDisjointPaths -/

/-- Two paths with the same tail can be glued after reversing the second one. -/
private lemma tail_eq_head_reverse_of_tail_eq (P Q : SimplePath α)
    (htail : P.tail = Q.tail) : P.val.tail = Q.val.reverse.head := by
  simpa using htail

/-- The walk obtained by following two internally disjoint paths in opposite
directions is a simple cycle. -/
private lemma isCycle_ofInternallyDisjointPaths (P Q : SimplePath α)
    (hhead : P.head = Q.head) (htail : P.tail = Q.tail)
    (hab : P.head ≠ P.tail)
    (hint : ∀ z, z ∈ P.vertices → z ∈ Q.vertices →
      z = P.head ∨ z = P.tail)
    (hlen : 3 ≤ P.length + Q.length) :
    SimpleWalk.IsCycle
      (SimpleWalk.glue P.val Q.val.reverse
        (tail_eq_head_reverse_of_tail_eq P Q htail)) := by
  have hPpos : P.vertices.length ≠ 0 := fun h0 =>
    hab (VertexSeq.head_eq_tail_of_length_zero P.vertices h0)
  have hQpos : Q.vertices.length ≠ 0 := fun h0 =>
    hab (hhead.trans ((VertexSeq.head_eq_tail_of_length_zero Q.vertices h0).trans htail.symm))
  have hQrevPos : Q.vertices.reverse.length ≠ 0 := by simpa using hQpos
  have hQrevNodup := VertexSeq.nodup_reverse Q.vertices Q.nodup
  have hdisj : ∀ z : α, z ∈ P.vertices.dropTail →
      z ∈ Q.vertices.reverse.dropTail → False := by
    intro z hzP hzQ
    have hzP2 := VertexSeq.dropTail_subset P.vertices z hzP
    have hzQ2 : z ∈ Q.vertices :=
      VertexSeq.mem_reverse.1
        (VertexSeq.dropTail_subset Q.vertices.reverse z hzQ)
    have hPt := VertexSeq.tail_not_mem_dropTail_of_nodup P.vertices P.nodup hPpos
    have hQt := VertexSeq.tail_not_mem_dropTail_of_nodup Q.vertices.reverse
      hQrevNodup hQrevPos
    have hQrt : Q.vertices.reverse.tail = Q.head := VertexSeq.tail_reverse Q.vertices
    grind [hint z hzP2 hzQ2]
  unfold SimpleWalk.glue
  rw [dif_neg hPpos]
  refine ⟨?_, ?_, ?_⟩
  · change 3 ≤ (P.vertices.dropTail.append Q.vertices.reverse).length
    have := VertexSeq.length_dropTail_succ P.vertices hPpos
    change 3 ≤ P.vertices.length + Q.vertices.length at hlen
    rw [VertexSeq.length_append, VertexSeq.length_reverse]
    omega
  · change (P.vertices.dropTail.append Q.vertices.reverse).closed
    simp [VertexSeq.closed, hhead]
  · change (P.vertices.dropTail.append Q.vertices.reverse).dropTail.nodup
    rw [VertexSeq.dropTail_append P.vertices.dropTail Q.vertices.reverse hQrevPos]
    exact VertexSeq.nodup_append _ _ (VertexSeq.nodup_dropTail P.vertices P.nodup)
      (VertexSeq.nodup_dropTail _ hQrevNodup) hdisj

/-- Construct a simple cycle by following one internally disjoint path and
returning along the reverse of the other. -/
def ofInternallyDisjointPaths (P Q : SimplePath α)
    (hhead : P.head = Q.head) (htail : P.tail = Q.tail)
    (hab : P.head ≠ P.tail)
    (hint : ∀ z, z ∈ P.vertices → z ∈ Q.vertices →
      z = P.head ∨ z = P.tail)
    (hlen : 3 ≤ P.length + Q.length) : SimpleCycle α :=
  ⟨SimpleWalk.glue P.val Q.val.reverse
      (tail_eq_head_reverse_of_tail_eq P Q htail),
    isCycle_ofInternallyDisjointPaths P Q hhead htail hab hint hlen⟩

/-- The length of the cycle obtained from two internally disjoint paths is the
sum of the two path lengths. -/
@[simp] lemma length_ofInternallyDisjointPaths (P Q : SimplePath α)
    (hhead : P.head = Q.head) (htail : P.tail = Q.tail)
    (hab : P.head ≠ P.tail)
    (hint : ∀ z, z ∈ P.vertices → z ∈ Q.vertices →
      z = P.head ∨ z = P.tail)
    (hlen : 3 ≤ P.length + Q.length) :
    (ofInternallyDisjointPaths P Q hhead htail hab hint hlen).length =
      P.length + Q.length := by
  have hPpos : P.vertices.length ≠ 0 := fun h0 =>
    hab (VertexSeq.head_eq_tail_of_length_zero P.vertices h0)
  unfold ofInternallyDisjointPaths SimpleWalk.glue
  grind [VertexSeq.length_append, VertexSeq.length_reverse,
    VertexSeq.length_dropTail_succ]

/-- The cycle from two internally disjoint paths is rooted at the head they
share: the traversal starts along `P`. -/
@[simp] lemma head_ofInternallyDisjointPaths (P Q : SimplePath α)
    (hhead : P.head = Q.head) (htail : P.tail = Q.tail)
    (hab : P.head ≠ P.tail)
    (hint : ∀ z, z ∈ P.vertices → z ∈ Q.vertices →
      z = P.head ∨ z = P.tail)
    (hlen : 3 ≤ P.length + Q.length) :
    (ofInternallyDisjointPaths P Q hhead htail hab hint hlen).head = P.head := by
  have hPpos : P.length ≠ 0 := fun h0 =>
    hab (VertexSeq.head_eq_tail_of_length_zero P.vertices h0)
  change (P.val.glue Q.val.reverse
    (tail_eq_head_reverse_of_tail_eq P Q htail)).head = P.head
  unfold SimpleWalk.glue
  rw [dif_neg hPpos]
  change (P.vertices.dropTail.append Q.vertices.reverse).head = P.vertices.head
  rw [VertexSeq.head_append, VertexSeq.head_dropTail]

/-- Every edge of the cycle from two internally disjoint paths is traversed by
one of them: the return leg only reverses `Q`, which leaves its edge set alone. -/
lemma edges_ofInternallyDisjointPaths_subset (P Q : SimplePath α)
    (hhead : P.head = Q.head) (htail : P.tail = Q.tail)
    (hab : P.head ≠ P.tail)
    (hint : ∀ z, z ∈ P.vertices → z ∈ Q.vertices →
      z = P.head ∨ z = P.tail)
    (hlen : 3 ≤ P.length + Q.length) {e : Sym2 α}
    (he : e ∈ (ofInternallyDisjointPaths P Q hhead htail hab hint hlen).edges) :
    e ∈ P.edges ∨ e ∈ Q.edges := by
  change e ∈ (P.val.glue Q.val.reverse
    (tail_eq_head_reverse_of_tail_eq P Q htail)).edges at he
  rw [SimpleWalk.edges_glue, List.mem_append] at he
  rcases he with heP | heQ
  · exact Or.inl heP
  · exact Or.inr (by grind [VertexSeq.edges_reverse])

/-! ### ofTwoPaths -/

/-- The vertex where two paths with a common head diverge: the last vertex of the
longest common prefix of their vertex lists.

Defined via `GraphLib.List.commonPrefix`, so no index arithmetic is involved. Compare the
earlier `findIdx`-on-`zip` definition, which forced every downstream lemma to
carry dependent `getElem` bounds. -/
private def divergenceVertex [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) : α :=
  (GraphLib.List.commonPrefix p.vertices.toList q.vertices.toList).getLast
    (GraphLib.List.commonPrefix_ne_nil (x := p.head) (by grind) (by grind))

/-- The three facts that make the divergence vertex what it is: the two suffixes
from it end together, it is not that common endpoint, and the two paths take
different next steps out of it. -/
private lemma divergenceVertex_core [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    let a := divergenceVertex p q hhead
    ∃ hap : a ∈ p.vertices, ∃ haq : a ∈ q.vertices,
      (p.suffixFrom a hap).tail = (q.suffixFrom a haq).tail ∧
      a ≠ (p.suffixFrom a hap).tail ∧
      (p.suffixFrom a hap).vertices.dropHead.head ≠
        (q.suffixFrom a haq).vertices.dropHead.head := by
  classical
  have hnp : p.vertices.toList.Nodup := (VertexSeq.nodup_iff_toList_nodup _).1 p.nodup
  have hnq : q.vertices.toList.Nodup := (VertexSeq.nodup_iff_toList_nodup _).1 q.nodup
  obtain ⟨r₁, r₂, h₁, h₂, hdiff⟩ :=
    GraphLib.List.commonPrefix_split p.vertices.toList q.vertices.toList
  have hcne : GraphLib.List.commonPrefix p.vertices.toList q.vertices.toList ≠ [] :=
    GraphLib.List.commonPrefix_ne_nil (x := p.head) (by grind) (by grind)
  set c := GraphLib.List.commonPrefix p.vertices.toList q.vertices.toList with hc
  set a := divergenceVertex p q hhead with hadefa
  have hadef : a = c.getLast hcne := rfl
  have hsplitc : c.dropLast ++ [a] = c := by
    rw [hadef]; exact List.dropLast_append_getLast hcne
  have hlp : p.vertices.toList = c.dropLast ++ a :: r₁ := by grind
  have hlq : q.vertices.toList = c.dropLast ++ a :: r₂ := by grind
  have hap : a ∈ p.vertices := by grind
  have haq : a ∈ q.vertices := by grind
  have hsp : (p.vertices.suffixFrom a hap).toList = a :: r₁ :=
    VertexSeq.toList_suffixFrom_eq_of_split _ p.nodup a hap _ _ hlp
  have hsq : (q.vertices.suffixFrom a haq).toList = a :: r₂ :=
    VertexSeq.toList_suffixFrom_eq_of_split _ q.nodup a haq _ _ hlq
  -- Each path ends at the last entry of its own `a :: rᵢ`; establish this once.
  have htp : p.vertices.tail = (a :: r₁).getLast (by simp) := by
    rw [← VertexSeq.getLast_toList p.vertices (by grind)]
    grind
  have htq : q.vertices.tail = (a :: r₂).getLast (by simp) := by
    rw [← VertexSeq.getLast_toList q.vertices (by grind)]
    grind
  -- Both remainders are non-empty: otherwise one vertex list is a prefix of the
  -- other, and a shared last vertex plus `nodup` would force the two paths to be
  -- equal, contradicting `hne`.
  have hr₁ : r₁ ≠ [] := by
    rintro rfl
    have hr₂ : r₂ = [] := by
      rcases r₂ with _ | ⟨y, ys⟩
      · rfl
      · exfalso
        have hmem := List.getLast_mem (l := y :: ys) (by simp)
        grind [List.getLast_cons, List.nodup_append]
    exact hne (VertexSeq.toList_injective (by grind))
  have hr₂ : r₂ ≠ [] := by
    rintro rfl
    have hmem := List.getLast_mem (l := r₁) hr₁
    grind [List.getLast_cons, List.nodup_append]
  have hane : a ∉ r₁ := by grind [List.nodup_append]
  refine ⟨hap, haq, by grind [VertexSeq.tail_suffixFrom], ?_, ?_⟩
  · have hmem := List.getLast_mem (l := r₁) hr₁
    grind [VertexSeq.tail_suffixFrom, List.getLast_cons]
  · have hd₁ := VertexSeq.head_dropHead_of_toList_eq_cons_cons _ a (r₁.head hr₁) r₁.tail
      (by rw [hsp, List.cons_head_tail hr₁])
    have hd₂ := VertexSeq.head_dropHead_of_toList_eq_cons_cons _ a (r₂.head hr₂) r₂.tail
      (by rw [hsq, List.cons_head_tail hr₂])
    have := hdiff (r₁.head hr₁) (by grind [List.head?_eq_some_head]) (r₂.head hr₂)
      (by grind [List.head?_eq_some_head])
    grind

/-- The full divergence specification used by `buildOfTwoPaths`. The four extra
components are routine consequences of `divergenceVertex_core`. -/
private lemma divergenceVertex_spec [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    let a := divergenceVertex p q hhead
    ∃ hap : a ∈ p.vertices, ∃ haq : a ∈ q.vertices,
      let p' := p.suffixFrom a hap
      let q' := q.suffixFrom a haq
      p'.head = a ∧ q'.head = a ∧ p'.tail = q'.tail ∧
        p'.length ≠ 0 ∧ q'.length ≠ 0 ∧ a ≠ p'.tail ∧
        p'.vertices.dropHead.head ≠ q'.vertices.dropHead.head := by
  obtain ⟨hap, haq, htaileq, hane, hsecond⟩ := divergenceVertex_core p q hhead htail hne
  refine ⟨hap, haq, ?_, ?_, htaileq, ?_, ?_, hane, hsecond⟩ <;>
    grind [VertexSeq.head_suffixFrom]

private lemma divergenceVertex_mem_left [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    divergenceVertex p q hhead ∈ p.vertices :=
  (divergenceVertex_core p q hhead htail hne).1

private lemma divergenceVertex_mem_right [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    divergenceVertex p q hhead ∈ q.vertices :=
  (divergenceVertex_core p q hhead htail hne).2.1

private def firstRejoinVertex [DecidableEq α] (a : α) (p q : SimplePath α)
    (hwit : ∃ z ∈ p.vertices.toList, ¬(z = a ∨ z ∉ q.vertices)) : α :=
  (p.vertices.dropWhile (fun z => z = a ∨ z ∉ q.vertices) hwit).head

private lemma firstRejoinVertex_spec [DecidableEq α] (a : α) (p q : SimplePath α)
    (hpa : p.head = a) (hqa : q.head = a)
    (hsecond : p.vertices.dropHead.head ≠ q.vertices.dropHead.head)
    (hwit : ∃ z ∈ p.vertices.toList, ¬(z = a ∨ z ∉ q.vertices)) :
    let b := firstRejoinVertex a p q hwit
    ∃ hbP : b ∈ p.vertices, ∃ hbQ : b ∈ q.vertices,
      let P := p.prefixUntil b hbP
      let Q := q.prefixUntil b hbQ
      P.head = Q.head ∧ P.tail = Q.tail ∧ P.head ≠ P.tail ∧
        (∀ z, z ∈ P.vertices → z ∈ Q.vertices →
          z = P.head ∨ z = P.tail) ∧
        3 ≤ P.length + Q.length := by
  let pred : α → Prop := fun z => z = a ∨ z ∉ q.vertices
  let r := p.vertices.dropWhile pred hwit
  let b := firstRejoinVertex a p q hwit
  have hbP : b ∈ p.vertices :=
    VertexSeq.dropWhile_subset p.vertices pred hwit _ (VertexSeq.head_mem r)
  have hbNot : ¬pred b := VertexSeq.not_pred_head_dropWhile p.vertices pred hwit
  have hba : b ≠ a := fun h => hbNot (Or.inl h)
  have hbQ : b ∈ q.vertices := by by_contra h; exact hbNot (Or.inr h)
  refine ⟨hbP, hbQ, ?_⟩
  let P := p.prefixUntil b hbP
  let Q := q.prefixUntil b hbQ
  have hPhead : P.head = a := (VertexSeq.head_prefixUntil p.vertices b hbP).trans hpa
  have hQhead : Q.head = a := (VertexSeq.head_prefixUntil q.vertices b hbQ).trans hqa
  have hPtail : P.tail = b := VertexSeq.tail_prefixUntil p.vertices b hbP
  have hQtail : Q.tail = b := VertexSeq.tail_prefixUntil q.vertices b hbQ
  have hPpos : P.length ≠ 0 :=
    VertexSeq.length_prefixUntil_ne_zero p.vertices b hbP (by grind)
  have hQpos : Q.length ≠ 0 :=
    VertexSeq.length_prefixUntil_ne_zero q.vertices b hbQ (by grind)
  refine ⟨hPhead.trans hQhead.symm, hPtail.trans hQtail.symm,
    fun heq => hba (hPtail.symm.trans (heq.symm.trans hPhead)), ?_, ?_⟩
  · intro z hzP hzQ
    have hzQ' : z ∈ q.vertices := VertexSeq.prefixUntil_subset q.vertices b hbQ z hzQ
    have hzFirst := VertexSeq.eq_head_dropWhile_or_pred_of_mem_prefixUntil
      p.vertices pred hwit (z := z) (by simpa [P, b, r, pred] using hzP)
    rcases hzFirst with hzb | hza | hznot
    · exact Or.inr (hzb.trans hPtail.symm)
    · exact Or.inl (hza.trans hPhead.symm)
    · exact (hznot hzQ').elim
  · by_contra h3
    change ¬3 ≤ P.length + Q.length at h3
    have hP1 : P.length = 1 := by omega
    have hQ1 : Q.length = 1 := by omega
    exact hsecond
      ((VertexSeq.head_dropHead_prefixUntil_of_length_one p.vertices b hbP hP1).trans
        (VertexSeq.head_dropHead_prefixUntil_of_length_one q.vertices b hbQ hQ1).symm)

private lemma firstRejoinVertex_mem_left [DecidableEq α] (a : α)
    (p q : SimplePath α)
    (hwit : ∃ z ∈ p.vertices.toList, ¬(z = a ∨ z ∉ q.vertices)) :
    firstRejoinVertex a p q hwit ∈ p.vertices := by
  exact VertexSeq.dropWhile_subset p.vertices (fun z => z = a ∨ z ∉ q.vertices)
    hwit _ (VertexSeq.head_mem _)

private lemma firstRejoinVertex_mem_right [DecidableEq α] (a : α)
    (p q : SimplePath α)
    (hwit : ∃ z ∈ p.vertices.toList, ¬(z = a ∨ z ∉ q.vertices)) :
    firstRejoinVertex a p q hwit ∈ q.vertices := by
  have hnot := VertexSeq.not_pred_head_dropWhile p.vertices
    (fun z => z = a ∨ z ∉ q.vertices) hwit
  by_contra h
  exact hnot (Or.inr h)

private structure OfTwoPathsData (p q : SimplePath α) where
  cycle : SimpleCycle α
  length_le : cycle.length ≤ p.length + q.length
  head_mem_left : cycle.head ∈ p.vertices
  edges_subset : ∀ e ∈ cycle.edges, e ∈ p.edges ∨ e ∈ q.edges

private def buildOfTwoPaths [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) : OfTwoPathsData p q := by
  let a := divergenceVertex p q hhead
  let hap := divergenceVertex_mem_left p q hhead htail hne
  let haq := divergenceVertex_mem_right p q hhead htail hne
  let p' := p.suffixFrom a hap
  let q' := q.suffixFrom a haq
  have hd : p'.head = a ∧ q'.head = a ∧ p'.tail = q'.tail ∧
      p'.length ≠ 0 ∧ q'.length ≠ 0 ∧ a ≠ p'.tail ∧
      p'.vertices.dropHead.head ≠ q'.vertices.dropHead.head := by
    obtain ⟨hap', haq', h⟩ := divergenceVertex_spec p q hhead htail hne
    simpa [a, p', q'] using h
  obtain ⟨hpHead, hqHead, hpTail, -, -, haTail, hsecond⟩ := hd
  have hwit : ∃ z ∈ p'.vertices.toList, ¬(z = a ∨ z ∉ q'.vertices) :=
    ⟨p'.tail, VertexSeq.tail_mem p'.vertices, by
      rintro (hta | htq)
      · exact haTail hta.symm
      · exact htq (hpTail.symm ▸ VertexSeq.tail_mem q'.vertices)⟩
  let b := firstRejoinVertex a p' q' hwit
  let hbP := firstRejoinVertex_mem_left a p' q' hwit
  let hbQ := firstRejoinVertex_mem_right a p' q' hwit
  let P := p'.prefixUntil b hbP
  let Q := q'.prefixUntil b hbQ
  have hr : P.head = Q.head ∧ P.tail = Q.tail ∧ P.head ≠ P.tail ∧
      (∀ z, z ∈ P.vertices → z ∈ Q.vertices →
        z = P.head ∨ z = P.tail) ∧ 3 ≤ P.length + Q.length := by
    obtain ⟨hbP', hbQ', h⟩ :=
      firstRejoinVertex_spec a p' q' hpHead hqHead hsecond hwit
    simpa [b, P, Q] using h
  obtain ⟨hPQHead, hPQTail, hPNe, hint, hlen⟩ := hr
  refine ⟨ofInternallyDisjointPaths P Q hPQHead hPQTail hPNe hint hlen, ?_, ?_, ?_⟩
  · change (ofInternallyDisjointPaths P Q hPQHead hPQTail hPNe hint hlen).length ≤ _
    rw [length_ofInternallyDisjointPaths]
    have hPle : P.length ≤ p'.length := VertexSeq.length_prefixUntil_le p'.vertices b hbP
    have hQle : Q.length ≤ q'.length := VertexSeq.length_prefixUntil_le q'.vertices b hbQ
    have hp'le : p'.length ≤ p.length := VertexSeq.length_suffixFrom_le p.vertices a hap
    have hq'le : q'.length ≤ q.length := VertexSeq.length_suffixFrom_le q.vertices a haq
    omega
  · rw [head_ofInternallyDisjointPaths]
    exact VertexSeq.suffixFrom_subset p.vertices a hap _
      (VertexSeq.prefixUntil_subset p'.vertices b hbP _ (VertexSeq.head_mem P.vertices))
  · intro e he
    rcases edges_ofInternallyDisjointPaths_subset P Q hPQHead hPQTail hPNe hint hlen he
      with heP | heQ
    · exact Or.inl (SimplePath.edges_suffixFrom_subset p a hap
        (SimplePath.edges_prefixUntil_subset p' b hbP heP))
    · exact Or.inr (SimplePath.edges_suffixFrom_subset q a haq
        (SimplePath.edges_prefixUntil_subset q' b hbQ heQ))

/-- Two distinct simple paths with the same endpoints determine a simple cycle
by taking the segment between their first divergence and first reconvergence. -/
def ofTwoPaths [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) : SimpleCycle α :=
  (buildOfTwoPaths p q hhead htail hne).cycle

/-- The cycle selected from two distinct paths is no longer than the two paths
combined. -/
lemma length_ofTwoPaths [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    (ofTwoPaths p q hhead htail hne).length ≤ p.length + q.length :=
  (buildOfTwoPaths p q hhead htail hne).length_le

/-- The selected cycle is rooted at a vertex of the first path. -/
lemma head_ofTwoPaths_mem_left [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) :
    (ofTwoPaths p q hhead htail hne).head ∈ p.vertices :=
  (buildOfTwoPaths p q hhead htail hne).head_mem_left

/-- Every edge of the selected cycle comes from one of the two input paths. -/
lemma edges_ofTwoPaths_subset [DecidableEq α] (p q : SimplePath α)
    (hhead : p.head = q.head) (htail : p.tail = q.tail)
    (hne : p.vertices ≠ q.vertices) {e : Sym2 α}
    (he : e ∈ (ofTwoPaths p q hhead htail hne).edges) :
    e ∈ p.edges ∨ e ∈ q.edges :=
  (buildOfTwoPaths p q hhead htail hne).edges_subset e he

/-! ## reverse -/

/-- Reverse the orientation of a simple cycle. -/
@[grind] def reverse (c : SimpleCycle α) : SimpleCycle α :=
  ⟨c.val.reverse, SimpleWalk.IsCycle.reverse c.val c.2⟩

/-! ## reroot -/

/-- The suffix rooted at a cycle vertex can be glued to the preceding prefix. -/
private lemma tail_suffixFrom_eq_head_prefixUntil [DecidableEq α] (c : SimpleCycle α)
    (u : α) (hu : u ∈ vertices c) :
    (c.val.suffixFrom u hu).val.tail = (c.val.prefixUntil u hu).val.head := by
  simpa using (closed c).symm

/-- Re-rooting the underlying walk of a simple cycle at a non-head vertex
preserves the cycle property. -/
private lemma isCycle_reroot_glue [DecidableEq α] (c : SimpleCycle α) (u : α)
    (hu : u ∈ vertices c) (hhead : u ≠ head c) :
    SimpleWalk.IsCycle
      ((c.val.suffixFrom u hu).glue (c.val.prefixUntil u hu)
        (tail_suffixFrom_eq_head_prefixUntil c u hu)) := by
  have hsplit := VertexSeq.dropTail_prefixUntil_append_suffixFrom
    (vertices c) u hu hhead
  let pre : VertexSeq α := (vertices c).prefixUntil u hu
  let suf : VertexSeq α := (vertices c).suffixFrom u hu
  have hpre_pos : pre.length ≠ 0 := fun hz =>
    hhead (by simpa [pre] using (VertexSeq.head_eq_tail_of_length_zero pre hz).symm)
  have hsuf_pos : suf.length ≠ 0 := by
    intro hz
    have huTail : u = (vertices c).tail := by
      simpa [suf] using VertexSeq.head_eq_tail_of_length_zero suf hz
    exact hhead (huTail.trans (closed c).symm)
  have hsplit' : pre.dropTail.append suf = vertices c := by simpa [pre, suf] using hsplit
  have hleft : (pre.dropTail.append suf.dropTail).nodup := by
    rw [← VertexSeq.dropTail_append pre.dropTail suf hsuf_pos,
      congrArg VertexSeq.dropTail hsplit']
    exact c.2.2.2
  have hsuf_pos' : ((c.val.suffixFrom u hu).val.length ≠ 0) := by simpa [suf] using hsuf_pos
  have hlenAll : pre.dropTail.length + suf.length + 1 = (vertices c).length := by
    simpa [VertexSeq.length_append] using congrArg VertexSeq.length hsplit'
  have hpreLen := VertexSeq.length_dropTail_succ pre hpre_pos
  have hsufLen := VertexSeq.length_dropTail_succ suf hsuf_pos
  have h3 : 3 ≤ (vertices c).length := c.2.1
  simp only [SimpleWalk.IsCycle, SimpleWalk.glue, hsuf_pos']
  refine ⟨?_, ?_, ?_⟩
  · change 3 ≤ (suf.dropTail.append pre).length
    rw [VertexSeq.length_append]
    omega
  · change (suf.dropTail.append pre).closed
    simp [VertexSeq.closed, pre, suf]
  · change (suf.dropTail.append pre).dropTail.nodup
    rw [VertexSeq.dropTail_append suf.dropTail pre hpre_pos]
    exact VertexSeq.nodup_append_comm pre.dropTail suf.dropTail hleft

/-- Re-root a simple cycle at any vertex on it. -/
def reroot [DecidableEq α] (c : SimpleCycle α) (u : α) (hu : u ∈ vertices c) :
    SimpleCycle α :=
  if hhead : u = head c then
    c
  else
    ⟨(c.val.suffixFrom u hu).glue (c.val.prefixUntil u hu)
        (tail_suffixFrom_eq_head_prefixUntil c u hu),
      isCycle_reroot_glue c u hu hhead⟩

/-! ## edges -/

/-- The number of traversed edges equals the cycle's length. -/
@[simp] lemma length_edges (c : SimpleCycle α) : (edges c).length = length c :=
  VertexSeq.length_edges (vertices c)

/-- A simple cycle has at least three traversed edges. -/
lemma three_le_length_edges (c : SimpleCycle α) : 3 ≤ (edges c).length := by
  rw [length_edges]
  exact c.2.1

/-- A simple cycle traverses at least one edge. -/
lemma edges_ne_nil (c : SimpleCycle α) : edges c ≠ [] := by
  grind [three_le_length_edges]

/-- The edge list is the interior path's edge list plus the closing edge. -/
lemma edges_eq_interior_concat (c : SimpleCycle α) :
    edges c = SimplePath.edges (interior c) ++ [s(SimplePath.tail (interior c), tail c)] := by
  have hpos : (vertices c).length ≠ 0 := by grind
  simpa [List.concat_eq_append] using VertexSeq.edges_eq_dropTail_concat (vertices c) hpos

/-- A simple cycle traverses each edge at most once. -/
lemma edges_nodup (c : SimpleCycle α) : (edges c).Nodup := by
  rw [edges_eq_interior_concat, List.nodup_append]
  refine ⟨SimplePath.edges_nodup (interior c), by simp, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_singleton] at hb
  subst hb; subst hab
  have hclosedTail : tail c = SimplePath.head (interior c) := by
    grind [VertexSeq.head_dropTail, closed]
  rw [hclosedTail] at ha
  have hle := VertexSeq.length_le_one_of_closing_edge_mem_swap
    (SimplePath.vertices (interior c)) (SimplePath.nodup (interior c)) ha
  have hlen : 3 ≤ (vertices c).length := c.2.1
  have hdrop := VertexSeq.length_dropTail_succ (vertices c) (by omega)
  change (vertices c).dropTail.length ≤ 1 at hle
  omega

/-- Reversal reverses the edge list. -/
@[simp] lemma edges_reverse (c : SimpleCycle α) :
    edges (reverse c) = (edges c).reverse :=
  VertexSeq.edges_reverse (vertices c)

/-! ## arcs -/

/-- The number of traversed arcs equals the cycle's length. -/
@[simp] lemma length_arcs (c : SimpleCycle α) : (arcs c).length = length c :=
  VertexSeq.length_arcs (vertices c)

/-- A simple cycle has at least three traversed arcs. -/
lemma three_le_length_arcs (c : SimpleCycle α) : 3 ≤ (arcs c).length := by
  rw [length_arcs]
  exact c.2.1

/-- A simple cycle traverses at least one arc. -/
lemma arcs_ne_nil (c : SimpleCycle α) : arcs c ≠ [] := by
  grind [three_le_length_arcs]

/-- The arc list is the interior path's arc list plus the closing arc. -/
lemma arcs_eq_interior_concat (c : SimpleCycle α) :
    arcs c =
      SimplePath.arcs (interior c) ++ [(SimplePath.tail (interior c), tail c)] := by
  have hpos : (vertices c).length ≠ 0 := by grind
  simpa [List.concat_eq_append] using VertexSeq.arcs_eq_dropTail_concat (vertices c) hpos

/-- A simple cycle traverses each directed arc at most once. -/
lemma arcs_nodup (c : SimpleCycle α) : (arcs c).Nodup := by
  rw [arcs_eq_interior_concat, List.nodup_append]
  refine ⟨SimplePath.arcs_nodup (interior c), by simp, ?_⟩
  have hclosedTail : tail c = SimplePath.head (interior c) := by
    grind [VertexSeq.head_dropTail, closed]
  have hlen : 3 ≤ (vertices c).length := c.2.1
  have hdrop := VertexSeq.length_dropTail_succ (vertices c) (by omega)
  grind [VertexSeq.length_le_one_of_closing_arc_mem]

/-- Reversal reverses the arc list and swaps every arc's endpoints. -/
@[simp] lemma arcs_reverse (c : SimpleCycle α) :
    arcs (reverse c) = (arcs c).reverse.map (fun a : α × α => (a.2, a.1)) :=
  VertexSeq.arcs_reverse (vertices c)

end SimpleCycle

end GraphLib
