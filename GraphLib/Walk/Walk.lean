/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Graph.Basic
import GraphLib.Walk.VertexSeq

/-!
# General graph-independent walks

A `Walk α β` is a nonempty alternating sequence of vertices and raw step tags. The tag stored
at a step is only a discriminator: `edges` and `arcs` reconstruct the full bundled actual edge
or arc from the tag and the adjacent vertices. In particular, one tag may soundly occur at
different endpoint pairs.

The constructor `cons w v t` extends on the right, from `w.tail` to `v`, with tag `t`.
-/

namespace GraphLib

variable {α β γ δ : Type*}

/-- A nonempty alternating sequence of vertices and raw step tags. -/
@[grind] inductive Walk (α β : Type*)
  | singleton (v : α) : Walk α β
  | cons (w : Walk α β) (v : α) (t : β) : Walk α β

instance : Snoc (Walk α β) (α × β) := ⟨fun w p => w.cons p.1 p.2⟩

namespace Walk

/-! ## Basic projections -/

/-- The number of traversal steps. -/
@[grind] def length : Walk α β → ℕ
  | .singleton _ => 0
  | .cons w _ _ => w.length + 1

/-- The first visited vertex. -/
@[grind] def head : Walk α β → α
  | .singleton v => v
  | .cons w _ _ => w.head

/-- The last visited vertex. -/
@[grind] def tail : Walk α β → α
  | .singleton v => v
  | .cons _ v _ => v

/-- The visited vertices, in traversal order. -/
@[grind] def vertices : Walk α β → List α
  | .singleton v => [v]
  | .cons w v _ => w.vertices.concat v

/-- The raw step tags, in traversal order. Tags are not actual edge identities. -/
@[grind] def tags : Walk α β → List β
  | .singleton _ => []
  | .cons w _ t => w.tags.concat t

@[simp] theorem length_singleton (v : α) : (singleton v : Walk α β).length = 0 := rfl
@[simp] theorem length_cons (w : Walk α β) (v : α) (t : β) :
    (w.cons v t).length = w.length + 1 := rfl
@[simp] theorem head_singleton (v : α) : (singleton v : Walk α β).head = v := rfl
@[simp] theorem head_cons (w : Walk α β) (v : α) (t : β) :
    (w.cons v t).head = w.head := rfl
@[simp] theorem tail_singleton (v : α) : (singleton v : Walk α β).tail = v := rfl
@[simp] theorem tail_cons (w : Walk α β) (v : α) (t : β) :
    (w.cons v t).tail = v := rfl
@[simp] theorem vertices_singleton (v : α) : (singleton v : Walk α β).vertices = [v] := rfl
@[simp] theorem vertices_cons (w : Walk α β) (v : α) (t : β) :
    (w.cons v t).vertices = w.vertices.concat v := rfl
@[simp] theorem tags_singleton (v : α) : (singleton v : Walk α β).tags = [] := rfl
@[simp] theorem tags_cons (w : Walk α β) (v : α) (t : β) :
    (w.cons v t).tags = w.tags.concat t := rfl

@[simp] theorem length_vertices (w : Walk α β) : w.vertices.length = w.length + 1 := by
  induction w <;> simp_all

@[simp] theorem length_tags (w : Walk α β) : w.tags.length = w.length := by
  induction w <;> simp_all

instance : Membership α (Walk α β) := ⟨fun w v => v ∈ w.vertices⟩

@[simp] theorem mem_def {v : α} (w : Walk α β) : v ∈ w ↔ v ∈ w.vertices := Iff.rfl

@[simp] theorem mem_singleton {u v : α} : u ∈ (singleton v : Walk α β) ↔ u = v := by
  simp [Walk.mem_def, vertices]

@[simp] theorem mem_cons (u v : α) (t : β) (w : Walk α β) :
    u ∈ w.cons v t ↔ u ∈ w ∨ u = v := by
  simp [Walk.mem_def, vertices, List.concat_eq_append]

/-- Raw tag occurrence. This deliberately does not claim edge identity. -/
def hasTag (w : Walk α β) (t : β) : Prop := t ∈ w.tags

@[simp] theorem hasTag_singleton (v : α) (t : β) : ¬ (singleton v : Walk α β).hasTag t := by
  simp [hasTag]

@[simp] theorem hasTag_cons (w : Walk α β) (v : α) (s t : β) :
    (w.cons v t).hasTag s ↔ w.hasTag s ∨ s = t := by
  simp [hasTag, List.concat_eq_append]

instance [DecidableEq α] (v : α) (w : Walk α β) : Decidable (v ∈ w) :=
  inferInstanceAs (Decidable (v ∈ w.vertices))

instance [DecidableEq β] (t : β) (w : Walk α β) : Decidable (w.hasTag t) :=
  inferInstanceAs (Decidable (t ∈ w.tags))

@[simp] theorem head_mem (w : Walk α β) : w.head ∈ w := by
  induction w <;> simp_all

@[simp] theorem tail_mem (w : Walk α β) : w.tail ∈ w := by
  cases w <;> simp

/-! ## Endpoint drops and joining -/

/-- Drop the first vertex and its outgoing tagged step. -/
@[grind] def dropHead : Walk α β → Walk α β
  | .singleton v => .singleton v
  | .cons (.singleton _) v _ => .singleton v
  | .cons w v t => .cons w.dropHead v t

/-- Drop the last vertex and its incoming tagged step. -/
@[grind] def dropTail : Walk α β → Walk α β
  | .singleton v => .singleton v
  | .cons w _ _ => w

/-! ## Subwalks and erasure -/

/-- The prefix ending at the first occurrence of `v`, inclusive. -/
@[grind] def prefixUntil [DecidableEq α] (w : Walk α β) (v : α) (_h : v ∈ w) :
    Walk α β :=
  match w with
  | .singleton x => .singleton x
  | .cons q x t =>
      if hq : v ∈ q then prefixUntil q v hq else .cons q x t

/-- The suffix starting at the first occurrence of `v`, inclusive. -/
@[grind] def suffixFrom [DecidableEq α] (w : Walk α β) (v : α) (_h : v ∈ w) :
    Walk α β :=
  match w with
  | .singleton x => .singleton x
  | .cons q x t =>
      if hq : v ∈ q then .cons (suffixFrom q v hq) x t else .singleton x

@[simp] theorem length_prefixUntil_le [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).length ≤ w.length := by
  fun_induction prefixUntil w v h <;> grind

@[simp] theorem length_suffixFrom_le [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).length ≤ w.length := by
  fun_induction suffixFrom w v h <;> grind

@[simp] theorem head_prefixUntil [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).head = w.head := by
  fun_induction prefixUntil w v h <;> grind

@[simp] theorem tail_prefixUntil [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).tail = v := by
  fun_induction prefixUntil w v h <;> grind [Walk.mem_def, vertices]

@[simp] theorem head_suffixFrom [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).head = v := by
  fun_induction suffixFrom w v h <;> grind [Walk.mem_def, vertices]

@[simp] theorem tail_suffixFrom [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).tail = w.tail := by
  fun_induction suffixFrom w v h <;> grind

/-- Take every vertex satisfying `p`, plus the first vertex that fails it, if one exists. -/
@[grind] def takeWhile (w : Walk α β) (p : α → Prop) [DecidablePred p] : Walk α β :=
  match w with
  | .singleton x => .singleton x
  | .cons q x t =>
      if ∃ v ∈ q.vertices, ¬ p v then takeWhile q p else .cons q x t

/-- Drop the longest prefix on which `p` holds, starting at the first failure. -/
@[grind] def dropWhile (w : Walk α β) (p : α → Prop) [DecidablePred p]
    (_h : ∃ v ∈ w.vertices, ¬ p v) : Walk α β :=
  match w with
  | .singleton x => .singleton x
  | .cons q x t =>
      if hq : ∃ v ∈ q.vertices, ¬ p v then .cons (dropWhile q p hq) x t
      else .singleton x

/-- Erase immediate stalls. -/
@[grind] def loopErase [DecidableEq α] : Walk α β → Walk α β
  | .singleton v => .singleton v
  | .cons w v t =>
      if w.tail = v then loopErase w else .cons (loopErase w) v t

/-- Erase cycles by cutting back to the first occurrence of a repeated vertex. -/
@[grind] def cycleErase [DecidableEq α] : Walk α β → Walk α β
  | .singleton v => .singleton v
  | .cons w v t =>
      if h : v ∈ w then cycleErase (prefixUntil w v h)
      else .cons (cycleErase w) v t
  termination_by w => w.length
  decreasing_by
  · simp [length]
    grind [length_prefixUntil_le]
  · simp [length]

/-- Append `q` after `p`, using `t` for the new step from `p.tail` to `q.head`. -/
@[grind] def append (p q : Walk α β) (t : β) : Walk α β :=
  match q with
  | .singleton v => p.cons v t
  | .cons q' v s => (append p q' t).cons v s

/-- Glue two walks whose endpoints agree, retaining every existing tagged step exactly once. -/
def glue (p q : Walk α β) (_h : p.tail = q.head) : Walk α β :=
  match p with
  | .singleton _ => q
  | .cons p' _ t => p'.append q t

@[simp] theorem length_append (p q : Walk α β) (t : β) :
    (p.append q t).length = p.length + q.length + 1 := by
  induction q <;> simp_all [append, Nat.add_assoc]

@[simp] theorem head_append (p q : Walk α β) (t : β) :
    (p.append q t).head = p.head := by induction q <;> simp_all [append]

@[simp] theorem tail_append (p q : Walk α β) (t : β) :
    (p.append q t).tail = q.tail := by induction q <;> simp_all [append]

@[simp] theorem vertices_append (p q : Walk α β) (t : β) :
    (p.append q t).vertices = p.vertices ++ q.vertices := by
  induction q <;> simp_all [append, List.concat_eq_append, List.append_assoc]

@[simp] theorem tags_append (p q : Walk α β) (t : β) :
    (p.append q t).tags = p.tags ++ [t] ++ q.tags := by
  induction q <;> simp_all [append, List.concat_eq_append, List.append_assoc]

@[simp] theorem length_glue (p q : Walk α β) (h : p.tail = q.head) :
    (p.glue q h).length = p.length + q.length := by
  cases p <;> simp [glue] <;> omega

@[simp] theorem head_glue (p q : Walk α β) (h : p.tail = q.head) :
    (p.glue q h).head = p.head := by
  cases p with
  | singleton v => simpa [glue] using h.symm
  | cons p v t => simp [glue]

@[simp] theorem tail_glue (p q : Walk α β) (h : p.tail = q.head) :
    (p.glue q h).tail = q.tail := by cases p <;> simp [glue]

@[simp] theorem tags_glue (p q : Walk α β) (h : p.tail = q.head) :
    (p.glue q h).tags = p.tags ++ q.tags := by
  cases p <;> simp [glue, List.concat_eq_append, List.append_assoc]

/-! ## Reversal -/

/-- Reverse the traversal while leaving its raw tags unchanged. -/
@[grind] def reverse : Walk α β → Walk α β
  | .singleton v => .singleton v
  | .cons w v t => (singleton v).append w.reverse t

@[simp] theorem length_reverse (w : Walk α β) : w.reverse.length = w.length := by
  induction w <;> simp_all [reverse]

@[simp] theorem head_reverse (w : Walk α β) : w.reverse.head = w.tail := by
  induction w <;> simp_all [reverse]

@[simp] theorem tail_reverse (w : Walk α β) : w.reverse.tail = w.head := by
  induction w <;> simp_all [reverse]

@[simp] theorem vertices_reverse (w : Walk α β) : w.reverse.vertices = w.vertices.reverse := by
  induction w <;> simp_all [reverse, List.concat_eq_append]

@[simp] theorem tags_reverse (w : Walk α β) : w.reverse.tags = w.tags.reverse := by
  induction w <;> simp_all [reverse, List.concat_eq_append]

/-- Walks are determined by their ordered vertex and tag lists. -/
@[ext] theorem ext {p q : Walk α β} (hvertices : p.vertices = q.vertices)
    (htags : p.tags = q.tags) : p = q := by
  induction p generalizing q with
  | singleton v =>
      cases q with
      | singleton u => simp_all [vertices]
      | cons q u t => simp [tags, List.concat_eq_append] at htags
  | cons p v t ih =>
      cases q with
      | singleton u => simp [tags, List.concat_eq_append] at htags
      | cons q u s =>
          have hv := (List.concat_inj.mp hvertices)
          have ht := (List.concat_inj.mp htags)
          cases hv.2
          cases ht.2
          exact congrArg (fun r => r.cons v t) (ih hv.1 ht.1)

@[simp] theorem reverse_reverse (w : Walk α β) : w.reverse.reverse = w := by
  apply Walk.ext <;> simp

/-! ## Vertex/tag maps -/

/-- Map the visited vertices, leaving raw tags unchanged. -/
def mapVertices (f : α → γ) : Walk α β → Walk γ β
  | .singleton v => .singleton (f v)
  | .cons w v t => .cons (w.mapVertices f) (f v) t

/-- Map the raw tags, leaving vertices unchanged. -/
def mapTags (g : β → δ) : Walk α β → Walk α δ
  | .singleton v => .singleton v
  | .cons w v t => .cons (w.mapTags g) v (g t)

@[simp] theorem length_mapVertices (w : Walk α β) (f : α → γ) :
    (w.mapVertices f).length = w.length := by induction w <;> simp_all [mapVertices]

@[simp] theorem head_mapVertices (w : Walk α β) (f : α → γ) :
    (w.mapVertices f).head = f w.head := by induction w <;> simp_all [mapVertices]

@[simp] theorem tail_mapVertices (w : Walk α β) (f : α → γ) :
    (w.mapVertices f).tail = f w.tail := by cases w <;> rfl

@[simp] theorem length_mapTags (w : Walk α β) (g : β → δ) :
    (w.mapTags g).length = w.length := by induction w <;> simp_all [mapTags]

@[simp] theorem head_mapTags (w : Walk α β) (g : β → δ) :
    (w.mapTags g).head = w.head := by induction w <;> simp_all [mapTags]

@[simp] theorem tail_mapTags (w : Walk α β) (g : β → δ) :
    (w.mapTags g).tail = w.tail := by cases w <;> rfl

@[simp] theorem vertices_mapVertices (w : Walk α β) (f : α → γ) :
    (w.mapVertices f).vertices = w.vertices.map f := by induction w <;> simp_all [mapVertices]

@[simp] theorem tags_mapVertices (w : Walk α β) (f : α → γ) :
    (w.mapVertices f).tags = w.tags := by induction w <;> simp_all [mapVertices]

@[simp] theorem vertices_mapTags (w : Walk α β) (g : β → δ) :
    (w.mapTags g).vertices = w.vertices := by induction w <;> simp_all [mapTags]

@[simp] theorem tags_mapTags (w : Walk α β) (g : β → δ) :
    (w.mapTags g).tags = w.tags.map g := by induction w <;> simp_all [mapTags]

@[simp] theorem mapVertices_id (w : Walk α β) : w.mapVertices id = w := by
  induction w <;> simp_all [mapVertices]

@[simp] theorem mapTags_id (w : Walk α β) : w.mapTags id = w := by
  induction w <;> simp_all [mapTags]

@[simp] theorem mapVertices_comp (w : Walk α β) (f : α → γ) (g : γ → δ) :
    (w.mapVertices f).mapVertices g = w.mapVertices (g ∘ f) := by
  induction w <;> simp_all [mapVertices]

@[simp] theorem mapTags_comp {η : Type*} (w : Walk α β) (f : β → δ) (g : δ → η) :
    (w.mapTags f).mapTags g = w.mapTags (g ∘ f) := by
  induction w <;> simp_all [mapTags]

theorem mapVertices_mapTags (w : Walk α β) (f : α → γ) (g : β → δ) :
    (w.mapVertices f).mapTags g = (w.mapTags g).mapVertices f := by
  induction w <;> simp_all [mapVertices, mapTags]

/-! ## Vertex folds and indexing -/

/-- Left fold over the visited vertices, from head to tail. -/
def foldl (f : γ → α → γ) (init : γ) : Walk α β → γ
  | .singleton v => f init v
  | .cons w v _ => f (w.foldl f init) v

/-- Right fold over the visited vertices, from tail to head. -/
def foldr (f : α → γ → γ) (init : γ) : Walk α β → γ
  | .singleton v => f v init
  | .cons w v _ => w.foldr f (f v init)

/-- Whether the predicate holds at some visited vertex. -/
def any (p : α → Prop) : Walk α β → Prop
  | .singleton v => p v
  | .cons w v _ => w.any p ∨ p v

/-- Whether the predicate holds at every visited vertex. -/
def all (p : α → Prop) : Walk α β → Prop
  | .singleton v => p v
  | .cons w v _ => w.all p ∧ p v

instance : GetElem (Walk α β) ℕ α (fun w i => i < w.vertices.length) where
  getElem w i h := w.vertices[i]

/-! ## Sequence view and predicates -/

/-- Forget the raw tags. -/
@[grind] def toVertexSeq : Walk α β → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v _ => .cons w.toVertexSeq v

@[simp] theorem toVertexSeq_toList (w : Walk α β) : w.toVertexSeq.toList = w.vertices := by
  induction w <;> simp_all [toVertexSeq, VertexSeq.toList, List.concat_eq_append]

@[simp] theorem toVertexSeq_head (w : Walk α β) : w.toVertexSeq.head = w.head := by
  induction w <;> simp_all [toVertexSeq]

@[simp] theorem toVertexSeq_tail (w : Walk α β) : w.toVertexSeq.tail = w.tail := by
  cases w <;> rfl

@[simp] theorem toVertexSeq_length (w : Walk α β) : w.toVertexSeq.length = w.length := by
  induction w <;> simp_all [toVertexSeq, VertexSeq.length] <;> omega

@[simp] theorem toVertexSeq_dropTail (w : Walk α β) :
    w.dropTail.toVertexSeq = w.toVertexSeq.dropTail := by
  cases w <;> rfl

@[simp] theorem toVertexSeq_dropHead (w : Walk α β) :
    w.dropHead.toVertexSeq = w.toVertexSeq.dropHead := by
  fun_induction dropHead <;> grind [toVertexSeq, VertexSeq.dropHead]

@[simp] theorem toVertexSeq_prefixUntil [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) :
    (w.prefixUntil v h).toVertexSeq = w.toVertexSeq.prefixUntil v (by simpa using h) := by
  fun_induction prefixUntil w v h <;>
    grind [toVertexSeq, prefixUntil, VertexSeq.prefixUntil, Walk.mem_def,
      VertexSeq.mem_def, toVertexSeq_toList]

@[simp] theorem toVertexSeq_suffixFrom [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) :
    (w.suffixFrom v h).toVertexSeq = w.toVertexSeq.suffixFrom v (by simpa using h) := by
  fun_induction suffixFrom w v h <;>
    grind [toVertexSeq, suffixFrom, VertexSeq.suffixFrom, Walk.mem_def,
      VertexSeq.mem_def, toVertexSeq_toList]

@[simp] theorem toVertexSeq_takeWhile (w : Walk α β) (p : α → Prop)
    [DecidablePred p] : (w.takeWhile p).toVertexSeq = w.toVertexSeq.takeWhile p := by
  induction w with
  | singleton _ => rfl
  | cons q x t ih =>
      simp only [takeWhile, toVertexSeq, VertexSeq.takeWhile, toVertexSeq_toList]
      split
      · exact ih
      · rfl

@[simp] theorem toVertexSeq_dropWhile (w : Walk α β) (p : α → Prop)
    [DecidablePred p] (h : ∃ v ∈ w.vertices, ¬ p v) :
    (w.dropWhile p h).toVertexSeq =
      w.toVertexSeq.dropWhile p (by simpa using h) := by
  fun_induction dropWhile w p h <;>
    grind [toVertexSeq, dropWhile, VertexSeq.dropWhile, toVertexSeq_toList]

@[simp] theorem toVertexSeq_loopErase [DecidableEq α] (w : Walk α β) :
    w.loopErase.toVertexSeq = w.toVertexSeq.loopErase := by
  fun_induction loopErase <;>
    grind [toVertexSeq, loopErase, VertexSeq.loopErase]

@[simp] theorem toVertexSeq_cycleErase [DecidableEq α] (w : Walk α β) :
    w.cycleErase.toVertexSeq = w.toVertexSeq.cycleErase := by
  fun_induction cycleErase w <;>
    grind [toVertexSeq, cycleErase, VertexSeq.cycleErase, Walk.mem_def,
      VertexSeq.mem_def, toVertexSeq_toList, toVertexSeq_prefixUntil]

/-- Cycle erasure preserves the initial vertex. -/
@[simp] theorem head_cycleErase [DecidableEq α] (w : Walk α β) :
    w.cycleErase.head = w.head := by
  rw [← toVertexSeq_head, toVertexSeq_cycleErase, VertexSeq.head_cycleErase,
    toVertexSeq_head]

/-- Cycle erasure preserves the final vertex. -/
@[simp] theorem tail_cycleErase [DecidableEq α] (w : Walk α β) :
    w.cycleErase.tail = w.tail := by
  rw [← toVertexSeq_tail, toVertexSeq_cycleErase, VertexSeq.tail_cycleErase,
    toVertexSeq_tail]

@[simp] theorem toVertexSeq_append (p q : Walk α β) (t : β) :
    (p.append q t).toVertexSeq = p.toVertexSeq.append q.toVertexSeq := by
  apply VertexSeq.toList_injective
  simp

@[simp] theorem toVertexSeq_reverse (w : Walk α β) :
    w.reverse.toVertexSeq = w.toVertexSeq.reverse := by
  induction w with
  | singleton v => rfl
  | cons w v t ih =>
      change ((Walk.singleton v).append w.reverse t).toVertexSeq =
        (w.toVertexSeq.cons v).reverse
      rw [toVertexSeq_append, ih]
      rfl

@[simp] theorem toVertexSeq_mapVertices (w : Walk α β) (f : α → γ) :
    (w.mapVertices f).toVertexSeq = w.toVertexSeq.map f := by
  induction w <;> simp_all [mapVertices, toVertexSeq, VertexSeq.map]

@[simp] theorem toVertexSeq_mapTags (w : Walk α β) (g : β → δ) :
    (w.mapTags g).toVertexSeq = w.toVertexSeq := by
  induction w <;> simp_all [mapTags, toVertexSeq]

/-- No vertex occurs twice. -/
def nodup (w : Walk α β) : Prop := w.vertices.Nodup

/-- Consecutive vertices are distinct. -/
def nonstalling (w : Walk α β) : Prop := w.toVertexSeq.nonstalling

/-- The first and last vertices agree. -/
def closed (w : Walk α β) : Prop := w.head = w.tail

@[simp] theorem toVertexSeq_nodup (w : Walk α β) : w.toVertexSeq.nodup ↔ w.nodup := by
  simp [VertexSeq.nodup_iff_toList_nodup, nodup]

@[simp] theorem toVertexSeq_nonstalling (w : Walk α β) :
    w.toVertexSeq.nonstalling ↔ w.nonstalling := Iff.rfl

@[simp] theorem toVertexSeq_closed (w : Walk α β) : w.toVertexSeq.closed ↔ w.closed := by
  simp [VertexSeq.closed, closed]

@[simp] theorem nodup_singleton (v : α) : (singleton v : Walk α β).nodup := by simp [nodup]

@[simp] theorem closed_reverse (w : Walk α β) : w.reverse.closed ↔ w.closed := by
  simp [closed, eq_comm]

/-! ## Actual reconstructed steps -/

/-- Actual undirected edges reconstructed from tags and adjacent vertices. -/
@[grind] def edges : Walk α β → List (Edge α β)
  | .singleton _ => []
  | .cons w v t => w.edges.concat ⟨t, s(w.tail, v)⟩

/-- Actual directed arcs reconstructed from tags and adjacent vertices. -/
@[grind] def arcs : Walk α β → List (Arc α β)
  | .singleton _ => []
  | .cons w v t => w.arcs.concat ⟨t, (w.tail, v)⟩

@[simp] theorem edges_singleton (v : α) : (singleton v : Walk α β).edges = [] := rfl
@[simp] theorem edges_cons (w : Walk α β) (v : α) (t : β) :
    (w.cons v t).edges = w.edges.concat ⟨t, s(w.tail, v)⟩ := rfl
@[simp] theorem arcs_singleton (v : α) : (singleton v : Walk α β).arcs = [] := rfl
@[simp] theorem arcs_cons (w : Walk α β) (v : α) (t : β) :
    (w.cons v t).arcs = w.arcs.concat ⟨t, (w.tail, v)⟩ := rfl

@[simp] theorem length_edges (w : Walk α β) : w.edges.length = w.length := by
  induction w <;> simp_all

@[simp] theorem length_arcs (w : Walk α β) : w.arcs.length = w.length := by
  induction w <;> simp_all

@[simp] theorem edges_mapVertices (w : Walk α β) (f : α → γ) :
    (w.mapVertices f).edges =
      w.edges.map (fun e => Edge.mk e.tag (Sym2.map f e.endpoints)) := by
  induction w <;> simp_all [mapVertices, edges]

@[simp] theorem arcs_mapVertices (w : Walk α β) (f : α → γ) :
    (w.mapVertices f).arcs =
      w.arcs.map (fun a => Arc.mk a.tag (f a.source, f a.target)) := by
  induction w <;> simp_all [mapVertices, arcs]

@[simp] theorem edges_mapTags (w : Walk α β) (g : β → δ) :
    (w.mapTags g).edges =
      w.edges.map (fun e => Edge.mk (g e.tag) e.endpoints) := by
  induction w <;> simp_all [mapTags, edges]

@[simp] theorem arcs_mapTags (w : Walk α β) (g : β → δ) :
    (w.mapTags g).arcs =
      w.arcs.map (fun a => Arc.mk (g a.tag) a.endpoints) := by
  induction w <;> simp_all [mapTags, arcs]

@[simp] theorem tail_dropHead (w : Walk α β) : w.dropHead.tail = w.tail := by
  cases w with
  | singleton v => rfl
  | cons w v t => cases w <;> rfl

@[simp] theorem edges_dropHead (w : Walk α β) : w.dropHead.edges = w.edges.tail := by
  induction w with
  | singleton v => rfl
  | cons w v t ih =>
      cases w with
      | singleton u => rfl
      | cons q u s =>
          simp only [dropHead, edges, List.concat_eq_append, ih]
          cases hq : q.edges <;> simp [hq, List.append_assoc]

@[simp] theorem arcs_dropHead (w : Walk α β) : w.dropHead.arcs = w.arcs.tail := by
  induction w with
  | singleton v => rfl
  | cons w v t ih =>
      cases w with
      | singleton u => rfl
      | cons q u s =>
          simp only [dropHead, arcs, List.concat_eq_append, ih]
          cases hq : q.arcs <;> simp [hq, List.append_assoc]

theorem edges_dropTail_subset (w : Walk α β) : w.dropTail.edges ⊆ w.edges := by
  cases w <;> simp [dropTail, edges, List.concat_eq_append]

theorem arcs_dropTail_subset (w : Walk α β) : w.dropTail.arcs ⊆ w.arcs := by
  cases w <;> simp [dropTail, arcs, List.concat_eq_append]

theorem edges_dropHead_subset (w : Walk α β) : w.dropHead.edges ⊆ w.edges := by
  induction w with
  | singleton v => simp [dropHead]
  | cons w v t ih =>
      cases w with
      | singleton u => simp [dropHead]
      | cons q u s =>
          intro e he
          simp only [dropHead, edges_cons, List.concat_eq_append, List.mem_append,
            List.mem_singleton, tail_dropHead] at he ⊢
          rcases he with he | he
          · have hprev : e ∈ q.edges ∨ e = Edge.mk s s(q.tail, u) := by
              simpa [edges_cons, List.concat_eq_append] using ih he
            exact Or.inl hprev
          · exact Or.inr he

theorem arcs_dropHead_subset (w : Walk α β) : w.dropHead.arcs ⊆ w.arcs := by
  induction w with
  | singleton v => simp [dropHead]
  | cons w v t ih =>
      cases w with
      | singleton u => simp [dropHead]
      | cons q u s =>
          intro a ha
          simp only [dropHead, arcs_cons, List.concat_eq_append, List.mem_append,
            List.mem_singleton, tail_dropHead] at ha ⊢
          rcases ha with ha | ha
          · have hprev : a ∈ q.arcs ∨ a = Arc.mk s (q.tail, u) := by
              simpa [arcs_cons, List.concat_eq_append] using ih ha
            exact Or.inl hprev
          · exact Or.inr ha

theorem edges_prefixUntil_subset [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).edges ⊆ w.edges := by
  fun_induction prefixUntil w v h <;>
    simp_all [prefixUntil, edges, List.concat_eq_append]

theorem arcs_prefixUntil_subset [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).arcs ⊆ w.arcs := by
  fun_induction prefixUntil w v h <;>
    simp_all [prefixUntil, arcs, List.concat_eq_append]

theorem edges_suffixFrom_subset [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).edges ⊆ w.edges := by
  fun_induction suffixFrom w v h <;>
    simp_all [suffixFrom, edges, List.concat_eq_append]

theorem arcs_suffixFrom_subset [DecidableEq α] (w : Walk α β)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).arcs ⊆ w.arcs := by
  fun_induction suffixFrom w v h <;>
    simp_all [suffixFrom, arcs, List.concat_eq_append]

@[simp] theorem edges_append (p q : Walk α β) (t : β) :
    (p.append q t).edges = p.edges ++ [⟨t, s(p.tail, q.head)⟩] ++ q.edges := by
  induction q <;> simp_all [append, List.concat_eq_append, List.append_assoc]

@[simp] theorem arcs_append (p q : Walk α β) (t : β) :
    (p.append q t).arcs = p.arcs ++ [⟨t, (p.tail, q.head)⟩] ++ q.arcs := by
  induction q <;> simp_all [append, List.concat_eq_append, List.append_assoc]

@[simp] theorem edges_glue (p q : Walk α β) (h : p.tail = q.head) :
    (p.glue q h).edges = p.edges ++ q.edges := by
  cases p with
  | singleton v => simp [glue]
  | cons p v t =>
      change (p.append q t).edges = (p.edges.concat ⟨t, s(p.tail, v)⟩) ++ q.edges
      rw [edges_append, ← h]
      simp [List.concat_eq_append, List.append_assoc]

@[simp] theorem arcs_glue (p q : Walk α β) (h : p.tail = q.head) :
    (p.glue q h).arcs = p.arcs ++ q.arcs := by
  cases p with
  | singleton v => simp [glue]
  | cons p v t =>
      change (p.append q t).arcs = (p.arcs.concat ⟨t, (p.tail, v)⟩) ++ q.arcs
      rw [arcs_append, ← h]
      simp [List.concat_eq_append, List.append_assoc]

@[simp] theorem edges_reverse (w : Walk α β) : w.reverse.edges = w.edges.reverse := by
  induction w with
  | singleton v => rfl
  | cons w v t =>
      simp [reverse, List.concat_eq_append, Sym2.eq_swap, *]

@[simp] theorem arcs_reverse (w : Walk α β) :
    w.reverse.arcs =
      w.arcs.reverse.map (fun a => Arc.mk a.tag (a.target, a.source)) := by
  induction w with
  | singleton v => rfl
  | cons w v t => simp [reverse, List.concat_eq_append, *]

/-- The generated undirected graph has exactly the vertices and reconstructed edges of `w`. -/
def toGraph (w : Walk α β) : Graph α β where
  vertexSet := {v | v ∈ w.vertices}
  edgeSet := {e | e ∈ w.edges}
  endpoints_mem := by
    intro e he v hv
    induction w with
    | singleton x => simp at he
    | cons w x t ih =>
        simp only [edges_cons, List.concat_eq_append, List.mem_append,
          List.mem_singleton] at he
        rcases he with he | rfl
        · change v ∈ w.vertices.concat x
          simp only [List.concat_eq_append, List.mem_append, List.mem_singleton]
          exact Or.inl (ih he)
        · simp only [Sym2.mem_iff] at hv
          rcases hv with rfl | rfl
          · change w.tail ∈ w.vertices.concat x
            simp only [List.concat_eq_append, List.mem_append, List.mem_singleton]
            exact Or.inl w.tail_mem
          · simp [vertices, List.concat_eq_append]

/-- The generated directed graph has exactly the vertices and reconstructed arcs of `w`. -/
def toDiGraph (w : Walk α β) : DiGraph α β where
  vertexSet := {v | v ∈ w.vertices}
  edgeSet := {a | a ∈ w.arcs}
  source_mem := by
    intro a ha
    induction w with
    | singleton x => simp at ha
    | cons w x t ih =>
        simp only [arcs_cons, List.concat_eq_append, List.mem_append,
          List.mem_singleton] at ha
        rcases ha with ha | rfl
        · change a.source ∈ w.vertices.concat x
          simp only [List.concat_eq_append, List.mem_append, List.mem_singleton]
          exact Or.inl (ih ha)
        · simp only [Arc.source]
          change w.tail ∈ w.vertices.concat x
          simp only [List.concat_eq_append, List.mem_append, List.mem_singleton]
          exact Or.inl w.tail_mem
  target_mem := by
    intro a ha
    induction w with
    | singleton x => simp at ha
    | cons w x t ih =>
        simp only [arcs_cons, List.concat_eq_append, List.mem_append,
          List.mem_singleton] at ha
        rcases ha with ha | rfl
        · change a.target ∈ w.vertices.concat x
          simp only [List.concat_eq_append, List.mem_append, List.mem_singleton]
          exact Or.inl (ih ha)
        · simp only [Arc.target]
          simp [vertices, List.concat_eq_append]

@[simp] theorem vertexSet_toGraph (w : Walk α β) : V(w.toGraph) = {v | v ∈ w.vertices} := rfl
@[simp] theorem edgeSet_toGraph (w : Walk α β) : E(w.toGraph) = {e | e ∈ w.edges} := rfl
@[simp] theorem vertexSet_toDiGraph (w : Walk α β) :
    V(w.toDiGraph) = {v | v ∈ w.vertices} := rfl
@[simp] theorem edgeSet_toDiGraph (w : Walk α β) : E(w.toDiGraph) = {a | a ∈ w.arcs} := rfl

end Walk

end GraphLib
