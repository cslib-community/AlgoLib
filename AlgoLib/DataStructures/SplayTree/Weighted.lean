import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

import AlgoLib.DataStructures.SplayTree.Complexity -- Required for some lemmas
import AlgoLib.DataStructures.SplayTree.Correctness -- Required for some lemmas

/-!
# Weighted Bounds for Splay Trees

An extension of the Complexity module. Formalizes Sleator and Tarjan's weighted analysis of
(bottom-up) splay trees and their Access Lemma.

The Access Lemma allow defining an arbitary positive weight `w(v)` for each node. It bounds the
amortized cost of an acess by `O( 1 + log(W/w(v)))`, where `W` is the total weight of all nodes in
the splay tree. The weight function is defined simply as a function `w : α → ℝ` on the node type
`α`.
-/

variable {α : Type}

namespace SplayTree

namespace Weighted

open Tree

/-! ## Definitions for weighted potential analysis -/
section WeightedPotentialMethod

/-- Property defining weight functions that are at least one.
This ensures that logs are nonnegative and is thus required for most internal lemmas -/
def FnLbOne (w : α → ℝ) : Prop :=
  ∀ x, 1 ≤ w x

/-- Property for positive weight functions -/
def FnPos (w : α → ℝ) : Prop :=
  ∀ x, 0 < w x

/-- Property for nonnegative weight functions. -/
def FnNonneg (w : α → ℝ) : Prop :=
  ∀ x, 0 ≤ w x

lemma FnPos_of_FnLbOne {w : α → ℝ} (h : FnLbOne w) : (FnPos w) := by
  intro x; linarith [h x]

lemma FnNonneg_of_FnPos {w : α → ℝ} (h : FnPos w) : (FnNonneg w) := by
  intro x; linarith [h x]

lemma FnNonneg_of_FnLbOne {w : α → ℝ} (h : FnLbOne w) : (FnNonneg w) := by
  intro x; linarith [h x]

/-- Size of a tree: total weight of all nodes. -/
def size (w : α → ℝ) : Tree α → ℝ
  | nil => (0 : ℝ)
  | node b l r => w b + size w l + size w r

/-- Rank of a tree: logarithm of the size, or 0 for the empty tree. -/
noncomputable def rank (w : α → ℝ) (t : Tree α) : ℝ :=
  match t with
    | nil => 0
    | _ => Real.logb 2 (size w t)

/-- Potential of a tree: sum of ranks over all subtrees (including itself). -/
noncomputable def φ (w : α → ℝ) : Tree α → ℝ
  | .nil => 0
  | s@(l △[_] r) => rank w s + φ w l + φ w r


/-! ### Lemmas for size, rank, and potential -/

variable {w : α → ℝ}

/-! #### Basic size lemmas -/

@[simp] lemma size_empty : size w (.nil : Tree α) = 0 := by simp only [size]
@[simp] lemma size_node {v : α} {l r : Tree α} : size w (node v l r) = w v + size w l + size w r :=
  by simp only [size]

@[simp] theorem size_rotateRight (t : Tree α) :
    size w (rotateRight t) = size w t := by
  rcases t with _ | ⟨k, (_ | ⟨lk, ll, lr⟩), r⟩ <;>
    simp [rotateRight]; linarith

@[simp] theorem size_rotateLeft (t : Tree α) :
    size w (rotateLeft t) = size w t := by
  rcases t with _ | ⟨k, l, (_ | ⟨rk, rl, rr⟩)⟩ <;>
    simp [rotateLeft]; linarith

lemma size_nonneg (hw : FnNonneg w) (t : Tree α) : 0 ≤ size w t := by
  induction t with
  | nil => simp [size_empty]
  | node v l r =>
    unfold size
    linarith [hw v]

private lemma size_nonneg' (hw : FnPos w) (t : Tree α) : 0 ≤ size w t :=
  size_nonneg (FnNonneg_of_FnPos hw) t

private lemma size_nonneg'' (hw : FnLbOne w) (t : Tree α) : 0 ≤ size w t :=
  size_nonneg (FnNonneg_of_FnLbOne hw) t

lemma size_ge_root_value (hw : FnNonneg w) (v : α) (l r : Tree α) :
    w v ≤ size w (node v l r) := by
  unfold size
  linarith [size_nonneg hw l, size_nonneg hw r]

lemma size_ge_left_child (hw : FnNonneg w) (v : α) (l r : Tree α) :
    size w l ≤ size w (node v l r) := by
    simp[size_node]; linarith [hw v, size_nonneg hw r]

lemma size_ge_right_child (hw : FnNonneg w) (v : α) (l r : Tree α) :
    size w r ≤ size w (node v l r) := by
    simp[size_node]; linarith [hw v, size_nonneg hw l]

lemma size_pos_of_non_nil (hw : FnPos w) (t : Tree α) (h : t ≠ nil) : 0 < size w t := by
  cases t with
  | nil => by_contra; apply h; rfl
  | node v l r =>
    linarith [hw v, size_ge_root_value (FnNonneg_of_FnPos hw) v l r]

lemma size_from_toKeyList (t : Tree α) :
  size w t = (t.toKeyList.map w).sum := by
  induction t with
  | nil => simp[size, toKeyList]
  | node a l r =>
    simp [size, toKeyList]
    linarith

lemma size_zero_iff_empty (hw : FnPos w) (t : Tree α) : size w t = 0 ↔ t = nil := by
  constructor
  · unfold size
    cases t with
    | nil => intro h; rfl
    | node v l r =>
      simp only [reduceCtorEq, imp_false]
      linarith [size_nonneg' hw l, size_nonneg' hw r, hw v]
  · intro h; simp [h]

lemma size_le_size_of_toKeyList_Sublist {w : α → ℝ} (hw : FnNonneg w)
    {s t : Tree α} (h : s.toKeyList.Sublist t.toKeyList) :
    size w s ≤ size w t := by
  rw [size_from_toKeyList, size_from_toKeyList]
  have : (List.map w s.toKeyList).Sublist (List.map w t.toKeyList) := by
    exact List.Sublist.map w h
  apply List.Sublist.sum_le_sum
  · exact List.Sublist.map w h
  · intro x hx
    have := List.mem_map.mp hx
    rcases this with ⟨y, _, hy⟩
    rw [←hy]; exact hw y

/-! #### Splay-tree-related size lemmas -/

@[simp]
theorem size_bringUp (d : Dir) (t : Tree α) :
    size w (d.bringUp t) = size w t := by
  cases d <;> simp [Dir.bringUp]

@[simp]
theorem size_applyChild (d : Dir) (op : Tree α → Tree α)
    (hop : ∀ s, size w (op s) = size w s) (t : Tree α) :
    size w (applyChild d op t) = size w t := by
  cases t with
  | nil => rfl
  | node k l r => cases d <;> simp [applyChild, hop]

lemma size_Frame_attach (s : Tree α) (f : Frame α) :
    size w (f.attach s) = size w s + w f.key + size w f.sibling := by
  simp [Frame.attach]
  cases f.dir; all_goals simp; linarith

@[simp] lemma size_splay [LinearOrder α] (s : Tree α) (q : α) : size w (splay s q) = size w s := by
  rw [size_from_toKeyList, size_from_toKeyList]; rw [toKeyList_splay]

/-! #### Basic rank lemmas -/

@[simp] lemma rank_empty : rank w (.nil : Tree α) = 0 :=
  by simp [rank]

lemma rank_nonneg (hw : FnLbOne w) (t : Tree α) : 0 ≤ rank w t := by
  unfold rank; cases t with
  | nil => simp
  | node v l r =>
    simp only [size_node]
    have : w v + size w l + size w r ≥ 1 := by
      linarith [hw v, size_nonneg'' hw l, size_nonneg'' hw r]
    exact Real.logb_nonneg (show 1 < (2 : ℝ) by simp) this

lemma rank_le_of_size_le (hw : FnLbOne w) (s t : Tree α) (h : size w s ≤ size w t) :
    rank w s ≤ rank w t := by
  cases s <;> cases t <;> all_goals try simp only [rank_empty, rank_nonneg hw, le_rfl]
  · simp only [rank]; simp only [size_empty] at h
    apply (Real.logb_nonpos_iff' (by simp) ?_).mpr
    · linarith
    · apply size_nonneg'' hw
  · apply SplayTree.logb_mono
    · exact size_pos_of_non_nil (FnPos_of_FnLbOne hw) _ (by simp)
    · linarith [h]

lemma rank_eq_of_toKeyList_eq {s t : Tree α}
  (h : s.toKeyList = t.toKeyList) : rank w s = rank w t := by
  simp only [rank]
  cases s with
  | nil =>
    simp only
    simp only [toKeyList, List.nil_eq] at h
    rw [size_from_toKeyList, h, List.map_nil, List.sum_nil, nil_of_toKeyList_empty h]
  | node v l r =>
    have : t.toKeyList ≠ [] := by rw [←h]; simp
    have : t ≠ nil := by contrapose this; rw [this]; exact toKeyList_empty
    simp only; rw [size_from_toKeyList, size_from_toKeyList, h]


/-! #### Splay-related rank lemmas -/

@[simp] lemma rank_splay [LinearOrder α] (w : α → ℝ) (t : Tree α) (q : α) :
    rank w (splay t q) = rank w t :=
  rank_eq_of_toKeyList_eq (toKeyList_splay t q)


/-! #### Basic potential lemmas -/

@[simp] lemma φ_empty : φ w (.nil : Tree α) = 0 := rfl

@[simp] lemma φ_node (l : Tree α) (k : α) (r : Tree α) :
    φ w (l △[k] r) = rank w (l △[k] r) + φ w l + φ w r := rfl

lemma φ_nonneg (hw : FnLbOne w) (t : Tree α) : 0 ≤ φ w t := by
  induction t with
  | nil => rfl
  | node k l r => simp [φ]; linarith [rank_nonneg hw (l △[k] r), φ_nonneg hw l, φ_nonneg hw r]


/-! #### Potential of subtrees versus the whole tree -/

theorem φ_le_attach (hw : FnLbOne w) (c : Tree α) (f : Frame α) :
  φ w c ≤ φ w (f.attach c) := by
  cases f with | mk d k s =>
  cases d <;> simp [Frame.attach, φ_node] <;>
  linarith [rank_nonneg hw (c △[k] s), rank_nonneg hw (s △[k] c),
  φ_nonneg hw c, φ_nonneg hw s]

theorem φ_le_reassemble (hw : FnLbOne w) (c : Tree α) (path : List (Frame α)) :
    φ w c ≤ φ w (reassemble c path) := by
  induction path generalizing c with
  | nil => simp
  | cons f rest ih => simp only [reassemble_cons]; exact le_trans (φ_le_attach hw c f) (ih _)

theorem φ_descend_subtree_le [LinearOrder α] (hw : FnLbOne w) (t : Tree α) (q : α) :
    φ w (descend t q).1 ≤ φ w t := by
  have h := descend_preserves_tree t q
  calc φ w (descend t q).1
      ≤ φ w (reassemble (descend t q).1 (descend t q).2) :=
        φ_le_reassemble hw _ _
    _ = φ w t := by rw [h]


/-! #### Mirror preserves rank and potential -/

lemma rank_mirror (t : Tree α) : rank w t.mirror = rank w t := by
  cases t
  · simp [rank]
  · simp only [rank, mirror_node, size_from_toKeyList, toKeyList_node, toKeyList_mirror,
    List.append_assoc, List.cons_append, List.nil_append, List.map_append, List.map_reverse,
    List.map_cons, List.sum_append, List.sum_reverse, List.sum_cons]
    apply congr
    · rfl
    · linarith

lemma φ_mirror (t : Tree α) : φ w t.mirror = φ w t := by
  induction t with
  | nil => rfl
  | node v r l =>
    rw [mirror_node, φ_node, φ_node, ← mirror, rank_mirror]
    simp_all; linarith

/-- Transfer a potential-step inequality from mirrored trees to the originals. -/
private lemma φ_transfer_mirror
    {step s c step' s' : Tree α}
    (hstep : step.mirror = step')
    (hs : s.mirror = s')
    (h : φ w step' - φ w s' + 2 ≤
      3 * (rank w step' - rank w c.mirror)) :
    φ w step - φ w s + 2 ≤ 3 * (rank w step - rank w c) := by
  rw [← hstep, φ_mirror, rank_mirror] at h
  rw [← hs, φ_mirror, rank_mirror c] at h
  assumption


/-! #### Splay step potential bounds -/

theorem φ_zig (hw : FnLbOne w) (c : Tree α) (f : Frame α) :
    φ w (f.dir.bringUp (f.attach c)) - φ w (f.attach c) ≤
      rank w (f.dir.bringUp (f.attach c)) - rank w c := by
  rcases f with ⟨d, key, sib⟩
  rcases c with _ | ⟨k, l, r⟩ <;> cases d <;>
    all_goals simp only [Dir.bringUp, rotateLeft, rotateRight,
    Frame.attach, φ_node, φ_empty, add_zero, sub_self, rank_empty, sub_zero]
  · exact rank_nonneg hw _
  · exact rank_nonneg hw _
  · have : rank w (r △[key] sib) ≤ rank w ((l △[k] r) △[key] sib) := by
      apply rank_le_of_size_le hw
      simp [size_node]; linarith [hw k, size_nonneg'' hw l]
    linarith
  · have : rank w (sib △[key] l) ≤ rank w (sib △[key] (l △[k] r)) := by
      apply rank_le_of_size_le hw
      simp [size_node]; linarith [hw k, size_nonneg'' hw l, size_nonneg'' hw r]
    linarith

private theorem φ_zigzig_left (hw : FnLbOne w)
    (a b c : α) (t1 t2 t3 t4 : Tree α) :
    let x := node a t1 t2 -- The node we're rotating
    let s := node c (node b x t3) t4 -- The initial tree
    let s' := rotateRight (rotateRight s) -- The resulting tree
    φ w s' - φ w s + 2 ≤ 3 * (rank w s' - rank w x) := by
  let x := node a t1 t2
  let s := node c (node b x t3) t4
  let s' := rotateRight (rotateRight s)
  let φ_children := φ w t1 + φ w t2 + φ w t3 + φ w t4
  -- Write out the potentials of both trees
  have : φ w s = rank w s + rank w (node b x t3) + rank w x + φ_children := by
    unfold s φ_children x; simp [φ_node]; linarith
  let x' := node c t3 t4
  have : φ w s' = rank w s' + rank w (node b t2 x') + rank w x' + φ_children := by
    unfold s' φ_children x' s rotateRight x; simp; linarith
  -- Total rank stays the same
  have : rank w s = rank w s' := by
    apply rank_eq_of_toKeyList_eq
    unfold s'; simp only [toKeyList_rotateRight]
  -- The calculation
  have : rank w (node b t2 x') ≤ rank w s' := by
    unfold s' s rotateRight x x'; simp only; apply rank_le_of_size_le hw
    exact size_ge_right_child (FnNonneg_of_FnLbOne hw) _ _ _
  have : rank w x ≤ rank w (node b x t3) := by
    apply rank_le_of_size_le hw; apply size_ge_left_child (FnNonneg_of_FnLbOne hw)
  have : rank w x + rank w x' ≤ 2 * rank w s' - 2 := by
    simp only [rank, reduceCtorEq, imp_self, (show s' ≠ nil by simp [s', rotateRight])]
    apply log_sum_le
    · exact size_pos_of_non_nil (FnPos_of_FnLbOne hw) x (show x ≠ nil by simp)
    · exact size_pos_of_non_nil (FnPos_of_FnLbOne hw) x' (show x' ≠ nil by simp)
    · unfold s' rotateRight s x x'; simp; linarith [hw b]
  linarith

theorem φ_zigzig (hw : FnLbOne w) (a : α) (l r : Tree α) (f1 f2 : Frame α)
    (heq : f1.dir = f2.dir) :
    let c := node a l r
    let s := f2.attach (f1.attach c)
    let step := f2.dir.bringUp (f2.dir.bringUp s)
    φ w step - φ w s + 2 ≤ 3 * (rank w step - rank w c) := by
  let c := node a l r
  rcases f1 with ⟨d, k1, n1⟩; rcases f2 with ⟨_, k2, n2⟩; subst heq
  cases d
  · exact φ_zigzig_left hw a k1 k2 l r n1 n2
  · have h := φ_zigzig_left hw a k1 k2 r.mirror l.mirror n1.mirror n2.mirror
    simp only [Frame.attach, Dir.bringUp, rotateRight, rotateLeft] at h ⊢
    repeat rw [← mirror] at h
    simp only [φ_mirror, rank_mirror] at h
    assumption

private theorem φ_zigzag_left (hw : FnLbOne w)
    (a b c : α) (t1 t2 t3 t4 : Tree α) :
    let x := node b t2 t3 -- The node we're rotating
    let s := node a t1 (node c x t4) -- The initial tree
    let s' := rotateLeft (applyChild .R rotateRight s) -- The resulting tree
    φ w s' - φ w s + 2 ≤ 3 * (rank w s' - rank w x) := by
  let x := node b t2 t3 -- The node we're rotating
  let s := node a t1 (node c x t4) -- The initial tree
  let s' := rotateLeft (applyChild .R rotateRight s) -- The resulting tree
  let φ_children := φ w t1 + φ w t2 + φ w t3 + φ w t4
  -- Write out the potentials of both trees
  have : φ w s = rank w s + rank w (node c x t4) + rank w x + φ_children := by
    unfold s φ_children x; simp; linarith
  have : φ w s' = rank w s' + rank w (node a t1 t2) + rank w (node c t3 t4) + φ_children := by
    unfold s' s applyChild rotateLeft rotateRight x φ_children; simp; linarith
  -- Total rank stays the same
  have : rank w s = rank w s' := by
    apply rank_eq_of_toKeyList_eq
    unfold s'; simp
  -- The calculation
  have : φ w s' - φ w s = (
      rank w (node a t1 t2) + rank w (node c t3 t4) - rank w (node c x t4) - rank w x ) := by
    linarith
  have : rank w x ≤ rank w (node c x t4) := by
    apply rank_le_of_size_le hw; apply size_ge_left_child (FnNonneg_of_FnLbOne hw)
  have : rank w (node a t1 t2) + rank w (node c t3 t4) ≤ 2 * rank w s' - 2 := by
    simp only [rank, size_node, imp_self,
      (show s' ≠ nil by simp [s', rotateLeft, applyChild, rotateRight])]
    apply log_sum_le
    · linarith [hw a, size_nonneg'' hw t1, size_nonneg'' hw t2]
    · linarith [hw c, size_nonneg'' hw t3, size_nonneg'' hw t4]
    · unfold s' applyChild rotateRight rotateLeft s x; simp; linarith [hw b]
  have : rank w x ≤ rank w s' := by
    simp only [s', s, applyChild, x, rotateRight, rotateLeft]; apply rank_le_of_size_le hw
    simp; linarith [hw a, hw c, size_nonneg'' hw t1, size_nonneg'' hw t4]
  linarith


theorem φ_zigzag (hw : FnLbOne w) (a : α) (l r : Tree α) (f1 f2 : Frame α)
    (hne : f1.dir ≠ f2.dir) :
    let c := node a l r
    let s := f2.attach (f1.attach c)
    let step := f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
    φ w step - φ w s + 2 ≤ 3 * (rank w step - rank w c) := by
  let c := node a l r
  rcases f1 with ⟨d1, k1, n1⟩; rcases f2 with ⟨d2, k2, n2⟩
  cases d1 <;> cases d2 <;> simp_all +decide only [ne_eq]
  · exact φ_zigzag_left hw k2 a k1 n2 l r n1
  · have h := φ_zigzag_left hw k2 a k1 n2.mirror r.mirror l.mirror n1.mirror
    simp only [Frame.attach, Dir.bringUp, rotateRight, rotateLeft, applyChild] at h ⊢
    repeat rw [← mirror] at h
    simp only [φ_mirror, rank_mirror] at h
    assumption


/-! #### Telescoping: potential change along the full splayUp -/

lemma φ_attach_congr {s s' : Tree α} (f : Frame α)
    (h : size w s = size w s') :
    φ w (f.attach s') - φ w (f.attach s) = φ w s' - φ w s := by
  cases f with | mk d k sib =>
  cases d <;> simp only [Frame.attach, φ_node, add_sub_add_right_eq_sub] <;>
    (unfold rank; simp [h])

lemma φ_reassemble_congr {s s' : Tree α} (path : List (Frame α))
    (h : size w s = size w s') :
    φ w (reassemble s' path) - φ w (reassemble s path) = φ w s' - φ w s := by
  induction path generalizing s s' with
  | nil => simp
  | cons f rest ih =>
    simp only [reassemble_cons]
    rw [ih (by simp [size_Frame_attach, h])]
    exact φ_attach_congr f h

/-- The total potential change of splayUp plus the path length is at
    most 3 × the rank increase + 1. -/
theorem φ_splayUp (hw : FnLbOne w) (c : Tree α) (hc : c ≠ nil) (path : List (Frame α)) :
    φ w (splayUp c path) - φ w (reassemble c path) + path.length ≤
      3 * (rank w (splayUp c path) - rank w c) + 1 := by
  induction c, path using splayUp_induction with
  | nil c => simp
  | single c f =>
    simp only [splayUp_singleton, reassemble_cons,
      reassemble_nil, List.length_singleton, Nat.cast_one]
    have : rank w (f.dir.bringUp (Frame.attach c f)) = rank w (Frame.attach c f) := by
      simp only [Dir.bringUp]; cases f.dir
      all_goals simp only; apply rank_eq_of_toKeyList_eq
      · apply toKeyList_rotateRight
      · apply toKeyList_rotateLeft
    have : rank w c ≤ rank w (f.dir.bringUp (Frame.attach c f)) := by
      rw [this]; simp only [Frame.attach]; cases f.dir;
        all_goals simp only; apply rank_le_of_size_le hw
      · apply size_ge_left_child (FnNonneg_of_FnLbOne hw)
      · apply size_ge_right_child (FnNonneg_of_FnLbOne hw)
    linarith [φ_zig hw c f]
  | step c f1 f2 rest ih =>
    cases c with
    | nil =>
      contradiction
    | node a l r =>
      rw [splayUp_cons_cons]; simp only [List.length_cons]
      split_ifs with hdir
      · set s := f2.attach (f1.attach (node a l r))
        set step_tree := f2.dir.bringUp (f2.dir.bringUp s)
        have hsize : size w step_tree = size w s := by
          simp [step_tree]
        simp only [reassemble_cons]; push_cast
        have : step_tree ≠ nil := by
          unfold step_tree; apply Dir.bringUp_ne_nil_of_ne_nil; apply Dir.bringUp_ne_nil_of_ne_nil
          unfold s; apply Frame.attach_ne_nil
        nlinarith [ih step_tree this,
          φ_reassemble_congr rest hsize.symm, φ_zigzig hw a l r f1 f2 hdir]
      · set s := f2.attach (f1.attach (node a l r))
        set step_tree := f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
        have hsize : size w step_tree = size w s := by
          simp [step_tree]
        simp only [reassemble_cons]; push_cast
        have : step_tree ≠ nil := by
          unfold step_tree; apply Dir.bringUp_ne_nil_of_ne_nil;
          apply Dir.applyChild_ne_nil_of_ne_nil
          unfold s; apply Frame.attach_ne_nil
        nlinarith [ih step_tree this,
          φ_reassemble_congr rest hsize.symm, φ_zigzag hw a l r f1 f2 hdir]

/-! #### The main amortized bound -/

/-- Slighly weaker version of Sleator and Tarjan's access lemma: Does not take into account the
  subtree rooted at q, only the weight of q itself; also requires weights at least one. -/
theorem splay_access_lemma [LinearOrder α]
    (hw : FnLbOne w) (t : Tree α) (q : α) (hbst : IsBST t) (hq : q ∈ t) :
    φ w (splay t q) - φ w t + splay.cost t q ≤
      3 * Real.logb 2 ( (size w t) / w q ) + 1 := by
  rcases hdecomp : descend t q with ⟨reached, path⟩
  have : ∃ l r, (descend t q).1 = node q l r := descend_contains' t q hbst hq
  have hreached : ∃ l r, reached = node q l r := by simp_all only
  have hpres := descend_preserves_tree t q
  rw [hdecomp] at hpres; simp only at hpres
  rcases hreached with ⟨l,r,hreached⟩
  have h_splay : splay t q = splayUp reached path ∨
      (∃ f rest, reached = .nil ∧
        path = f :: rest ∧
        splay t q = splayUp (f.attach .nil) rest) := by
    simp only [splay, hdecomp]
    rw [hreached]; simp
  have h_cost : splay.cost t q = path.length := by simp [splay.cost, hdecomp, hreached]
  rw [h_cost]
  have h_eq : splay t q = splayUp (l △[q] r) path := by simp [splay, hdecomp, hreached]
  rw [h_eq]
  have hφ := φ_splayUp hw (l △[q] r) (by simp) path
  rw [←hreached, hpres, hreached] at hφ
  have hrank_eq : rank w (splayUp (l △[q] r) path) = rank w t := by
    have h := rank_splay w t q; simp only [splay, hdecomp, hreached] at h; exact h
  have htnn : t ≠ nil := nonnil_of_mem q hq
  calc φ w (splayUp (l △[q] r) path) - φ w t + ↑path.length
      ≤ 3 * (rank w (splayUp (l △[q] r) path) - rank w (l △[q] r)) + 1 := by exact_mod_cast hφ
    _ ≤ 3 * (rank w t - rank w (l △[q] r)) + 1 := by simp [hrank_eq]
    _ ≤ 3 * ( Real.logb 2 ( size w t ) - rank w (l △[q] r)) + 1 := by simp [rank]
    _ ≤ 3 * ( Real.logb 2 ( size w t ) - Real.logb 2 (w q)) + 1 := by
      have : Real.logb 2 (w q) ≤ rank w (l △[q] r) := by
        simp only [rank, size_node]; apply logb_mono (by linarith [hw q])
        linarith [size_nonneg'' hw l, size_nonneg'' hw r]
      linarith
    _ ≤ 3 * Real.logb 2 ( (size w t) / w q ) + 1 := by
      have hsizepos: size w t ≠ 0 := by linarith [size_pos_of_non_nil (FnPos_of_FnLbOne hw) t htnn]
      have hwqpos: w q ≠ 0 := by linarith [hw q]
      simp [Real.logb_div hsizepos hwqpos]


end WeightedPotentialMethod


/-! ## Sequence cost with a fixed weight function -/
section SequenceCost

variable {w : α → ℝ}

/-! ### Weights ≥ 1 -/

/-- Potential method: The total cost is the total amortized cost plus the overall potential change.
This is a more general version of `amortized_cost_bound` in the `Complexity` module, which assumes
uniform amortized cost. -/
theorem total_cost_bound {S : Type*} (m : ℕ)
    (s : Fin (m + 1) → S) (cost : Fin m → ℝ)
    (Φ : S → ℝ) (B : Fin m → ℝ)
    (hamort : ∀ i : Fin m,
      Φ (s i.succ) - Φ (s i.castSucc) + cost i ≤ B i) :
    ∑ i : Fin m, cost i ≤ ∑ i : Fin m, (B i) + Φ (s 0) - Φ (s (Fin.last m)) := by
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    hamort i
  simp_all +decide only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ge_iff_le]
  linarith! [Fin.sum_univ_castSucc fun i => Φ (s i),
    Fin.sum_univ_succ fun i => Φ (s i)]

/-- Sequence version of `splay_access_lemma`. -/
theorem splay_total_weighted_cost' [LinearOrder α]
    (hw : FnLbOne w)
    (m : ℕ)
    (t : Fin (m + 1) → Tree α)
    (q : Fin m → α)
    (hseq : ∀ i : Fin m, t i.succ = splay (t i.castSucc) (q i))
    (hbst : (t 0).IsBST)
    (hcont : ∀ i : Fin m, (q i) ∈ (t 0)) :
    ∑ i : Fin m, (splay.cost (t i.castSucc) (q i) : ℝ) ≤
    ∑ i : Fin m, (3 * Real.logb 2 ( size w (t 0) / w (q i) ) + 1) + φ w (t 0) - φ w (t (Fin.last m))
    := by
  cases m with
  | zero => simp
  | succ m' =>
    let m := m'+1
    let B := fun i => (3 * Real.logb 2 ( size w (t 0) / w (q i) ) + 1)
    have hbst' : ∀ i : Fin (m+1), (t i).IsBST := by
      intro i
      induction i using Fin.induction with
      | zero => exact hbst
      | succ i ih => rw [hseq i]; apply IsBST_splay; exact ih
    have hcont' : ∀ (i : Fin m) (j : Fin (m+1)), (q i) ∈ (t j) := by
      intro i j
      induction j using Fin.induction with
      | zero => apply hcont
      | succ j jh =>
        rw [hseq j]
        apply mem_iff_mem_toKeyList.mpr; simp only [toKeyList_splay]; apply mem_iff_mem_toKeyList.mp
        exact jh
    have hnn' : ∀ i : Fin (m+1), (t i) ≠ nil := by
      intro i; exact nonnil_of_mem (q 0) (hcont' 0 i)
    have hsize : ∀ i : Fin (m+1), size w (t i) = size w (t 0) := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => rw [hseq, size_splay]; exact ih
    apply total_cost_bound m t (fun i => (splay.cost (t i.castSucc) (q i) : ℝ)) (φ w) B
    intro i
    rw [hseq i]
    have hb := splay_access_lemma hw (t i.castSucc) (q i) (hbst' i.castSucc) (hcont' i i.castSucc)
    calc φ w (splay (t i.castSucc) (q i)) - φ w (t i.castSucc) +
          splay.cost (t i.castSucc) (q i)
      ≤ 3 * Real.logb 2 (size w (t i.castSucc) / w (q i)) + 1 := hb
    _ ≤ 3 * Real.logb 2 (size w (t 0) / w (q i)) + 1 := by rw[hsize i.castSucc]

private lemma toKeyList_splaySeq [LinearOrder α]
    {m : ℕ} (init : Tree α) (X : Fin m → α) (k : Fin (m + 1)) :
    (splaySeq init X k).toKeyList = init.toKeyList := by
  induction k using Fin.induction with
  | zero => simp [splaySeq]
  | succ m ih => simp only [splaySeq_succ, toKeyList_splay]; exact ih

/-- Simplified version of `splay_total_weighted_cost'` using a general tree potential upper bound.
-/
theorem splay_total_weighted_cost [LinearOrder α]
    (hw : FnLbOne w)
    (m : ℕ)
    (init : Tree α) (hbst : init.IsBST)
    {φ_ub : ℝ} (hφ : ∀ t, t.toKeyList = init.toKeyList → φ w t ≤ φ_ub)
    (X : Fin m → α) (hcont : ∀ i, X i ∈ init)
    : splay.sequence_cost init X ≤
      ∑ i : Fin m, (3 * Real.logb 2 ( size w init / w (X i) ) + 1)
      + φ_ub := by
  have hbound := splay_total_weighted_cost'
    hw m (splaySeq init X) X (splaySeq_succ init X) hbst hcont
  have : splaySeq init X 0 = init := rfl
  rw [this] at hbound
  have : 0 ≤ φ w (splaySeq init X (Fin.last m)) := by apply φ_nonneg hw
  have : (splaySeq init X (Fin.last m)).toKeyList = init.toKeyList :=
    toKeyList_splaySeq init X (Fin.last m)
  have := hφ init (by rfl)
  simp [splay.sequence_cost]; linarith [hbound]


/-! #### Generalization to positive weights -/

/-- Weight function with a positive lower bound. -/
def FnLb (b : ℝ) (w : α → ℝ) : Prop :=
  ∀ x, b ≤ w x

lemma FnPos_of_FnLb {w : α → ℝ} {b : ℝ} (h : FnLb b w) (hb : b > 0) : (FnPos w) := by
  intro x; linarith [h x]

private lemma size_mul_weight (c : ℝ) (t : Tree α) :
  let w' := fun x => c * (w x)
  size w' t = c * (size w t) := by
    induction t with
    | nil => simp
    | node v l r lih rih => unfold size; simp [lih, rih]; linarith

private lemma rank_mul_weight (hw : FnPos w) (c : ℝ) (hc : c > 0) (t : Tree α) (ht : t ≠ nil) :
  let w' := fun x => c * (w x)
  rank w' t = rank w t + Real.logb 2 c := by
    cases t with
    | nil => contradiction
    | node v l r =>
      set w' := fun x => c * (w x)
      have hcnz : c ≠ 0 := by linarith [hc]
      have hsize : size w (l △[v] r) ≠ 0 := by
        simp; linarith [hw v, size_nonneg' hw l, size_nonneg' hw r]
      unfold rank; simp only [w', size_mul_weight, Real.logb_mul hcnz hsize]; linarith

private lemma φ_mul_weight (hw : FnPos w) (c : ℝ) (hc : c > 0) (t : Tree α) :
  let w' := fun x => c * (w x)
  φ w' t = φ w t + t.num_nodes * (Real.logb 2 c) := by
  induction t with
  | nil => simp
  | node v l r lih rih =>
    have : (node v l r) ≠ nil := by simp
    simp only [φ_node, num_nodes_node, Nat.cast_add, Nat.cast_one];
    rw [rank_mul_weight hw c hc (node v l r) this, lih, rih]; linarith

/-- Version of `splay_total_weighted_cost'` for weight functions with an arbitrary positive lower
bound, not necessarily one. -/
theorem splay_total_weighted_cost_lb [LinearOrder α]
    {ε : ℝ} (hε : ε > 0) (hw : FnLb ε w)
    (m : ℕ)
    (t : Fin (m + 1) → Tree α)
    (q : Fin m → α)
    (hseq : ∀ i : Fin m, t i.succ = splay (t i.castSucc) (q i))
    (hbst : (t 0).IsBST)
    (hcont : ∀ i : Fin m, (q i) ∈ (t 0)) :
    ∑ i : Fin m, (splay.cost (t i.castSucc) (q i) : ℝ) ≤
    ∑ i : Fin m, (3 * Real.logb 2 ( size w (t 0) / w (q i) ) + 1)
      + φ w (t 0) - φ w (t (Fin.last m)) := by
  if ε ≥ 1 then
    have hw2 : FnLbOne w := by unfold FnLbOne; intro x; have := hw x; linarith
    exact splay_total_weighted_cost' hw2 m t q hseq hbst hcont
  else
    let w' := fun x => (1/ε) * (w x)
    have hw': FnLbOne w' := by
      unfold FnLbOne; intro x; simp [w']; field_simp [hε]; exact hw x
    have h := splay_total_weighted_cost' hw' m t q hseq hbst hcont
    simp only [one_div, size_mul_weight, w'] at h
    have := φ_mul_weight (FnPos_of_FnLb hw hε) (ε⁻¹) (by field_simp; linarith)
    rw [this (t 0), this (t (Fin.last m))] at h
    have : ∀ i, (t 0).num_nodes = (t i).num_nodes := by
      intro i; induction i using Fin.induction with
      | zero => rfl
      | succ m ih => simp[ih, hseq]
    rw [this (Fin.last m)] at h
    have : ∀ i, ε⁻¹ * size w (t 0) / (ε⁻¹ * w (q i)) = (size w (t 0)) / (w (q i)) := by
      intro i; field_simp
    calc ∑ i, ↑(splay.cost (t i.castSucc) (q i)) ≤
      ∑ x, (3 * Real.logb 2 (ε⁻¹ * size w (t 0) / (ε⁻¹ * w (q x))) + 1) +
        (φ w (t 0) + ↑(t (Fin.last m)).num_nodes * Real.logb 2 ε⁻¹) -
          (φ w (t (Fin.last m)) + ↑(t (Fin.last m)).num_nodes * Real.logb 2 ε⁻¹) := h
      _ ≤ ∑ x, (3 * Real.logb 2 (ε⁻¹ * size w (t 0) / (ε⁻¹ * w (q x))) + 1)
        + φ w (t 0) - φ w (t (Fin.last m)) := by linarith
      _ ≤ ∑ x, (3 * Real.logb 2 (size w (t 0) / (w (q x))) + 1)
        + φ w (t 0) - φ w (t (Fin.last m)) := by simp [this]

private lemma fn_lb_finset_of_FnPos {w : α → ℝ} (hw : FnPos w) (xs : Finset α) :
    ∃ ε > 0, ∀ x ∈ xs, ε ≤ w x := by
  induction xs using Finset.induction with
  | empty => use 1; simp
  | insert x xs hx hε =>
    rcases hε with ⟨ε, hpos, h⟩
    use min ε (w x); constructor
    · exact lt_min hpos (hw x)
    · intro y hy
      simp only [Finset.mem_insert] at hy; rcases hy with hy | hy
      · rw [hy]; exact Std.min_le_right
      · have : min ε (w x) ≤ ε := by exact Std.min_le_left
        linarith [h y hy]
  exact Classical.typeDecidableEq α

theorem FnLb_of_Fintype_of_FnPos {w : α → ℝ} (hα : Fintype α) (hw : FnPos w) :
    ∃ ε > 0, FnLb ε w := by
  set xs := hα.elems
  rcases (fn_lb_finset_of_FnPos hw xs) with ⟨ε, hpos, h⟩
  use ε; constructor
  · exact hpos
  · intro x; exact h x (hα.complete x)

/-- Version of `splay_total_weighted_cost'` for arbitrary positive weight functions on finite types.
-/
theorem splay_total_weighted_cost_pos [LinearOrder α] (hα : Fintype α)
    (hw : FnPos w)
    (m : ℕ)
    (t : Fin (m + 1) → Tree α)
    (q : Fin m → α)
    (hseq : ∀ i : Fin m, t i.succ = splay (t i.castSucc) (q i))
    (hbst : (t 0).IsBST)
    (hcont : ∀ i : Fin m, (q i) ∈ (t 0))
    :
    ∑ i : Fin m, (splay.cost (t i.castSucc) (q i) : ℝ) ≤
    ∑ i : Fin m, (3 * Real.logb 2 ( size w (t 0) / w (q i) ) + 1)
      + φ w (t 0) - φ w (t (Fin.last m)) := by
  rcases (FnLb_of_Fintype_of_FnPos hα hw) with ⟨ε, hε, hεw⟩
  exact splay_total_weighted_cost_lb hε hεw m t q hseq hbst hcont

end SequenceCost

end Weighted

end SplayTree
