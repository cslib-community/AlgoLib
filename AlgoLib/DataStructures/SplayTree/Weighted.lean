/-
Copyright (c) 2026 AlgoLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Aram Berendsohn, Antoine du Fresne von Hohenesche
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

import AlgoLib.DataStructures.SplayTree.Complexity -- Required for some lemmas
import AlgoLib.DataStructures.SplayTree.Correctness -- Required for some lemmas

/-!
# Weighted Bounds for Splay Trees

An extension of the Complexity module. Formalizes Sleator and Tarjan's weighted analysis of
(bottom-up) splay trees and their Access Lemma.

The Access Lemma allows defining an arbitrary weight `w(v) ≥ 1` for each node. It bounds the
amortized cost of an access by `O(1 + log(W/w(v)))`, where `W` is the total weight of all nodes in
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

lemma FnPos_of_FnLbOne {w : α → ℝ} (h : FnLbOne w) : (FnPos w) := fun x => one_pos.trans_le (h x)

lemma FnNonneg_of_FnPos {w : α → ℝ} (h : FnPos w) : (FnNonneg w) := fun x => (h x).le

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

@[simp] lemma size_empty : size w (.nil : Tree α) = 0 := rfl
@[simp] lemma size_node {v : α} {l r : Tree α} : size w (node v l r) = w v + size w l + size w r :=
  rfl

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
  | nil => rfl
  | node v l r ihl ihr => exact add_nonneg (add_nonneg (hw v) ihl) ihr

private lemma size_nonneg' (hw : FnPos w) (t : Tree α) : 0 ≤ size w t :=
  size_nonneg (FnNonneg_of_FnPos hw) t

private lemma size_nonneg'' (hw : FnLbOne w) (t : Tree α) : 0 ≤ size w t :=
  size_nonneg (FnNonneg_of_FnLbOne hw) t

lemma size_ge_root_value (hw : FnNonneg w) (v : α) (l r : Tree α) :
    w v ≤ size w (node v l r) :=
  le_add_of_le_of_nonneg (le_add_of_nonneg_right (size_nonneg hw l)) (size_nonneg hw r)

lemma size_ge_left_child (hw : FnNonneg w) (v : α) (l r : Tree α) :
    size w l ≤ size w (node v l r) := by
  simp [size_node]; linarith [hw v, size_nonneg hw r]

lemma size_ge_right_child (hw : FnNonneg w) (v : α) (l r : Tree α) :
    size w r ≤ size w (node v l r) := by
  simp [size_node]; linarith [hw v, size_nonneg hw l]

lemma size_pos_of_non_nil (hw : FnPos w) (t : Tree α) (h : t ≠ nil) : 0 < size w t := by
  obtain ⟨l, v, r, rfl⟩ := non_empty_exist t h
  exact (hw v).trans_le (size_ge_root_value (FnNonneg_of_FnPos hw) v l r)

lemma size_from_toKeyList (t : Tree α) :
    size w t = (t.toKeyList.map w).sum := by
  induction t <;> simp [*]; ring

lemma size_zero_iff_empty (hw : FnPos w) (t : Tree α) : size w t = 0 ↔ t = nil :=
  ⟨not_imp_not.mp fun ht => (size_pos_of_non_nil hw t ht).ne', fun h => h ▸ rfl⟩

lemma size_le_size_of_toKeyList_Sublist (hw : FnNonneg w)
    {s t : Tree α} (h : s.toKeyList.Sublist t.toKeyList) :
    size w s ≤ size w t := by
  rw [size_from_toKeyList, size_from_toKeyList]
  exact (h.map w).sum_le_sum (List.forall_mem_map.mpr fun x _ => hw x)

/-! #### Splay-tree-related size lemmas -/

@[simp]
theorem size_bringUp (d : Dir) (t : Tree α) :
    size w (d.bringUp t) = size w t := by
  cases d <;> simp [Dir.bringUp]

@[simp]
theorem size_applyChild (d : Dir) (op : Tree α → Tree α)
    (hop : ∀ s, size w (op s) = size w s) (t : Tree α) :
    size w (applyChild d op t) = size w t := by
  cases t <;> cases d <;> simp [applyChild, hop]

lemma size_Frame_attach (s : Tree α) (f : Frame α) :
    size w (f.attach s) = size w s + w f.key + size w f.sibling := by
  rcases f with ⟨_ | _, k, sib⟩ <;> simp only [Frame.attach, size_node] <;> ring

@[simp] lemma size_splay [LinearOrder α] (s : Tree α) (q : α) : size w (splay s q) = size w s := by
  rw [size_from_toKeyList, size_from_toKeyList]; rw [toKeyList_splay]

/-! #### Basic rank lemmas -/

@[simp] lemma rank_empty : rank w (.nil : Tree α) = 0 := rfl

lemma rank_nonneg (hw : FnLbOne w) (t : Tree α) : 0 ≤ rank w t := by
  cases t with
  | nil => rfl
  | node v l r =>
    exact Real.logb_nonneg one_lt_two
      ((hw v).trans (size_ge_root_value (FnNonneg_of_FnLbOne hw) v l r))

private lemma rank_eq_logb_size (t : Tree α) : rank w t = Real.logb 2 (size w t) := by
  cases t <;> simp [rank]

lemma rank_le_of_size_le (hw : FnLbOne w) (s t : Tree α) (h : size w s ≤ size w t) :
    rank w s ≤ rank w t := by
  rcases eq_or_ne s nil with rfl | hs
  · exact rank_nonneg hw t
  · rw [rank_eq_logb_size, rank_eq_logb_size]
    exact Real.logb_le_logb_of_le one_lt_two (size_pos_of_non_nil (FnPos_of_FnLbOne hw) s hs) h

lemma rank_eq_of_toKeyList_eq {s t : Tree α}
    (h : s.toKeyList = t.toKeyList) : rank w s = rank w t := by
  rw [rank_eq_logb_size, rank_eq_logb_size, size_from_toKeyList, size_from_toKeyList, h]


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
  | node k l r ihl ihr => exact add_nonneg (add_nonneg (rank_nonneg hw _) ihl) ihr


/-! #### Potential of subtrees versus the whole tree -/

theorem φ_le_attach (hw : FnLbOne w) (c : Tree α) (f : Frame α) :
    φ w c ≤ φ w (f.attach c) := by
  rcases f with ⟨_ | _, k, s⟩ <;> simp only [Frame.attach, φ_node] <;>
    linarith [rank_nonneg hw (c △[k] s), rank_nonneg hw (s △[k] c), φ_nonneg hw s]

theorem φ_le_reassemble (hw : FnLbOne w) (c : Tree α) (path : List (Frame α)) :
    φ w c ≤ φ w (reassemble c path) := by
  induction path generalizing c with
  | nil => rfl
  | cons f rest ih => exact (φ_le_attach hw c f).trans (ih _)

theorem φ_descend_subtree_le [LinearOrder α] (hw : FnLbOne w) (t : Tree α) (q : α) :
    φ w (descend t q).1 ≤ φ w t :=
  (φ_le_reassemble hw _ _).trans_eq (congrArg (φ w) (descend_preserves_tree t q))


/-! #### Mirror preserves rank and potential -/

lemma rank_mirror (t : Tree α) : rank w t.mirror = rank w t := by
  simp [rank_eq_logb_size, size_from_toKeyList]

lemma φ_mirror (t : Tree α) : φ w t.mirror = φ w t := by
  induction t with
  | nil => rfl
  | node v l r =>
    rw [mirror_node, φ_node, φ_node, ← mirror, rank_mirror]
    simp_all; linarith


/-! #### Splay step potential bounds -/

theorem φ_zig (hw : FnLbOne w) (c : Tree α) (f : Frame α) :
    φ w (f.dir.bringUp (f.attach c)) - φ w (f.attach c) ≤
      rank w (f.dir.bringUp (f.attach c)) - rank w c := by
  rcases f with ⟨_ | _, key, sib⟩ <;> rcases c with _ | ⟨k, l, r⟩ <;>
    simp only [Dir.bringUp, rotateLeft, rotateRight, Frame.attach, φ_node, sub_self, rank_empty,
      sub_zero, rank_nonneg hw]
  · linarith [rank_le_of_size_le hw (r △[key] sib) ((l △[k] r) △[key] sib)
      (by simp; linarith [hw k, size_nonneg'' hw l])]
  · linarith [rank_le_of_size_le hw (sib △[key] l) (sib △[key] (l △[k] r))
      (by simp; linarith [hw k, size_nonneg'' hw r])]

private theorem φ_zigzig_left (hw : FnLbOne w)
    (a b c : α) (t1 t2 t3 t4 : Tree α) :
    let x := node a t1 t2 -- The node we're rotating
    let s := node c (node b x t3) t4 -- The initial tree
    let s' := rotateRight (rotateRight s) -- The resulting tree
    φ w s' - φ w s + 2 ≤ 3 * (rank w s' - rank w x) := by
  intro x s s'
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
  rcases f1 with ⟨d, k1, n1⟩; rcases f2 with ⟨_, k2, n2⟩; subst heq
  cases d
  · exact φ_zigzig_left hw a k1 k2 l r n1 n2
  · have h := φ_zigzig_left hw a k1 k2 r.mirror l.mirror n1.mirror n2.mirror
    simp only [Frame.attach, Dir.bringUp, rotateRight, rotateLeft] at h ⊢
    simpa only [← mirror_node, φ_mirror, rank_mirror] using h

private theorem φ_zigzag_left (hw : FnLbOne w)
    (a b c : α) (t1 t2 t3 t4 : Tree α) :
    let x := node b t2 t3 -- The node we're rotating
    let s := node a t1 (node c x t4) -- The initial tree
    let s' := rotateLeft (applyChild .R rotateRight s) -- The resulting tree
    φ w s' - φ w s + 2 ≤ 3 * (rank w s' - rank w x) := by
  intro x s s'
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
      rank w (node a t1 t2) + rank w (node c t3 t4) - rank w (node c x t4) - rank w x) := by
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
  rcases f1 with ⟨d1, k1, n1⟩; rcases f2 with ⟨d2, k2, n2⟩
  cases d1 <;> cases d2 <;> simp_all +decide only [ne_eq]
  · exact φ_zigzag_left hw k2 a k1 n2 l r n1
  · have h := φ_zigzag_left hw k2 a k1 n2.mirror r.mirror l.mirror n1.mirror
    simp only [Frame.attach, Dir.bringUp, rotateRight, rotateLeft, applyChild] at h ⊢
    simpa only [← mirror_node, φ_mirror, rank_mirror] using h


/-! #### Telescoping: potential change along the full splayUp -/

lemma φ_attach_congr {s s' : Tree α} (f : Frame α)
    (h : size w s = size w s') :
    φ w (f.attach s') - φ w (f.attach s) = φ w s' - φ w s := by
  rcases f with ⟨_ | _, k, sib⟩ <;> simp [Frame.attach, rank, h]

lemma φ_reassemble_congr {s s' : Tree α} (path : List (Frame α))
    (h : size w s = size w s') :
    φ w (reassemble s' path) - φ w (reassemble s path) = φ w s' - φ w s := by
  induction path generalizing s s' with
  | nil => simp
  | cons f rest ih => exact (ih (by simp [size_Frame_attach, h])).trans (φ_attach_congr f h)

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
      rw [splayUp_cons_cons]; simp only [List.length_cons, reassemble_cons]; push_cast
      set s := f2.attach (f1.attach (node a l r))
      split_ifs with hdir
      · set step_tree := f2.dir.bringUp (f2.dir.bringUp s)
        have hsize : size w step_tree = size w s := by
          simp [step_tree]
        have : step_tree ≠ nil := by
          unfold step_tree; apply Dir.bringUp_ne_nil_of_ne_nil; apply Dir.bringUp_ne_nil_of_ne_nil
          unfold s; apply Frame.attach_ne_nil
        nlinarith [ih step_tree this,
          φ_reassemble_congr rest hsize.symm, φ_zigzig hw a l r f1 f2 hdir]
      · set step_tree := f2.dir.bringUp (applyChild f2.dir f1.dir.bringUp s)
        have hsize : size w step_tree = size w s := by
          simp [step_tree]
        have : step_tree ≠ nil := by
          unfold step_tree; apply Dir.bringUp_ne_nil_of_ne_nil;
          apply applyChild_ne_nil_of_ne_nil
          unfold s; apply Frame.attach_ne_nil
        nlinarith [ih step_tree this,
          φ_reassemble_congr rest hsize.symm, φ_zigzag hw a l r f1 f2 hdir]

/-! #### The main amortized bound -/

/-- Slightly weaker version of Sleator and Tarjan's access lemma: Does not take into account the
  subtree rooted at q, only the weight of q itself; also requires weights at least one. -/
theorem splay_access_lemma [LinearOrder α]
    (hw : FnLbOne w) (t : Tree α) (q : α) (hbst : IsBST t) (hq : q ∈ t) :
    φ w (splay t q) - φ w t + splay.cost t q ≤
      3 * Real.logb 2 (size w t / w q) + 1 := by
  rcases hdecomp : descend t q with ⟨reached, path⟩
  have : ∃ l r, (descend t q).1 = node q l r := descend_contains' t q hbst hq
  have hreached : ∃ l r, reached = node q l r := by simp_all only
  have hpres := descend_preserves_tree t q
  rw [hdecomp] at hpres; simp only at hpres
  rcases hreached with ⟨l, r, hreached⟩
  have h_cost : splay.cost t q = path.length := by simp [splay.cost, hdecomp, hreached]
  rw [h_cost]
  have h_eq : splay t q = splayUp (l △[q] r) path := by simp [splay, hdecomp, hreached]
  rw [h_eq]
  have hφ := φ_splayUp hw (l △[q] r) (by simp) path
  rw [←hreached, hpres, hreached] at hφ
  have hrank_eq : rank w (splayUp (l △[q] r) path) = rank w t := by
    have h := rank_splay w t q; simp only [splay, hdecomp, hreached] at h; exact h
  have htnn : t ≠ nil := ne_nil_of_mem q hq
  calc φ w (splayUp (l △[q] r) path) - φ w t + ↑path.length
      ≤ 3 * (rank w (splayUp (l △[q] r) path) - rank w (l △[q] r)) + 1 := by exact_mod_cast hφ
    _ ≤ 3 * (rank w t - rank w (l △[q] r)) + 1 := by simp [hrank_eq]
    _ ≤ 3 * (Real.logb 2 (size w t) - rank w (l △[q] r)) + 1 := by simp [rank]
    _ ≤ 3 * (Real.logb 2 (size w t) - Real.logb 2 (w q)) + 1 := by
      have : Real.logb 2 (w q) ≤ rank w (l △[q] r) := by
        simp only [rank, size_node]
        apply Real.logb_le_logb_of_le (by norm_num) (by linarith [hw q])
        linarith [size_nonneg'' hw l, size_nonneg'' hw r]
      linarith
    _ ≤ 3 * Real.logb 2 (size w t / w q) + 1 := by
      have hsizepos : size w t ≠ 0 := by linarith [size_pos_of_non_nil (FnPos_of_FnLbOne hw) t htnn]
      have hwqpos : w q ≠ 0 := by linarith [hw q]
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
  have := Fintype.sum_mono hamort
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at this
  linarith [Fin.sum_univ_castSucc fun i => Φ (s i), Fin.sum_univ_succ fun i => Φ (s i)]

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
    ∑ i : Fin m, (3 * Real.logb 2 (size w (t 0) / w (q i)) + 1) +
      φ w (t 0) - φ w (t (Fin.last m)) := by
  let B := fun i => (3 * Real.logb 2 (size w (t 0) / w (q i)) + 1)
  have ht : ∀ i : Fin (m+1), (t 0).toKeyList = (t i).toKeyList := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => rw [hseq i, toKeyList_splay, ih]
  apply total_cost_bound m t (fun i => (splay.cost (t i.castSucc) (q i) : ℝ)) (φ w) B
  intro i
  rw [hseq i]
  have hb := splay_access_lemma hw (t i.castSucc) (q i)
    (IsBST_of_toKeyList_eq (ht i.castSucc).symm hbst)
    (by simp [mem_iff_mem_toKeyList, ←ht i.castSucc, mem_iff_mem_toKeyList.mp (hcont i)])
  calc φ w (splay (t i.castSucc) (q i)) - φ w (t i.castSucc) + splay.cost (t i.castSucc) (q i)
    ≤ 3 * Real.logb 2 (size w (t i.castSucc) / w (q i)) + 1 := hb
  _ ≤ 3 * Real.logb 2 (size w (t 0) / w (q i)) + 1 := by simp [size_from_toKeyList, ht i.castSucc]

/-- Simplified version of `splay_total_weighted_cost'` using a general tree potential upper bound.
-/
theorem splay_total_weighted_cost [LinearOrder α]
    (hw : FnLbOne w)
    (m : ℕ)
    (init : Tree α) (hbst : init.IsBST)
    {φ_ub : ℝ} (hφ : ∀ t, t.toKeyList = init.toKeyList → φ w t ≤ φ_ub)
    (X : Fin m → α) (hcont : ∀ i, X i ∈ init) :
    splay.sequence_cost init X ≤
      ∑ i : Fin m, (3 * Real.logb 2 (size w init / w (X i)) + 1) + φ_ub := by
  have hbound := splay_total_weighted_cost'
    hw m (splaySeq init X) X (splaySeq_succ init X) hbst hcont
  have : splaySeq init X 0 = init := rfl
  rw [this] at hbound
  have : 0 ≤ φ w (splaySeq init X (Fin.last m)) := by apply φ_nonneg hw
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
  simp [size_from_toKeyList, List.sum_map_mul_left]

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
    ∑ i : Fin m, (3 * Real.logb 2 (size w (t 0) / w (q i)) + 1)
      + φ w (t 0) - φ w (t (Fin.last m)) := by
  let w' := fun x => (1/ε) * (w x)
  have hw' : FnLbOne w' := by
    unfold FnLbOne; intro x; simp [w']; field_simp [hε]; exact hw x
  have h := splay_total_weighted_cost' hw' m t q hseq hbst hcont
  simp only [one_div, size_mul_weight, w'] at h
  have := φ_mul_weight (FnPos_of_FnLb hw hε) (ε⁻¹) (by field_simp; linarith)
  rw [this (t 0), this (t (Fin.last m))] at h
  have : ∀ i, (t 0).num_nodes = (t i).num_nodes := by
    intro i; induction i using Fin.induction with
    | zero => rfl
    | succ m ih => simp [ih, hseq]
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

theorem FnLb_of_Finite_of_FnPos {w : α → ℝ} [Finite α] (hw : FnPos w) :
    ∃ ε > 0, FnLb ε w := by
  cases isEmpty_or_nonempty α
  · exact ⟨1, one_pos, isEmptyElim⟩
  · obtain ⟨x, hx⟩ := Finite.exists_min w
    exact ⟨w x, hw x, hx⟩

/-- Version of `splay_total_weighted_cost'` for arbitrary positive weight functions on finite types.
-/
theorem splay_total_weighted_cost_pos [LinearOrder α] [Finite α]
    (hw : FnPos w)
    (m : ℕ)
    (t : Fin (m + 1) → Tree α)
    (q : Fin m → α)
    (hseq : ∀ i : Fin m, t i.succ = splay (t i.castSucc) (q i))
    (hbst : (t 0).IsBST)
    (hcont : ∀ i : Fin m, (q i) ∈ (t 0)) :
    ∑ i : Fin m, (splay.cost (t i.castSucc) (q i) : ℝ) ≤
    ∑ i : Fin m, (3 * Real.logb 2 (size w (t 0) / w (q i)) + 1)
      + φ w (t 0) - φ w (t (Fin.last m)) := by
  rcases FnLb_of_Finite_of_FnPos hw with ⟨ε, hε, hεw⟩
  exact splay_total_weighted_cost_lb hε hεw m t q hseq hbst hcont

end SequenceCost

end Weighted

end SplayTree
