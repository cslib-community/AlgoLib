/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Tree.Basic

set_option linter.style.header false

@[expose] public section

/-!
# Binary Tree

In this file we introduce the `Tree` data structure and its basic operations.
-/

variable {α : Type}

/-- A tree node -/
notation:65 l:66 " △[" v "] " r:66 => Tree.node v l r

namespace Tree

/-! ### Core Definitions -/
section CoreDefs

theorem non_empty_exist (s : Tree α) (h : s ≠ .nil) :
    ∃ A k B, s = A △[k] B := by
  induction s <;> grind

def num_nodes : Tree α → ℕ
  | .nil => 0
  | .node _ l r => 1 + num_nodes l + num_nodes r

@[simp] lemma num_nodes_empty : num_nodes (nil : Tree α) = 0 := rfl

@[simp] lemma num_nodes_node (l : Tree α) (k : α) (r : Tree α) :
    (l △[k] r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl

/-- In-order traversal as a list of keys. -/
def toKeyList : Tree α → List α
  | .nil => []
  | l △[k] r => l.toKeyList ++ [k] ++ r.toKeyList

@[simp] lemma toKeyList_empty : toKeyList (nil : Tree α) = [] := rfl

@[simp] lemma toKeyList_node (l : Tree α) (k : α) (r : Tree α) :
    (l △[k] r).toKeyList = l.toKeyList ++ [k] ++ r.toKeyList := rfl

lemma nil_of_toKeyList_empty {t : Tree α} (h : toKeyList t = []) : t = nil := by
  cases t
  · simp
  · simp [List.append_assoc] at h

lemma num_nodes_from_toKeyList (t : Tree α) : t.num_nodes = t.toKeyList.length := by
  induction t with
  | nil => simp
  | node v l r lih rih => simp [lih, rih]; omega


/-- Number of nodes on the search path for `q` in `t`. Zero on the empty
tree; on a node this counts the root plus (if `q ≠ k`) the search path
length in the appropriate subtree. -/
def search_path_len [LinearOrder α] (t : Tree α) (q : α) : ℕ :=
  match t with
  | nil => 0
  | l △[key] r =>
    if q < key then
      1 + l.search_path_len q
    else if key < q then
      1 + r.search_path_len q
    else
      1

lemma search_path_len_le_num_nodes [LinearOrder α] (t : Tree α) (q : α) :
    search_path_len t q ≤ t.num_nodes := by
  induction t with
  | nil => simp[search_path_len]
  | node v l r ihl ihr => simp[search_path_len]; split_ifs; all_goals omega

/--
Remark:
This implementation is not really a "contain function",
because a binary tree could have q >/< key while being in
the left/right subtree of key respectively.
If `contains t q` is true, then `q` is in `t`; but
the converse need not necessarily hold true. The
converse is true for a binary search tree. Hence the name of it.
-/
def BST_contains [LinearOrder α] (t : Tree α) (q : α) : Prop :=
  match t with
  | nil => False
  | l △[key] r =>
    if q < key then
      l.BST_contains q
    else if key < q then
      r.BST_contains q
    else
      True

end CoreDefs


/-! ### Membership -/
section Membership

/-- Inductive membership relation on binary trees, modelled on `List.Mem`. -/
inductive Mem (a : α) : Tree α → Prop where
  /-- `a` is the key at the root. -/
  | here  {l r : Tree α} : Mem a (l △[a] r)
  /-- `a` lies in the left subtree. -/
  | left  {k : α} {l r : Tree α} : Mem a l → Mem a (l △[k] r)
  /-- `a` lies in the right subtree. -/
  | right {k : α} {l r : Tree α} : Mem a r → Mem a (l △[k] r)

instance : Membership α (Tree α) := ⟨fun t a => Mem a t⟩

@[simp] lemma not_mem_nil (a : α) : a ∉ (nil : Tree α) := nofun

@[simp] lemma mem_node_iff {a k : α} {l r : Tree α} :
    a ∈ (l △[k] r) ↔ a = k ∨ a ∈ l ∨ a ∈ r := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | here    => exact Or.inl rfl
    | left h  => exact Or.inr (Or.inl h)
    | right h => exact Or.inr (Or.inr h)
  · rcases h with rfl | h | h
    · exact .here
    · exact .left h
    · exact .right h

/-- Membership agrees with membership in the in-order key list. -/
theorem mem_iff_mem_toKeyList {a : α} {t : Tree α} :
    a ∈ t ↔ a ∈ t.toKeyList := by
  induction t with
  | nil => simp
  | node k l r ihl ihr =>
    rw [toKeyList_node, mem_node_iff]
    simp only [List.mem_append, List.mem_singleton, ihl, ihr]
    tauto

instance decidableMem [DecidableEq α] (a : α) : ∀ t : Tree α, Decidable (a ∈ t)
  | .nil       => isFalse nofun
  | l △[k] r =>
    haveI : Decidable (a ∈ l) := decidableMem a l
    haveI : Decidable (a ∈ r) := decidableMem a r
    decidable_of_iff (a = k ∨ a ∈ l ∨ a ∈ r) mem_node_iff.symm

/-- The search-path `contains` implies membership. The converse needs the BST
invariant. -/
theorem contains_imp_mem [LinearOrder α] {t : Tree α} {q : α} :
    t.BST_contains q → q ∈ t := by
  induction t with
  | nil => simp [BST_contains]
  | node k l r ihl ihr =>
    intro h
    simp only [BST_contains] at h
    split_ifs at h with h1 h2
    · exact .left (ihl h)
    · exact .right (ihr h)
    · have hqk : q = k := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      exact hqk ▸ .here

end Membership


/-! ### Rotations and Mirroring -/
section Transformations

def rotateRight : Tree α → Tree α
  | (a △[x] b) △[y] c => a △[x] (b △[y] c)
  | t => t

def rotateLeft : Tree α → Tree α
  | a △[x] (b △[y] c) => (a △[x] b) △[y] c
  | t => t

/-- Mirror a binary tree: swap every left and right subtree. -/
def mirror : Tree α → Tree α
  | .nil => .nil
  | l △[k] r => r.mirror △[k] l.mirror

@[simp] lemma mirror_empty : (nil : Tree α).mirror = nil := rfl

@[simp] lemma mirror_node (l : Tree α) (k : α) (r : Tree α) :
    (l △[k] r).mirror = r.mirror △[k] l.mirror := rfl

@[simp] lemma mirror_mirror (t : Tree α) : t.mirror.mirror = t := by
  induction t <;> simp_all

@[simp] lemma num_nodes_mirror (t : Tree α) : t.mirror.num_nodes = t.num_nodes := by
  induction t <;> simp_all [num_nodes]; omega

@[simp] lemma toKeyList_mirror (t : Tree α) : t.mirror.toKeyList = t.toKeyList.reverse := by
  induction t <;> simp_all [toKeyList]

@[simp] lemma mirror_rotateRight (t : Tree α) :
    (rotateRight t).mirror = rotateLeft t.mirror := by
  rcases t with _ | ⟨k, (_ | ⟨lk, ll, lr⟩), r⟩ <;>
    simp [rotateRight, rotateLeft, mirror]

@[simp] lemma mirror_rotateLeft (t : Tree α) :
    (rotateLeft t).mirror = rotateRight t.mirror := by
  rcases t with _ | ⟨k, l, (_ | ⟨rk, rl, rr⟩)⟩ <;>
    simp [rotateRight, rotateLeft, mirror]

@[simp] theorem num_nodes_rotateRight (t : Tree α) :
    (rotateRight t).num_nodes = t.num_nodes := by
  rcases t with _ | ⟨k, (_ | ⟨lk, ll, lr⟩), r⟩ <;>
    simp [rotateRight]; omega

@[simp] theorem num_nodes_rotateLeft (t : Tree α) :
    (rotateLeft t).num_nodes = t.num_nodes := by
  have h := num_nodes_rotateRight t.mirror
  simp only [← mirror_rotateLeft, num_nodes_mirror] at h; exact h

end Transformations


/-! ### Contains Characterizations -/
section ContainsLemmas

@[simp] lemma not_contains_empty [LinearOrder α] (q : α) :
    ¬ (nil : Tree α).BST_contains q := nofun

@[simp] lemma contains_node_lt [LinearOrder α] {l : Tree α} {k q : α}
    {r : Tree α} (h : q < k) :
    (l △[k] r).BST_contains q ↔ l.BST_contains q := by
  simp [BST_contains, h]

@[simp] lemma contains_node_gt [LinearOrder α] {l : Tree α} {k q : α}
    {r : Tree α} (h : k < q) :
    (l △[k] r).BST_contains q ↔ r.BST_contains q := by
  simp [BST_contains, h, not_lt_of_gt h]

@[simp] lemma contains_node_not_eq_not_lt [LinearOrder α]
    {l : Tree α} {k q : α} {r : Tree α}
    (h1 : ¬ q = k) (h2 : ¬ q < k) :
    (l △[k] r).BST_contains q ↔ r.BST_contains q := by
  have hgt : k < q := lt_of_le_of_ne (Std.not_lt.mp h2) (Ne.symm (Ne.intro h1))
  simp [BST_contains, hgt, not_lt_of_gt hgt]

end ContainsLemmas


/-! ### Tree Invariants and BST Properties -/
section Invariants

/-- BST invariant parameterised by optional lower/upper key bounds.
`IsBSTAux t lb ub` holds iff every key in `t` lies strictly in `(lb, ub)`
(absent bound = ±∞) and children satisfy the BST property recursively. -/
inductive IsBSTAux [LinearOrder α] : Tree α → Option α → Option α → Prop where
  | nil (lb ub : Option α) : IsBSTAux .nil lb ub
  | node {l r : Tree α} {k : α} {lb ub : Option α}
      (hlb : lb.elim True (· < k))
      (hub : ub.elim True (k < ·))
      (hl  : IsBSTAux l lb (some k))
      (hr  : IsBSTAux r (some k) ub) :
      IsBSTAux (l △[k] r) lb ub

def IsBST [LinearOrder α] (t : Tree α) : Prop := t.IsBSTAux none none

end Invariants

/-! ### Accessor Lemmas for IsBST -/
section IsBSTAccessors

@[simp] lemma IsBSTAux_nil [LinearOrder α] (lb ub : Option α) :
    IsBSTAux (.nil : Tree α) lb ub := .nil lb ub

@[simp] lemma IsBSTAux_node [LinearOrder α] (l : Tree α) (k : α) (r : Tree α)
    (lb ub : Option α) :
    IsBSTAux (l △[k] r) lb ub ↔
      lb.elim True (· < k) ∧ ub.elim True (k < ·) ∧
      IsBSTAux l lb (some k) ∧ IsBSTAux r (some k) ub :=
  ⟨fun h => by cases h with | node hlb hub hl hr => exact ⟨hlb, hub, hl, hr⟩,
   fun ⟨h1, h2, h3, h4⟩ => .node h1 h2 h3 h4⟩

@[simp] lemma IsBST_node [LinearOrder α] (l : Tree α) (k : α) (r : Tree α) :
    IsBST (l △[k] r) ↔ IsBSTAux l none (some k) ∧ IsBSTAux r (some k) none := by
  simp [IsBST, IsBSTAux_node]

private lemma IsBSTAux_children_none [LinearOrder α] (t : Tree α) (x y : Option α)
    (h : IsBSTAux t x y) : IsBSTAux t none y ∧ IsBSTAux t x none ∧ IsBSTAux t none none := by
  induction t generalizing x y with
  | nil => simp
  | node k l r lih rih =>
    simp only [IsBSTAux_node] at h
    rcases h with ⟨_, _, h1, h2⟩
    rcases lih x (some k) h1 with ⟨_,_,_⟩
    rcases rih (some k) y h2 with ⟨_,_,_⟩
    simp only [IsBSTAux_node, Option.elim_none, true_and]; split_ands; all_goals assumption

private lemma IsBST_of_IsBSTAux [LinearOrder α] {t : Tree α} {x y : Option α}
    (h : IsBSTAux t x y) : IsBST t := by
  unfold IsBST; rcases IsBSTAux_children_none t x y h with ⟨_,_,_⟩; assumption

theorem IsBST_left_of_IsBST [LinearOrder α] {k : α} {l r : Tree α}
    (hbst : IsBST (l △[k] r)) : IsBST l := by
  simp only [IsBST, IsBSTAux_node, Option.elim_none, true_and] at hbst; rcases hbst with ⟨hl,_⟩
  exact IsBST_of_IsBSTAux hl

theorem IsBST_right_of_IsBST [LinearOrder α] {k : α} {l r : Tree α}
    (hbst : IsBST (l △[k] r)) : IsBST r := by
  simp only [IsBST, IsBSTAux_node, Option.elim_none, true_and] at hbst; rcases hbst with ⟨_,hr⟩
  exact IsBST_of_IsBSTAux hr

end IsBSTAccessors


/-! ### BST Membership -/
section BSTMembership

/-- In a BST subtree with upper bound `some ub`, every member is `< ub`. -/
private lemma IsBSTAux.lt_of_mem_ub [LinearOrder α] {t : Tree α} {q ub : α}
    {lb : Option α} (h : IsBSTAux t lb (some ub)) (hmem : q ∈ t) : q < ub := by
  induction t generalizing lb ub with
  | nil => simp at hmem
  | node k l r ihl ihr =>
    obtain ⟨_, hub, hl, hr⟩ := (IsBSTAux_node l k r lb (some ub)).mp h
    rcases mem_node_iff.mp hmem with rfl | hml | hmr
    · exact hub
    · exact lt_trans (ihl hl hml) hub
    · exact ihr hr hmr

/-- In a BST subtree with lower bound `some lb`, every member is `> lb`. -/
private lemma IsBSTAux.gt_of_mem_lb [LinearOrder α] {t : Tree α} {q lb : α}
    {ub : Option α} (h : IsBSTAux t (some lb) ub) (hmem : q ∈ t) : lb < q := by
  induction t generalizing lb ub with
  | nil => simp at hmem
  | node k l r ihl ihr =>
    obtain ⟨hlb, _, hl, hr⟩ := (IsBSTAux_node l k r (some lb) ub).mp h
    rcases mem_node_iff.mp hmem with rfl | hml | hmr
    · exact hlb
    · exact ihl hl hml
    · exact lt_trans hlb (ihr hr hmr)

/-- Membership implies the BST search path finds the key, for any bound
configuration. -/
private theorem IsBSTAux.mem_imp_contains [LinearOrder α] {t : Tree α} {q : α}
    {lb ub : Option α} (h : IsBSTAux t lb ub) (hmem : q ∈ t) : t.BST_contains q := by
  induction t generalizing lb ub with
  | nil => simp at hmem
  | node k l r ihl ihr =>
    obtain ⟨_, _, hl, hr⟩ := (IsBSTAux_node l k r lb ub).mp h
    rcases mem_node_iff.mp hmem with rfl | hml | hmr
    · simp [BST_contains]
    · have hlt : q < k := IsBSTAux.lt_of_mem_ub hl hml
      simp only [BST_contains, if_pos hlt]
      exact ihl hl hml
    · have hgt : k < q := IsBSTAux.gt_of_mem_lb hr hmr
      simp only [BST_contains, if_neg (not_lt.mpr hgt.le), if_pos hgt]
      exact ihr hr hmr

/-- Converse of `contains_imp_mem` for BSTs: membership implies the search-path
`contains` succeeds. -/
theorem mem_imp_contains [LinearOrder α] {t : Tree α} (hbst : IsBST t)
    {q : α} (hmem : q ∈ t) : t.BST_contains q :=
  IsBSTAux.mem_imp_contains hbst hmem

/-- For BSTs, the search-path `contains` coincides with membership. -/
theorem contains_iff_mem [LinearOrder α] {t : Tree α} (hbst : IsBST t) {q : α} :
    t.BST_contains q ↔ q ∈ t :=
  ⟨contains_imp_mem, mem_imp_contains hbst⟩

/-- For BSTs, all keys in the left subtree are smaller than the root key. -/
theorem lt_of_IsBST_left [LinearOrder α] (l : Tree α) (k : α) (r : Tree α)
    (hbst : IsBST (l △[k] r)) {q : α} (hql : q ∈ l) : q < k := by
  simp only [IsBST_node] at hbst; rcases hbst with ⟨hl,_⟩
  exact IsBSTAux.lt_of_mem_ub hl hql

/-- For BSTs, all keys in the right subtree are greater than the root key. -/
theorem gt_of_IsBST_right [LinearOrder α] (l : Tree α) (k : α) (r : Tree α)
    (hbst : IsBST (l △[k] r)) {q : α} (hqr : q ∈ r) : k < q := by
  simp only [IsBST_node] at hbst; rcases hbst with ⟨_,hr⟩
  exact IsBSTAux.gt_of_mem_lb hr hqr

/-- A tree that contains something is not nil. -/
theorem nonnil_of_mem {t : Tree α} (q : α) (hq : q ∈ t) : (t ≠ nil) := by
  by_contra
  have : q ∉ t := by rw[this]; exact not_mem_nil q
  contradiction

end BSTMembership

end Tree

/-! ### BST Structure -/
section BSTStructure

/-- A binary search tree: a `Tree` bundled with a proof of the `IsBST` invariant. -/
structure BST (α : Type) [LinearOrder α] where
  tree : Tree α
  hBST : Tree.IsBST tree

namespace BST

/-- Checks if the BST contains a given key by delegating to the underlying tree. -/
def contains [LinearOrder α] (t : BST α) (q : α) : Prop :=
  t.tree.BST_contains q

end BST

end BSTStructure
