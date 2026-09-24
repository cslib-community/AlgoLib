import AlgoLib.DataStructures.SplayTree.Weighted

/-!
# Static optimality of Splay Trees

Formalizes static optimality of splay trees with an O(n²) overall overhead, as per David Eppstein's
analysis (https://11011110.github.io/blog/2008/02/07/static-optimality-for.html).
-/

variable {α : Type}

namespace SplayTree

namespace Weighted

open Tree

def staticCost {m : ℕ} [LinearOrder α] (t : Tree α) (X : Fin m → α) : ℕ :=
  ∑ i, search_path_len t (X i)

private noncomputable def staticWeight [LinearOrder α] (s : Tree α) (q : α) : ℝ :=
  3^(s.num_nodes - search_path_len s q : ℝ)

private lemma staticWeight_ge_one [LinearOrder α] (s : Tree α) (q : α) :
    staticWeight s q ≥ 1 := by
  simp only [staticWeight, ge_iff_le]; rw[←Real.rpow_zero 3]
  apply Real.rpow_le_rpow_of_exponent_le
  · simp
  · simp; linarith [search_path_len_le_num_nodes s q]

private lemma staticWeight_pos [LinearOrder α] (s : Tree α) (q : α) : staticWeight s q > 0 := by
  simp [FnPos_of_FnLbOne (staticWeight_ge_one s) q]

private lemma search_path_len_left [LinearOrder α] (v : α) (l r : Tree α) (q : α) (hqv : q < v) :
    search_path_len (node v l r) q = 1 + search_path_len l q := by
  simp [search_path_len, hqv]

private lemma staticWeight_left [LinearOrder α] (v : α) (l r : Tree α) (q : α) (hqv : q < v) :
    let s := node v l r
    staticWeight s q = 3^(s.num_nodes - l.num_nodes-1 : ℝ) * staticWeight l q := by
  simp only [staticWeight, num_nodes_node, Nat.cast_add, Nat.cast_one]
  rw [←Real.rpow_add (by simp)]
  apply (Real.rpow_right_inj (by simp) (by simp)).mpr
  simp [search_path_len_left v l r q hqv]; linarith

private lemma staticWeight_size_left [LinearOrder α]
    {v : α} {l r : Tree α} (hbst : (node v l r).IsBST) :
    let s := node v l r
    size (staticWeight s) l = 3^(s.num_nodes - l.num_nodes-1 : ℝ) * size (staticWeight l) l := by
  simp only [size_from_toKeyList]
  have hlv : ∀ x ∈ l.toKeyList, x < v := by
    intro x hx
    apply lt_of_IsBST_left l v r hbst
    exact mem_iff_mem_toKeyList.mpr hx
  have : ∀ xs, xs.Sublist l.toKeyList → (List.map (staticWeight (l △[v] r)) xs).sum =
      3 ^ ((l △[v] r).num_nodes - ↑l.num_nodes - 1 : ℝ) * (List.map (staticWeight l) xs).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro hsub
      have hxv : x < v := by apply hlv; exact List.mem_of_cons_sublist hsub
      have := ih (List.sublist_of_cons_sublist hsub)
      simp [this, staticWeight_left v l r x hxv]; linarith
  exact this l.toKeyList (by rfl)


private lemma search_path_len_right [LinearOrder α] (v : α) (l r : Tree α) (q : α) (hqv : v < q) :
    search_path_len (node v l r) q = 1 + search_path_len r q := by
  simp only [search_path_len, hqv, ↓reduceIte, ite_eq_right_iff, Nat.add_left_cancel_iff]
  intro h'; apply le_of_lt at h'; apply not_le_of_gt at hqv; contradiction

private lemma staticWeight_right [LinearOrder α] (v : α) (l r : Tree α) (q : α) (hqv : v < q) :
    let s := node v l r
    staticWeight s q = 3^(s.num_nodes - r.num_nodes-1 : ℝ) * staticWeight r q := by
  simp only [staticWeight, num_nodes_node, Nat.cast_add, Nat.cast_one]
  rw [←Real.rpow_add (by simp)]
  apply (Real.rpow_right_inj (by simp) (by simp)).mpr
  simp [search_path_len_right v l r q hqv]; linarith

private lemma staticWeight_size_right [LinearOrder α]
    {v : α} {l r : Tree α} (hbst : (node v l r).IsBST) :
    let s := node v l r
    size (staticWeight s) r = 3^(s.num_nodes - r.num_nodes-1 : ℝ) * size (staticWeight r) r := by
  simp only [size_from_toKeyList]
  have hrv : ∀ x ∈ r.toKeyList, v < x := by
    intro x hx
    apply gt_of_IsBST_right l v r hbst
    exact mem_iff_mem_toKeyList.mpr hx
  have : ∀ xs, xs.Sublist r.toKeyList → (List.map (staticWeight (l △[v] r)) xs).sum =
      3 ^ ((l △[v] r).num_nodes - ↑r.num_nodes - 1 : ℝ) * (List.map (staticWeight r) xs).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro hsub
      have hxv : v < x := by apply hrv; exact List.mem_of_cons_sublist hsub
      have := ih (List.sublist_of_cons_sublist hsub)
      simp [this, staticWeight_right v l r x hxv]; linarith
  exact this r.toKeyList (by rfl)


private lemma staticWeight_size_self_ub [LinearOrder α] (s : Tree α) (hbst : s.IsBST) :
    size (staticWeight s) s ≤ 3 ^ s.num_nodes := by
  induction s with
  | nil => simp
  | node v l r lih rih =>
    let s := node v l r
    simp only [size]
    have h1 : staticWeight (l △[v] r) v ≤ 3^(s.num_nodes - 1 : ℝ) := by
      simp[staticWeight, s, search_path_len]
    have hl : size (staticWeight (l △[v] r)) l ≤ 3^(s.num_nodes - 1 : ℝ) := by
      calc size (staticWeight (l △[v] r)) l
          = 3^(s.num_nodes - l.num_nodes-1 : ℝ) * size (staticWeight l) l := by
            exact staticWeight_size_left hbst
        _ ≤ 3^(s.num_nodes - l.num_nodes-1 : ℝ) * 3 ^ l.num_nodes := by
            gcongr; apply lih; exact IsBST_left_of_IsBST hbst
        _ = 3^(s.num_nodes - 1 : ℝ) := by
          rw [←Real.rpow_natCast 3]
          rw [←Real.rpow_add (show 0 < 3 by simp)]
          apply (Real.rpow_right_inj (by simp) (by simp)).mpr
          linarith
    have hr : size (staticWeight (l △[v] r)) r ≤ 3^(s.num_nodes - 1 : ℝ) := by
      calc size (staticWeight (l △[v] r)) r
          = 3^(s.num_nodes - r.num_nodes-1 : ℝ) * size (staticWeight r) r := by
            exact staticWeight_size_right hbst
        _ ≤ 3^(s.num_nodes - r.num_nodes-1 : ℝ) * 3 ^ r.num_nodes := by
            gcongr; apply rih; exact IsBST_right_of_IsBST hbst
        _ = 3^(s.num_nodes - 1 : ℝ) := by
          rw [←Real.rpow_natCast 3]
          rw [←Real.rpow_add (show 0 < 3 by simp)]
          apply (Real.rpow_right_inj (by simp) (by simp)).mpr
          linarith
    have : 3^s.num_nodes = (3 : ℝ) * 3^(s.num_nodes - 1 : ℝ) := by
      have := Real.rpow_add (show 0 < 3 by simp) (s.num_nodes-1) 1
      simp only [sub_add_cancel, Real.rpow_natCast, Real.rpow_one] at this
      simp only [this]; apply mul_comm
    linarith

private lemma staticWeight_size_ub [LinearOrder α] (s t : Tree α)
    (hst : t.toKeyList.Sublist s.toKeyList) (hbst : s.IsBST) :
    size (staticWeight s) t ≤ 3 ^ s.num_nodes := by
  have := size_le_size_of_toKeyList_Sublist (FnNonneg_of_FnPos (staticWeight_pos s)) hst
  have := staticWeight_size_self_ub s hbst
  linarith

private lemma staticWeight_rank_ub [LinearOrder α] (s t : Tree α)
    (hst : t.toKeyList.Sublist s.toKeyList) (hbst : s.IsBST) :
    rank (staticWeight s) t ≤ s.num_nodes * Real.logb 2 3 := by
  unfold rank; cases t with
  | nil =>
    simp only; apply mul_nonneg (by simp)
    · exact Real.logb_nonneg (by simp) (by simp)
  | node v l r =>
    simp only
    rw [←Real.logb_pow 2 3]; apply logb_mono
    · apply size_pos_of_non_nil (staticWeight_pos s)
      simp
    · exact staticWeight_size_ub s _ hst hbst

private lemma staticWeight_φ_ub_aux [LinearOrder α] (s t : Tree α)
    (hst : t.toKeyList.Sublist s.toKeyList) (hbst : s.IsBST) :
    φ (staticWeight s) t ≤ s.num_nodes * t.num_nodes * Real.logb 2 3 := by
  induction t with
  | nil => simp
  | node v l r lih rih =>
    simp [φ]
    have : l.toKeyList.Sublist s.toKeyList := by
      have : l.toKeyList.Sublist (node v l r).toKeyList := by simp [toKeyList]
      exact List.Sublist.trans this hst
    simp [this] at lih
    have : r.toKeyList.Sublist s.toKeyList := by
      have : r.toKeyList.Sublist (node v l r).toKeyList := by simp [toKeyList]
      exact List.Sublist.trans this hst
    simp [this] at rih
    have := staticWeight_rank_ub s (node v l r) hst hbst
    linarith

private lemma staticWeight_φ_ub [LinearOrder α] (s t : Tree α)
    (hst : s.toKeyList = t.toKeyList) (hbst : s.IsBST) :
    φ (staticWeight s) t ≤ s.num_nodes^2 * Real.logb 2 3 := by
  calc φ (staticWeight s) t ≤ s.num_nodes * t.num_nodes * Real.logb 2 3 := by
        apply staticWeight_φ_ub_aux
        · rw [hst]
        · exact hbst
    _ ≤ s.num_nodes^2 * Real.logb 2 3 := by
      have : s.num_nodes = t.num_nodes := by
        simp [num_nodes_from_toKeyList, hst]
      rw [pow_two, this]

/-- This variant requires an extra assumption hsbst, even though that is implied by the other
assumptions -/
private lemma splay_tree_static_optimality' [LinearOrder α] (m : ℕ)
    (init s : Tree α) (hkeys : s.toKeyList = init.toKeyList)
    (hinitbst : init.IsBST) (hsbst : s.IsBST)
    (X : Fin m → α) (hX : ∀ i, X i ∈ init) :
    let n := s.num_nodes
    splay.sequence_cost init X ≤ m + (Real.logb 2 3) * (3 * staticCost s X + n ^ 2) := by
  by_cases hinit : init = nil
  · have : s = nil := by apply nil_of_toKeyList_empty; simp [hkeys, hinit]
    have hsnc : s.num_nodes = 0 := by simp [this]
    cases m with
    | zero => simp[hsnc, splay.sequence_cost]
    | succ m =>
      have : init ≠ nil := nonnil_of_mem (X (Fin.last m)) (hX (Fin.last m))
      contradiction
  · have hφ_ub: (∀ (t : Tree α), t.toKeyList = init.toKeyList
        → φ (staticWeight s) t ≤ ↑s.num_nodes ^ 2 * Real.logb 2 3) := by
      intro t h; apply staticWeight_φ_ub
      · simp [h, hkeys]
      · exact hsbst
    have hbound := splay_total_weighted_cost (staticWeight_ge_one s) m init hinitbst hφ_ub X hX
    have hsize_ub := staticWeight_size_ub s init (by simp [hkeys]) hsbst
    apply le_trans hbound
    simp only [staticCost, Nat.cast_sum]
    rw [mul_comm 3, Finset.sum_mul]
    have : (m : ℝ) = ∑ i : Fin m, 1 := by simp
    rw [this, mul_comm (Real.logb 2 3)]
    rw [add_mul, Finset.sum_mul, ←add_assoc, ←Finset.sum_add_distrib]
    simp only [add_comm]
    gcongr 3 with i
    calc 3 * Real.logb 2 (size (staticWeight s) init / staticWeight s (X i)) ≤
      3 * Real.logb 2 (3 ^ (s.num_nodes : ℝ) / staticWeight s (X i)) := by
          have hpos := staticWeight_pos s (X i)
          simp only [Real.rpow_natCast, Nat.ofNat_pos, mul_le_mul_iff_right₀, ge_iff_le]
          apply logb_mono
          · apply div_pos (size_pos_of_non_nil (staticWeight_pos s) init hinit) hpos
          · exact (div_le_div_iff_of_pos_right hpos).mpr hsize_ub
      _ = 3 * Real.logb 2 (3 ^ (s.search_path_len (X i) : ℝ)) := by
        simp only[staticWeight]; congr; field_simp
        rw [←Real.rpow_add (show 0 < 3 by simp)]
        congr; linarith
      _ ≤ (s.search_path_len (X i) * 3 * Real.logb 2 3 : ℝ) := by
        rw [mul_comm]
        rw [Real.logb_rpow_eq_mul_logb_of_pos (by simp)]
        linarith

/--
Splay performs as well as any static tree `s`, with any initial tree `init`, up to constant factors
and an O(n²) additive term.
Assumes that all queries are successful.
-/
theorem splay_tree_static_optimality [LinearOrder α] (m : ℕ)
    (init s : Tree α) (hkeys : s.toKeyList = init.toKeyList)
    (hinitbst : init.IsBST)
    (X : Fin m → α) (hX : ∀ i, X i ∈ init) :
    let n := s.num_nodes
    splay.sequence_cost init X ≤ m + (Real.logb 2 3) * (3 * staticCost s X + n ^ 2) := by
  have hsbst : s.IsBST := by exact IsBST_of_toKeyList_eq hkeys hinitbst
  exact splay_tree_static_optimality' m init s hkeys hinitbst hsbst X hX

end Weighted

end SplayTree
