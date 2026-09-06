/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.GraphCursor
import AlgoLib.Experimental.RAM.Prototype.Composition.Encoding
import AlgoLib.Experimental.RAM.Backend.Memory.GraphInput

/-!
# Owned immutable adjacency lists

The existing certified graph encoding supplies linked neighbor lists. This adapter
adds finite ownership to each read, so the generic frame theorem protects the graph
when a client writes its visited array or queue. Open and next execute loads from
RAM; they never evaluate the specification's neighbor function as a runtime callback.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.GraphCursorImplementation
open Checked.Language Experimental.RAM.BFS

def ChainIn (r : Footprint) (m : Nat → Nat) : Nat → List Nat → Prop
  | p, [] => p = 0
  | p, v :: vs => p ≠ 0 ∧ .heap (5 * p + 3) ∈ r ∧ .heap (5 * p + 4) ∈ r ∧
      m (5 * p + 3) = v ∧ ChainIn r m (m (5 * p + 4)) vs

theorem ChainIn.local {r : Footprint} {s t : Store} (agree : Agree r s t)
    (row : List Nat) (p : Nat) (h : ChainIn r s.heap p row) : ChainIn r t.heap p row := by
  induction row generalizing p with
  | nil => exact h
  | cons v vs ih =>
    refine ⟨h.1, h.2.1, h.2.2.1, (agree _ h.2.1).trans h.2.2.2.1, ?_⟩
    have next := agree _ h.2.2.1
    change t.heap (5 * p + 4) = s.heap (5 * p + 4) at next
    rw [next]
    exact ih _ h.2.2.2.2

def cells (a : Adjacency) : Footprint :=
  (Finset.range a.n).biUnion fun v => {.heap (5 * v)} ∪
    (Finset.range (a.neighbors v).length).biUnion fun i =>
      {.heap (5 * a.pointer v i + 3), .heap (5 * a.pointer v i + 4)}

def footprint (a : Adjacency) (cursor : Var .word) : Footprint :=
  cells a ∪ {.register .word cursor.name}

theorem cursor_owned (a : Adjacency) (cursor : Var .word) :
    Location.register .word cursor.name ∈ footprint a cursor := by simp [footprint]

theorem head_owned (a : Adjacency) (cursor : Var .word) (v : Nat) (hv : v < a.n) :
    Location.heap (5 * v) ∈ footprint a cursor := by
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  exact ⟨v, Finset.mem_range.mpr hv, Finset.mem_union_left _ (by simp)⟩

theorem node_owned (a : Adjacency) (cursor : Var .word) (v i : Nat)
    (hv : v < a.n) (hi : i < (a.neighbors v).length) :
    Location.heap (5 * a.pointer v i + 3) ∈ footprint a cursor ∧
      Location.heap (5 * a.pointer v i + 4) ∈ footprint a cursor := by
  constructor <;> apply Finset.mem_union_left <;> apply Finset.mem_biUnion.mpr
  · exact ⟨v, Finset.mem_range.mpr hv, Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, by simp⟩)⟩
  · exact ⟨v, Finset.mem_range.mpr hv, Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, by simp⟩)⟩

def Stored (a : Adjacency) (r : Footprint) (m : Nat → Nat) : Prop :=
  ∀ v < a.n, .heap (5 * v) ∈ r ∧ ChainIn r m (m (5 * v)) (a.neighbors v)

theorem Stored.local {a : Adjacency} {r : Footprint} {s t : Store}
    (agree : Agree r s t) (h : Stored a r s.heap) : Stored a r t.heap := by
  intro v hv
  have row := h v hv
  refine ⟨row.1, ?_⟩
  have head := agree _ row.1
  change t.heap (5 * v) = s.heap (5 * v) at head
  rw [head]
  exact ChainIn.local agree _ _ row.2

def representation (a : Adjacency) (cursor : Var .word) : Representation (List Nat) where
  holds row r s saved := r = footprint a cursor ∧ Stored a r s.heap ∧
    ChainIn r s.heap (s.vars .word cursor.name) row ∧ row.length ≤ a.entries ∧ saved = 0
  locality := by
    rintro row r s t saved agree ⟨rfl, stored, chain, bound, rfl⟩
    have read := agree _ (cursor_owned a cursor)
    change t.vars .word cursor.name = s.vars .word cursor.name at read
    refine ⟨rfl, Stored.local agree stored, ?_, bound, rfl⟩
    rw [read]
    exact ChainIn.local agree _ _ chain

theorem row_bound (a : Adjacency) (v : Nat) (valid : v < a.n) :
    (a.neighbors v).length ≤ a.entries :=
  Finset.single_le_sum (f := fun v => (a.neighbors v).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr valid)

def address (index : Expr .word) (offset : Nat) : Expr .ptr :=
  .bin .offset (.lit offset) (.bin .mul (.lit 5) index)

instance openImplementation (a : Adjacency) (cursor : Var .word) [q : ScalarStorage Q] :
    Primitive 24 ((representation a cursor).sep Q) (GraphCursor.openRow a)
      ((representation a cursor).sep Q) where
  code := .assign cursor (.load (address (.var q.register) 0))
  correct input pre r s saved rep := by
    obtain ⟨rp, rq, cp, cq, disjoint, rfl, rfl, hp, hq⟩ := rep
    obtain ⟨rfl, stored, old, bound, rfl⟩ := hp
    have read : (Expr.load (address (.var q.register) 0)).eval s = s.heap (5 * input.2) := by
      simp [address, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval, q.read _ _ _ _ hq]
    have exec := Eval.assign cursor (.load (address (.var q.register) 0)) s
    rw [read] at exec
    have changed := Writes.set s cursor (s.heap (5 * input.2)) (cursor_owned a cursor)
    refine ⟨7, _, cq, exec, ⟨footprint a cursor, rq, 0, cq, disjoint, rfl, by omega,
      ⟨rfl, stored, ?_, row_bound a input.2 pre, rfl⟩, Q.frame hq disjoint changed⟩,
      changed.mono Finset.subset_union_left, by simp [GraphCursor.openRow]⟩
    simpa [Store.set] using (stored input.2 pre).2

instance nextImplementation (a : Adjacency) (cursor : Var .word) [q : ScalarStorage Q] :
    Primitive 24 ((representation a cursor).sep Q) GraphCursor.next
      ((representation a cursor).sep Q) where
  code := .seq (.assign q.register (.load (address (.var cursor) 3)))
    (.assign cursor (.load (address (.var cursor) 4)))
  correct input pre r s saved rep := by
    obtain ⟨rp, rq, cp, cq, disjoint, rfl, rfl, hp, hq⟩ := rep
    obtain ⟨row, out⟩ := input
    cases row with
    | nil => exact (pre rfl).elim
    | cons v vs =>
      have old := hp.2.2.1
      have read : (Expr.load (address (.var cursor) 3)).eval s = v := by
        simpa [address, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval, Nat.add_comm]
          using old.2.2.2.1
      have first := Eval.assign q.register (.load (address (.var cursor) 3)) s
      rw [read] at first
      let t := s.set q.register v
      obtain ⟨hq', changed⟩ := q.update out rq s cq hq v
      have hp' := (representation a cursor).frame hp disjoint.symm changed
      have chain := hp'.2.2.1
      let next := t.heap (5 * t.vars .word cursor.name + 4)
      have readNext : (Expr.load (address (.var cursor) 4)).eval t = next := by
        simp [next, address, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval, Nat.add_comm]
      have second := Eval.assign cursor (.load (address (.var cursor) 4)) t
      rw [readNext] at second
      have advance : Writes rp t (t.set cursor next) :=
        Writes.set t cursor next (by rw [hp'.1]; exact cursor_owned a cursor)
      refine ⟨14, _, 0 + cq, .seq first second, ⟨rp, rq, 0, cq, disjoint, rfl, ?_,
        ⟨hp'.1, hp'.2.1, ?_, ?_, rfl⟩, Q.frame hq' disjoint advance⟩,
        (changed.mono Finset.subset_union_right).trans
          (advance.mono Finset.subset_union_left), ?_⟩
      · have := hp.2.2.2.2; omega
      · simpa only [GraphCursor.next, List.tail_cons, Store.set, if_pos (And.intro rfl rfl)]
          using (show ChainIn rp t.heap next vs from chain.2.2.2.2)
      · have := hp'.2.2.2.1
        simp only [GraphCursor.next, List.tail_cons, List.length_cons] at *
        omega
      · have := hp.2.2.2.2; simp [GraphCursor.next]; omega

instance nonemptyImplementation (a : Adjacency) (cursor : Var .word) :
    TestImplementation 24 (representation a cursor) GraphCursor.nonempty where
  condition := ⟨.word, .lt, .lit 0, .var cursor⟩
  correct row r s saved rep := by
    have chain := rep.2.2.1
    cases row with
    | nil => simp [Condition.eval, Expr.eval, Comparison.eval, GraphCursor.nonempty,
        show s.vars .word cursor.name = 0 from chain]
    | cons v vs => simp [Condition.eval, Expr.eval, Comparison.eval, GraphCursor.nonempty,
        Nat.pos_of_ne_zero chain.1]
  cost := by simp [Condition.cost, Expr.cost]

def decodeChain : Nat → (Nat → Nat) → Nat → List Nat
  | 0, _, _ => []
  | n + 1, m, p => if p = 0 then [] else m (5 * p + 3) :: decodeChain n m (m (5 * p + 4))

theorem decodeChain_correct (row : List Nat) (r : Footprint) (m : Nat → Nat) (p fuel : Nat)
    (h : ChainIn r m p row) (bound : row.length ≤ fuel) : decodeChain fuel m p = row := by
  induction row generalizing p fuel with
  | nil => cases fuel <;> simp [decodeChain, show p = 0 from h]
  | cons v vs ih =>
    cases fuel with
    | zero => simp at bound
    | succ fuel =>
      simp only [decodeChain, if_neg h.1, h.2.2.2.1]
      congr 1
      exact ih _ _ h.2.2.2.2 (by simp at bound; omega)

instance decoder (a : Adjacency) (cursor : Var .word) : Decoder (representation a cursor) where
  decode s := decodeChain a.entries s.heap (s.vars .word cursor.name)
  correct row r s _ h := decodeChain_correct row r s.heap _ _ h.2.2.1 h.2.2.2.1

/-- Upgrade the existing adjacency encoding to a finite ownership certificate. -/
theorem encoded_chain (a : Adjacency) (cursor : Var .word) (v : Nat) (hv : v < a.n) (i : Nat) :
    ChainIn (footprint a cursor) a.encode (a.pointer v i) ((a.neighbors v).drop i) := by
  generalize hn : (a.neighbors v).length - i = n
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih =>
    by_cases hi : i < (a.neighbors v).length
    · have chain := a.encode_chain v i
      rw [List.drop_eq_getElem_cons hi] at chain ⊢
      have owned := node_owned a cursor v i hv hi
      refine ⟨chain.1, owned.1, owned.2, chain.2.1, ?_⟩
      have next : a.encode (5 * a.pointer v i + 4) = a.pointer v (i + 1) := by
        simp [Adjacency.encode, Adjacency.pointer, hi, Nat.add_div, Nat.mul_comm]
      rw [next]
      exact ih _ (by omega) (i + 1) rfl
    · have empty : (a.neighbors v).drop i = [] := List.drop_eq_nil_of_le (by omega)
      simp [empty, ChainIn, Adjacency.pointer, hi]

/-- Graph materialization is input encoding; the mutable cursor starts empty. -/
def encoder (a : Adjacency) (cursor : Var .word) : Encoder (representation a cursor) where
  footprint := footprint a cursor
  requires row := row = []
  saved _ := 0
  store _ := { vars := fun _ _ => 0, heap := a.encode }
  correct row empty := by
    subst row
    refine ⟨rfl, ?_, rfl, by simp, rfl⟩
    intro v hv
    refine ⟨head_owned a cursor v hv, ?_⟩
    change ChainIn _ a.encode (a.encode (5 * v)) (a.neighbors v)
    rw [encode_head]
    simpa using encoded_chain a cursor v hv 0

/-- The resident graph arena ends before separately allocated mutable arrays. -/
def extent (a : Adjacency) : Nat := (cells a).sup fun
  | .heap address => address + 1
  | .register _ _ => 0

theorem below_extent (a : Adjacency) (address : Nat) (h : Location.heap address ∈ cells a) :
    address < extent a := by
  have bound := Finset.le_sup (f := fun
    | Location.heap address => address + 1
    | .register _ _ => 0) h
  exact bound

theorem no_register (a : Adjacency) (ty : Ty) (name : String) :
    Location.register ty name ∉ cells a := by simp [cells]

end AlgoLib.Experimental.RAM.Prototype.Composition.GraphCursorImplementation
