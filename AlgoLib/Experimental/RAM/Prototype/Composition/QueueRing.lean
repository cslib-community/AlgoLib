/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Queue
import AlgoLib.Experimental.RAM.Prototype.Composition.Encoding

/-!
# Circular-buffer FIFO representation

Head and length are private registers; capacity cells are reserved once. Indices
wrap with a comparison and subtraction, so no division instruction is assumed.
Inactive cells are unrestricted. The model is the FIFO list, with zero private
potential. Calls borrow a scalar and preserve every other owned resource.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.QueueRing
open Checked.Language

structure Layout where
  name : String
  base : Nat
  capacity : Nat

def Layout.head (l : Layout) : Var .word := ⟨l.name ++ ".head"⟩
def Layout.length (l : Layout) : Var .word := ⟨l.name ++ ".length"⟩
def Layout.footprint (l : Layout) : Footprint :=
  {.register .word l.head.name, .register .word l.length.name} ∪
    (Finset.range l.capacity).image (fun i => Location.heap (l.base + i))

def index (capacity head i : Nat) : Nat :=
  if head + i < capacity then head + i else head + i - capacity

theorem index_lt (hc : head < capacity) (hi : i < capacity) :
    index capacity head i < capacity := by unfold index; split_ifs <;> omega

theorem index_injective (_hc : head < capacity) (hi : i < capacity) (hj : j < capacity) :
    index capacity head i = index capacity head j ↔ i = j := by
  unfold index; split_ifs <;> omega

def advance (capacity head : Nat) := if head + 1 < capacity then head + 1 else 0

theorem advance_lt (hc : head < capacity) : advance capacity head < capacity := by
  unfold advance; split_ifs <;> omega

theorem index_advance (hc : head < capacity) (hi : i + 1 < capacity) :
    index capacity (advance capacity head) i = index capacity head (i + 1) := by
  unfold index advance; split_ifs <;> omega

theorem head_owned (l : Layout) : Location.register .word l.head.name ∈ l.footprint := by
  simp [Layout.footprint]
theorem length_owned (l : Layout) : Location.register .word l.length.name ∈ l.footprint := by
  simp [Layout.footprint]
theorem cell_owned (l : Layout) (hi : i < l.capacity) :
    Location.heap (l.base + i) ∈ l.footprint := by
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)

@[simp] theorem names_differ (l : Layout) : l.head.name ≠ l.length.name := by
  simp [Layout.head, Layout.length]

def Valid (l : Layout) (xs : List Nat) (s : Store) : Prop :=
  xs.length ≤ l.capacity ∧ s.vars .word l.head.name < max 1 l.capacity ∧
  s.vars .word l.length.name = xs.length ∧
  ∀ i, i < xs.length → s.heap (l.base + index l.capacity (s.vars .word l.head.name) i) = xs[i]!

def representation (l : Layout) : Representation (List Nat) where
  holds xs r s saved := r = l.footprint ∧ Valid l xs s ∧ saved = 0
  locality := by
    rintro xs r s t saved agree ⟨rfl, valid, rfl⟩
    obtain ⟨bound, head, len, cells⟩ := valid
    have hh := agree _ (head_owned l)
    have hl := agree _ (length_owned l)
    change t.vars .word l.head.name = s.vars .word l.head.name at hh
    change t.vars .word l.length.name = s.vars .word l.length.name at hl
    refine ⟨rfl, ⟨bound, by omega, hl.trans len, ?_⟩, rfl⟩
    intro i hi
    rw [hh]
    have hc : s.vars .word l.head.name < l.capacity := by omega
    exact (agree _ (cell_owned l (index_lt hc (hi.trans_le bound)))).trans (cells i hi)

theorem push_valid (l : Layout) (xs : List Nat) (x : Nat) (s : Store)
    (h : Valid l xs s) (space : xs.length < l.capacity) :
    Valid l (xs ++ [x])
      ((s.write (l.base + index l.capacity (s.vars .word l.head.name) xs.length) x).set
        l.length (xs.length + 1)) := by
  have hc : s.vars .word l.head.name < l.capacity := by have := h.2.1; omega
  refine ⟨by simp; omega, ?_, ?_, ?_⟩
  · simpa [Store.set, Store.write] using h.2.1
  · simp [Store.set]
  · intro i hi
    by_cases old : i < xs.length
    · have ni : l.base + index l.capacity (s.vars .word l.head.name) i ≠
          l.base + index l.capacity (s.vars .word l.head.name) xs.length := by
        have := index_injective hc (old.trans space) space
        omega
      have ni' : index l.capacity (s.vars .word l.head.name) i ≠
          index l.capacity (s.vars .word l.head.name) xs.length := by omega
      simpa [Store.set, Store.write, Function.update_apply, ni, Ne.symm ni, ni',
        List.getElem?_append, old] using h.2.2.2 i old
    · have eq : i = xs.length := by simp at hi; omega
      subst i
      simp [Store.set, Store.write]

theorem pop_valid (l : Layout) (x : Nat) (xs : List Nat) (s : Store)
    (h : Valid l (x :: xs) s) :
    Valid l xs ((s.set l.head (advance l.capacity (s.vars .word l.head.name))).set
      l.length xs.length) := by
  have hc : s.vars .word l.head.name < l.capacity := by
    have := h.1; have := h.2.1; simp at *; omega
  refine ⟨by have := h.1; simp at *; omega, ?_, by simp [Store.set], ?_⟩
  · simpa [Store.set] using (advance_lt hc).trans_le (Nat.le_max_right 1 l.capacity)
  · intro i hi
    have hb : i + 1 < l.capacity := by have := h.1; simp at *; omega
    simpa [Store.set, index_advance hc hb] using h.2.2.2 (i + 1) (by simp; omega)

def increment (v : Var .word) : Expr .word := .bin .add (.var v) (.lit 1)
def decrement (v : Var .word) : Expr .word := .bin .sub (.var v) (.lit 1)
def sum (l : Layout) : Expr .word := .bin .add (.var l.head) (.var l.length)
def direct (l : Layout) : Expr .ptr := .bin .offset (.lit l.base) (sum l)
def wrapped (l : Layout) : Expr .ptr :=
  .bin .offset (.lit l.base) (.bin .sub (sum l) (.lit l.capacity))
def wraps (l : Layout) : Condition := ⟨.word, .lt, sum l, .lit l.capacity⟩

def writeTail (l : Layout) (v : Var .word) : Cmd :=
  .branch (wraps l) (.write (direct l) (.var v)) (.write (wrapped l) (.var v))

theorem writeTail_correct (l : Layout) (v : Var .word) (s : Store) :
    ∃ k, k ≤ 14 ∧ Eval (writeTail l v) s k
      (s.write (l.base + index l.capacity (s.vars .word l.head.name)
        (s.vars .word l.length.name)) (s.vars .word v.name)) := by
  by_cases h : s.vars .word l.head.name + s.vars .word l.length.name < l.capacity
  · refine ⟨12, by omega, ?_⟩
    have step := Eval.ifTrue (b := .write (wrapped l) (.var v))
      (q := wraps l) (by simpa [wraps, Condition.eval, sum, Expr.eval, Op.eval,
        Op.machine, Checked.BinOp.eval, Comparison.eval] using h)
      (Eval.write (direct l) (.var v) s)
    simpa [writeTail, direct, sum, wraps, Condition.cost, Expr.cost, Expr.eval, Op.eval,
      Op.machine, Checked.BinOp.eval, index, h] using step
  · refine ⟨14, by omega, ?_⟩
    have step := Eval.ifFalse (a := .write (direct l) (.var v))
      (q := wraps l) (by simpa [wraps, Condition.eval, sum, Expr.eval, Op.eval,
        Op.machine, Checked.BinOp.eval, Comparison.eval] using h)
      (Eval.write (wrapped l) (.var v) s)
    simpa [writeTail, wrapped, sum, wraps, Condition.cost, Expr.cost, Expr.eval, Op.eval,
      Op.machine, Checked.BinOp.eval, index, h] using step

instance pushImplementation (name : String) (base capacity : Nat) [q : ScalarStorage Q] :
    Primitive 24 ((representation ⟨name, base, capacity⟩).sep Q) (Queue.push capacity)
      ((representation ⟨name, base, capacity⟩).sep Q) where
  code := .seq (writeTail ⟨name, base, capacity⟩ q.register)
    (.assign (Layout.length ⟨name, base, capacity⟩)
      (increment (Layout.length ⟨name, base, capacity⟩)))
  correct input pre r s saved rep := by
    let l : Layout := ⟨name, base, capacity⟩
    obtain ⟨rp, rq, cp, cq, disjoint, rfl, rfl, hp, hq⟩ := rep
    obtain ⟨rfl, valid, rfl⟩ := hp
    have len : s.vars .word l.length.name = input.1.length := valid.2.2.1
    have value := q.read input.2 rq s cq hq
    obtain ⟨k, bound, first⟩ := writeTail_correct l q.register s
    rw [len, value] at first
    let addr := l.base + index l.capacity (s.vars .word l.head.name) input.1.length
    let t := s.write addr input.2
    have second : Eval (.assign l.length (increment l.length)) t 4
        (t.set l.length (input.1.length + 1)) := by
      simpa [increment, Expr.cost, Expr.eval, Op.eval, Op.machine,
        Checked.BinOp.eval, t, Store.write,
        len] using Eval.assign l.length (increment l.length) t
    have hc : s.vars .word l.head.name < l.capacity := by
      have := valid.2.1; change input.1.length < capacity at pre; dsimp [l] at *; omega
    have owned : Location.heap addr ∈ l.footprint := cell_owned l (index_lt hc pre)
    have changed := (Writes.write s addr input.2 owned).trans
      (Writes.set t l.length (input.1.length + 1) (length_owned l))
    refine ⟨k + 4, _, cq, .seq first second,
      ⟨l.footprint, rq, 0, cq, disjoint, rfl, by omega,
        ⟨rfl, push_valid l input.1 input.2 s valid pre, rfl⟩,
        Q.frame hq disjoint changed⟩,
      changed.mono Finset.subset_union_left, ?_⟩
    simp [Queue.push]; omega

def advanceHead (l : Layout) : Cmd :=
  .branch ⟨.word, .lt, increment l.head, .lit l.capacity⟩
    (.assign l.head (increment l.head)) (.assign l.head (.lit 0))

theorem advanceHead_correct (l : Layout) (s : Store) :
    ∃ k, k ≤ 9 ∧ Eval (advanceHead l) s k
      (s.set l.head (advance l.capacity (s.vars .word l.head.name))) := by
  by_cases h : s.vars .word l.head.name + 1 < l.capacity
  · refine ⟨9, by omega, ?_⟩
    have step := Eval.ifTrue (b := .assign l.head (.lit 0))
      (q := ⟨.word, .lt, increment l.head, .lit l.capacity⟩)
      (by simpa [Condition.eval, increment, Expr.eval, Op.eval, Op.machine,
        Checked.BinOp.eval, Comparison.eval] using h)
      (Eval.assign l.head (increment l.head) s)
    simpa [advanceHead, increment, Condition.cost, Expr.cost, Expr.eval, Op.eval,
      Op.machine, Checked.BinOp.eval, advance, h] using step
  · refine ⟨7, by omega, ?_⟩
    have step := Eval.ifFalse (a := .assign l.head (increment l.head))
      (q := ⟨.word, .lt, increment l.head, .lit l.capacity⟩)
      (by simpa [Condition.eval, increment, Expr.eval, Op.eval, Op.machine,
        Checked.BinOp.eval, Comparison.eval] using h)
      (Eval.assign l.head (.lit 0) s)
    simpa [advanceHead, increment, Condition.cost, Expr.cost, Expr.eval, advance, h] using step

def headAddress (l : Layout) : Expr .ptr := .bin .offset (.lit l.base) (.var l.head)

instance popImplementation (l : Layout) [q : ScalarStorage Q] :
    Primitive 24 ((representation l).sep Q) Queue.pop ((representation l).sep Q) where
  code := .seq (.assign q.register (.load (headAddress l)))
    (.seq (advanceHead l) (.assign l.length (decrement l.length)))
  correct input pre r s saved rep := by
    obtain ⟨rp, rq, cp, cq, disjoint, rfl, rfl, hp, hq⟩ := rep
    obtain ⟨rfl, valid, rfl⟩ := hp
    obtain ⟨xs, out⟩ := input
    cases xs with
    | nil => exact (pre rfl).elim
    | cons x xs =>
      have hc : s.vars .word l.head.name < l.capacity := by
        have := valid.1; have := valid.2.1; simp at *; omega
      have read : (Expr.load (headAddress l)).eval s = x := by
        have atHead := valid.2.2.2 0 (by simp)
        simpa [headAddress, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval, index, hc]
          using atHead
      have first := Eval.assign q.register (.load (headAddress l)) s
      rw [read] at first
      let t := s.set q.register x
      obtain ⟨hq', otherWrites⟩ := q.update out rq s cq hq x
      have hp' := (representation l).frame
        (show (representation l).holds (x :: xs) l.footprint s 0 from ⟨rfl, valid, rfl⟩)
        disjoint.symm otherWrites
      have valid' := hp'.2.1
      obtain ⟨k, bound, second⟩ := advanceHead_correct l t
      let u := t.set l.head (advance l.capacity (t.vars .word l.head.name))
      have len' : t.vars .word l.length.name = (x :: xs).length := valid'.2.2.1
      have third : Eval (.assign l.length (decrement l.length)) u 4
          (u.set l.length xs.length) := by
        simpa [decrement, Expr.cost, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval, u,
          Store.set, Ne.symm (names_differ l), len'] using
          Eval.assign l.length (decrement l.length) u
      have changed := (Writes.set t l.head _ (head_owned l)).trans
        (Writes.set u l.length xs.length (length_owned l))
      refine ⟨5 + (k + 4), _, cq, .seq first (.seq second third),
        ⟨l.footprint, rq, 0, cq, disjoint, rfl, by omega,
          ⟨rfl, pop_valid l x xs t valid', rfl⟩, Q.frame hq' disjoint changed⟩,
        (otherWrites.mono Finset.subset_union_right).trans
          (changed.mono Finset.subset_union_left), ?_⟩
      simp [Queue.pop]; omega

instance resetImplementation (l : Layout) :
    Primitive 24 (representation l) Queue.reset (representation l) where
  code := .seq (.assign l.head (.lit 0)) (.assign l.length (.lit 0))
  correct xs pre r s saved rep := by
    obtain ⟨rfl, valid, rfl⟩ := rep
    refine ⟨4, _, 0, .seq (.assign _ _ _) (.assign _ _ _),
      ⟨rfl, ?_, rfl⟩,
      (Writes.set s l.head 0 (head_owned l)).trans
        (Writes.set _ l.length 0 (length_owned l)), by simp [Queue.reset]⟩
    simp [Valid, Queue.reset, Store.set, Expr.eval]

instance nonemptyImplementation (l : Layout) :
    TestImplementation 24 (representation l) Queue.nonempty where
  condition := ⟨.word, .lt, .lit 0, .var l.length⟩
  correct xs r s saved h := by
    cases xs <;> simp [Condition.eval, Expr.eval, Comparison.eval, h.2.1.2.2.1, Queue.nonempty]
  cost := by simp [Condition.cost, Expr.cost]

def encoder (l : Layout) : Encoder (representation l) where
  footprint := l.footprint
  requires xs := xs.length ≤ l.capacity
  saved _ := 0
  store xs :=
    { vars := fun _ name => if name = l.head.name then 0 else xs.length
      heap := fun i => xs[i - l.base]! }
  correct xs bound := by
    refine ⟨rfl, ⟨bound, by simp, by simp [Ne.symm (names_differ l)], ?_⟩, rfl⟩
    intro i hi
    simp [index, hi.trans_le bound]

instance decoder (l : Layout) : Decoder (representation l) where
  decode s := (List.range (s.vars .word l.length.name)).map
    (fun i => s.heap (l.base + index l.capacity (s.vars .word l.head.name) i))
  correct xs r s saved h := by
    rw [h.2.1.2.2.1]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simpa [getElem!_pos xs i hj] using h.2.1.2.2.2 i hj

end AlgoLib.Experimental.RAM.Prototype.Composition.QueueRing
