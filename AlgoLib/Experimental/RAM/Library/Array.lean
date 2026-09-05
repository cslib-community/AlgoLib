/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Language.Verification
import AlgoLib.Experimental.RAM.Library.Framing

/-! # Contiguous arrays: representation, functional contracts, costs, and frames -/
namespace AlgoLib.Experimental.RAM.Checked.Language

@[simp] theorem Store.set_vars {ty : Ty} (s : Store) (v : Var ty) (n : Nat)
    (t : Ty) (name : String) :
    (s.set v n).vars t name = if t = ty ∧ name = v.name then n else s.vars t name := rfl
@[simp] theorem Store.set_heap {ty : Ty} (s : Store) (v : Var ty) (n : Nat) :
    (s.set v n).heap = s.heap := rfl
@[simp] theorem Store.write_vars (s : Store) (a v : Nat) :
    (s.write a v).vars = s.vars := rfl
@[simp] theorem Store.write_heap (s : Store) (a v : Nat) :
    (s.write a v).heap = Function.update s.heap a v := rfl

@[simp] theorem Store.set_restore {ty : Ty} (s : Store) (v : Var ty) (n : Nat) :
    (s.set v n).set v (s.vars ty v.name) = s := by
  cases s
  unfold Store.set
  congr 1
  funext t name
  split <;> simp_all

theorem Store.set_comm {a b : Ty} (s : Store) (v : Var a) (w : Var b) (x y : Nat)
    (hne : v.name ≠ w.name) : (s.set v x).set w y = (s.set w y).set v x := by
  unfold Store.set
  congr 1
  funext t name
  by_cases hv : t = a ∧ name = v.name <;>
    by_cases hw : t = b ∧ name = w.name
  · exact False.elim (hne (hv.2.symm.trans hw.2))
  all_goals simp [hv, hw, hne, Ne.symm hne]

/-- A logical segment. The list is ghost data, not a runtime list oracle. -/
def Segment (s : Store) (base : Nat) (xs : List Nat) : Prop :=
  ∀ i (h : i < xs.length), s.heap (base + i) = xs[i]

theorem Segment.nil (s : Store) (base : Nat) : Segment s base [] := by
  intro i hi; simp at hi

theorem Segment.heap_eq {s t : Store} {base : Nat} {xs : List Nat}
    (h : Segment s base xs) (he : t.heap = s.heap) : Segment t base xs := by
  intro i hi; rw [he]; exact h i hi

theorem Segment.append {s : Store} {base : Nat} {xs : List Nat} (h : Segment s base xs)
    (v : Nat) : Segment (s.write (base + xs.length) v) base (xs ++ [v]) := by
  intro i hi
  by_cases hx : i < xs.length
  · have hn : base + i ≠ base + xs.length := by omega
    simpa [Store.write, Function.update_apply, hn, Nat.ne_of_lt hx,
      List.getElem_append, hx] using h i hx
  · have he : i = xs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simp [Store.write, List.getElem_append_right]

theorem Segment.tail {s : Store} {base v : Nat} {xs : List Nat}
    (h : Segment s base (v :: xs)) : Segment s (base + 1) xs := by
  intro i hi
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (i + 1) (by simp; omega)

theorem Segment.head {s : Store} {base v : Nat} {xs : List Nat}
    (h : Segment s base (v :: xs)) : s.heap base = v := by
  simpa using h 0 (by simp)

theorem Segment.prefix {s : Store} {base v : Nat} {xs : List Nat}
    (h : Segment s base (xs ++ [v])) : Segment s base xs := by
  intro i hi
  exact (h i (by simp; omega)).trans (List.getElem_append_left hi)

theorem Segment.last {s : Store} {base v : Nat} {xs : List Nat}
    (h : Segment s base (xs ++ [v])) : s.heap (base + xs.length) = v := by
  simpa using h xs.length (by simp)

/-- Runtime array base; length/ownership are explicit logical preconditions.
The base is a variable, so the same compiled code handles every input address. -/
structure ArrayRef where
  base : Var .ptr

def ArrayRef.address (a : ArrayRef) (i : Expr .word) : Expr .ptr := .bin .offset (.var a.base) i
def ArrayRef.cell (a : ArrayRef) (i : Expr .word) : Expr .word := .load (a.address i)
def ArrayRef.get (a : ArrayRef) (i : Expr .word) (out : Var .word) : Cmd := .assign out (a.cell i)
def ArrayRef.put (a : ArrayRef) (i value : Expr .word) : Cmd := .write (a.address i) value

def ArrayRef.Rep (a : ArrayRef) (s : Store) (xs : List Nat) : Prop :=
  Segment s (s.vars .ptr a.base.name) xs

/-- Bounds are checked in the proof; reads preserve the entire heap. -/
theorem ArrayRef.get_spec (a : ArrayRef) (i : Expr .word) (out : Var .word)
    (xs : List Nat) : Contract (a.get i out)
      (fun s => a.Rep s xs ∧ i.eval s < xs.length)
      (fun s t => t = s.set out (xs[i.eval s]?.getD 0))
      (fun _ => i.cost + 4) := by
  intro s hs
  refine ⟨_, _, .assign _ _ _, ?_, by simp [ArrayRef.cell, ArrayRef.address, Expr.cost]; omega⟩
  congr 1
  simpa [ArrayRef.cell, ArrayRef.address, Expr.eval, Op.eval, Op.machine, BinOp.eval,
    List.getElem?_eq_getElem hs.2] using hs.1 _ hs.2

/-- The exact state equation is a frame contract too: one cell changes, all
variables and every other heap address remain unchanged. -/
theorem ArrayRef.put_spec (a : ArrayRef) (i value : Expr .word) :
    Contract (a.put i value) (fun _ => True)
      (fun s t => t = s.write (s.vars .ptr a.base.name + i.eval s) (value.eval s))
      (fun _ => i.cost + value.cost + 3) := by
  intro s _
  exact ⟨_, _, .write _ _ _, rfl, by simp [ArrayRef.address, Expr.cost]; omega⟩

/-- A write refines the mathematical array update, with no out-of-bounds claim. -/
theorem ArrayRef.put_rep (a : ArrayRef) (s : Store) (xs : List Nat)
    (h : a.Rep s xs) (i : Nat) (_hi : i < xs.length) (v : Nat) :
    a.Rep (s.write (s.vars .ptr a.base.name + i) v) (xs.set i v) := by
  intro j hj
  have hj' : j < xs.length := by simpa using hj
  by_cases he : j = i
  · subst j; simp [Store.write]
  · have hn : s.vars .ptr a.base.name + j ≠ s.vars .ptr a.base.name + i := by omega
    simpa [Store.write, Function.update_apply, hn, List.getElem_set, he, Ne.symm he] using h j hj'

/-- The safe public write contract combines bounds, mathematical update, and frame. -/
theorem ArrayRef.set_spec (a : ArrayRef) (xs : List Nat) (i value : Expr .word) :
    Contract (a.put i value) (fun s => a.Rep s xs ∧ i.eval s < xs.length)
      (fun s t => a.Rep t (xs.set (i.eval s) (value.eval s)) ∧
        t = s.write (s.vars .ptr a.base.name + i.eval s) (value.eval s))
      (fun _ => i.cost + value.cost + 3) := by
  intro s hs
  obtain ⟨k, t, hx, ht, hk⟩ := a.put_spec i value s trivial
  subst t
  exact ⟨k, _, hx, ⟨a.put_rep s xs hs.1 _ hs.2 _, rfl⟩, hk⟩

/-- A segment representation reads only its owned interval. Registered once
by the library; clients do not unfold element/address equations to frame it. -/
theorem Segment.reads (base : Nat) (xs : List Nat) :
    Framing.ReadsOnly (Set.Ico base (base + xs.length))
      (fun m => ∀ i (h : i < xs.length), m (base + i) = xs[i]) := by
  intro m n he h i hi
  exact (he _ ⟨by omega, by omega⟩).trans (h i hi)

/-- All segment frames follow from the same footprint rule as graph frames. -/
theorem Segment.frame_write {s : Store} {base address value : Nat} {xs : List Nat}
    (h : Segment s base xs) (outside : address < base ∨ base + xs.length ≤ address) :
    Segment (s.write address value) base xs := by
  exact Framing.frame_write (Segment.reads base xs)
    (by simp only [Set.mem_Ico]; omega) h

end AlgoLib.Experimental.RAM.Checked.Language
