/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Buffer
import AlgoLib.Experimental.RAM.Prototype.Composition.Linking

/-!
# Two bounded-buffer implementations with different private payment strategies

Lazy clear only resets the length; inactive payloads may retain old values. Eager
clear overwrites every occupied cell, maintaining a zero inactive suffix. Eager
append stores twelve units of potential per element to pay the future erase loop.
Both implement exactly Buffer.argument, Buffer.append and Buffer.clear.

Registers and the entire bounded allocation are owned. Distinct buffer layouts can
be composed using the generic separating product. No algorithm-specific refinement
is supplied. The ABI consists of two named word registers plus resident buffer cells.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.BufferImplementation
open Checked.Language

structure Layout where
  name : String
  base : Nat
  capacity : Nat

def Layout.lengthVar (l : Layout) : Var .word := ⟨l.name ++ ".length"⟩
def Layout.argumentVar (l : Layout) : Var .word := ⟨l.name ++ ".argument"⟩
def Layout.footprint (l : Layout) : Footprint :=
  { .register .word l.lengthVar.name, .register .word l.argumentVar.name } ∪
    (Finset.range l.capacity).image (fun i => Location.heap (l.base + i))

theorem length_owned (l : Layout) : Location.register .word l.lengthVar.name ∈ l.footprint := by
  simp [Layout.footprint]
theorem argument_owned (l : Layout) : Location.register .word l.argumentVar.name ∈ l.footprint := by
  simp [Layout.footprint]
theorem cell_owned (l : Layout) (hi : i < l.capacity) :
    Location.heap (l.base + i) ∈ l.footprint := by
  simp only [Layout.footprint, Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)

/-- The zero suffix and saved potential are implementation-private. -/
def Valid (l : Layout) (eager : Bool) (xs : List Nat) (s : Store) : Prop :=
  xs.length ≤ l.capacity ∧ s.vars .word l.lengthVar.name = xs.length ∧
  (∀ i, i < xs.length → s.heap (l.base + i) = xs[i]!) ∧
  (eager = true → ∀ i, xs.length ≤ i → i < l.capacity → s.heap (l.base + i) = 0)

def potential (eager : Bool) (n : Nat) : Nat := if eager then 12 * n else 0

def representation (l : Layout) (eager : Bool) : Representation (List Nat) where
  holds xs r s saved := r = l.footprint ∧ Valid l eager xs s ∧ saved = potential eager xs.length
  locality := by
    rintro xs r s t saved h ⟨rfl, hv, hp⟩
    refine ⟨rfl, ⟨hv.1, ?_, ?_, ?_⟩, hp⟩
    · exact (h _ (length_owned l)).trans hv.2.1
    · intro i hi
      exact (h _ (cell_owned l (hi.trans_le hv.1))).trans (hv.2.2.1 i hi)
    · intro he i hi hb
      exact (h _ (cell_owned l hb)).trans (hv.2.2.2 he i hi hb)

/-- A typed argument occupies a reserved register in the buffer's own footprint. -/
def inputRepresentation (l : Layout) (eager : Bool) : Representation (List Nat × Nat) where
  holds input r s saved := (representation l eager).holds input.1 r s saved ∧
    s.vars .word l.argumentVar.name = input.2
  locality := by
    intro input r s t saved h hp
    refine ⟨(representation l eager).locality h hp.1, ?_⟩
    exact (h (.register .word l.argumentVar.name) (hp.1.1.symm ▸ argument_owned l)).trans hp.2

def address (l : Layout) : Expr .ptr := .bin .offset (.lit l.base) (.var l.lengthVar)
def increase (l : Layout) : Expr .word := .bin .add (.var l.lengthVar) (.lit 1)
def decrease (l : Layout) : Expr .word := .bin .sub (.var l.lengthVar) (.lit 1)
def nonempty (l : Layout) : Condition := ⟨.word, .lt, .lit 0, .var l.lengthVar⟩

theorem names_differ (l : Layout) : l.lengthVar.name ≠ l.argumentVar.name := by
  simp [Layout.lengthVar, Layout.argumentVar]

instance argumentImplementation (l : Layout) (eager : Bool) (value : Nat) :
    Primitive 24 (representation l eager) (Buffer.argument value)
      (inputRepresentation l eager) where
  code := .assign l.argumentVar (.lit value)
  correct xs _ r s saved rep := by
    obtain ⟨rfl, hv, rfl⟩ := rep
    refine ⟨2, _, potential eager xs.length, .assign _ _ _, ?_,
      Writes.set s _ value (argument_owned l), by simp [Buffer.argument]⟩
    refine ⟨⟨rfl, ?_, rfl⟩, ?_⟩
    · simpa [Valid, Store.set, names_differ l, Expr.eval] using hv
    · simp [Store.set, Expr.eval, Buffer.argument]

/-- Appending writes one payload and advances the length. -/
def appendCode (l : Layout) : Cmd :=
  .seq (.write (address l) (.var l.argumentVar)) (.assign l.lengthVar (increase l))

theorem append_valid (l : Layout) (eager : Bool) (xs : List Nat) (s : Store)
    (hv : Valid l eager xs s) (space : xs.length < l.capacity) (value : Nat) :
    Valid l eager (xs ++ [value])
      ((s.write (l.base + xs.length) value).set l.lengthVar (xs.length + 1)) := by
  refine ⟨by simp; omega, ?_, ?_, ?_⟩
  · simp [Store.set]
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases old : i < xs.length
    · have ne : l.base + i ≠ l.base + xs.length := by omega
      have ni : i ≠ xs.length := by omega
      simpa [Store.set, Store.write, Function.update_apply, ne, Ne.symm ne, ni,
        List.getElem?_append, old] using hv.2.2.1 i old
    · have equal : i = xs.length := by omega
      subst i
      simp [Store.set, Store.write]
  · intro he i hi hb
    simp only [List.length_append, List.length_singleton] at hi
    have ne : l.base + i ≠ l.base + xs.length := by omega
    have ni : i ≠ xs.length := by omega
    simpa [Store.set, Store.write, Function.update_apply, ne, Ne.symm ne, ni] using
      hv.2.2.2 he i (by omega) hb

@[reducible] def appendImplementation (l : Layout) (eager : Bool) :
    Primitive 24 (inputRepresentation l eager) (Buffer.append l.capacity)
      (representation l eager) where
  code := appendCode l
  correct input space r s saved rep := by
    obtain ⟨⟨rfl, hv, rfl⟩, ha⟩ := rep
    have addr : (address l).eval s = l.base + input.1.length := by
      simp [address, Expr.eval, Op.eval, Op.machine, Checked.BinOp.eval, hv.2.1]
    have val : (Expr.var l.argumentVar).eval s = input.2 := ha
    have inc : (increase l).eval (s.write (l.base + input.1.length) input.2) =
        input.1.length + 1 := by
      simp [increase, Expr.eval, Store.write, Op.eval, Op.machine, Checked.BinOp.eval, hv.2.1]
    have exe := Eval.seq (Eval.write (address l) (.var l.argumentVar) s)
      (Eval.assign l.lengthVar (increase l) _)
    rw [addr, val, inc] at exe
    refine ⟨9, _, potential eager (input.1.length + 1), exe, ?_, ?_, ?_⟩
    · exact ⟨rfl, append_valid l eager input.1 s hv space input.2, by simp [Buffer.append]⟩
    · exact (Writes.write _ _ _ (cell_owned l space)).trans
        (Writes.set _ _ _ (length_owned l))
    · cases eager <;> simp [potential, Buffer.append]
      omega

/-- Expose the public capacity directly for type-directed operation lookup. -/
instance appendRegistered (name : String) (base capacity : Nat) (eager : Bool) :
    Primitive 24 (inputRepresentation ⟨name, base, capacity⟩ eager) (Buffer.append capacity)
      (representation ⟨name, base, capacity⟩ eager) :=
  appendImplementation ⟨name, base, capacity⟩ eager

/-- The private expensive operation: decrement, erase the last payload, repeat. -/
def eraseBody (l : Layout) : Cmd :=
  .seq (.assign l.lengthVar (decrease l)) (.write (address l) (.lit 0))
def erase (l : Layout) : Cmd := .loop (nonempty l) (eraseBody l)

/-- This implementation theorem pays for every erase-loop test and store. -/
theorem erase_correct (l : Layout) (n : Nat) (s : Store)
    (bound : n ≤ l.capacity) (len : s.vars .word l.lengthVar.name = n)
    (suffix : ∀ i, n ≤ i → i < l.capacity → s.heap (l.base + i) = 0) :
    ∃ t, Eval (erase l) s (12 * n + 3) t ∧ Valid l true [] t ∧ Writes l.footprint s t := by
  induction n generalizing s with
  | zero =>
    refine ⟨s, ?_, ⟨by simp, len, by simp, ?_⟩, Writes.refl _ _⟩
    · apply Eval.whileFalse
      simp [nonempty, Condition.eval, Expr.eval, Comparison.eval, len]
    · intro _ i _ hi
      exact suffix i (by omega) hi
  | succ n ih =>
    let t := (s.set l.lengthVar n).write (l.base + n) 0
    have step : Eval (eraseBody l) s 9 t := by
      have exe := Eval.seq (Eval.assign l.lengthVar (decrease l) s)
        (Eval.write (address l) (.lit 0) _)
      simpa [eraseBody, decrease, address, Expr.cost, Expr.eval, Op.eval, Op.machine,
        Checked.BinOp.eval, Store.set, len, t] using exe
    have length : t.vars .word l.lengthVar.name = n := by simp [t, Store.write, Store.set]
    have suffix' : ∀ i, n ≤ i → i < l.capacity → t.heap (l.base + i) = 0 := by
      intro i hi hb
      by_cases eq : i = n
      · subst i; simp [t, Store.write]
      · have ne : l.base + i ≠ l.base + n := by omega
        simpa [t, Store.write, Store.set, Function.update_apply, ne, Ne.symm ne, eq] using
          suffix i (by omega) hb
    obtain ⟨u, exec, valid, writes⟩ := ih t (by omega) length suffix'
    refine ⟨u, ?_, valid, ?_⟩
    · have test : (nonempty l).eval s = true := by
        simp [nonempty, Condition.eval, Expr.eval, Comparison.eval, len]
      have exe := Eval.whileTrue test step exec
      convert exe using 1
      simp [nonempty, Condition.cost, Expr.cost]
      omega
    · exact ((Writes.set _ _ _ (length_owned l)).trans
        (Writes.write _ _ _ (cell_owned l (by omega)))).trans writes

instance clearImplementation (l : Layout) (eager : Bool) :
    Primitive 24 (representation l eager) Buffer.clear (representation l eager) where
  code := if eager then erase l else .assign l.lengthVar (.lit 0)
  correct xs _ r s saved rep := by
    obtain ⟨rfl, hv, rfl⟩ := rep
    cases eager with
    | false =>
      refine ⟨2, _, 0, .assign _ _ _, ⟨rfl, ?_, rfl⟩,
        Writes.set _ _ _ (length_owned l), by simp [Buffer.clear, potential]⟩
      simp [Valid, Buffer.clear, Store.set, Expr.eval]
    | true =>
      obtain ⟨t, exec, valid, writes⟩ := erase_correct l xs.length s hv.1 hv.2.1 (hv.2.2.2 rfl)
      exact ⟨12 * xs.length + 3, t, 0, exec, ⟨rfl, valid, rfl⟩, writes,
        by simp [Buffer.clear, potential]; omega⟩

instance nonemptyImplementation (l : Layout) (eager : Bool) :
    TestImplementation 24 (representation l eager) Buffer.nonempty where
  condition := nonempty l
  correct xs r s saved h := by
    simp only [nonempty, Condition.eval, Expr.eval, Comparison.eval, h.2.1.2.1, Buffer.nonempty]
    cases xs <;> simp
  cost := by simp [nonempty, Condition.cost, Expr.cost]

end AlgoLib.Experimental.RAM.Prototype.Composition.BufferImplementation
