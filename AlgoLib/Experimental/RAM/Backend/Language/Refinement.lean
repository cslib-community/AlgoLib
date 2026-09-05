/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Normalization
import AlgoLib.Experimental.RAM.Backend.Memory.Array

/-!
# Instruction-certificate refinement

Maps fixed machine register slots into typed variables and lifts instruction execution facts into
typed contracts with a proved cost overhead.

Concrete adapters call these lemmas. Clients use the resulting Action contracts without register
correspondence or factor-transport arguments.

## Further details

# Reusing instruction-level invariant proofs for typed source programs

This is a proof adapter, not an alternate executable. Supported instruction
certificates lift to source executions. Source normalization then checks the
actual DSL program, and the ordinary verified compiler produces its executable.
The adapter pays up to five source/RAM operations per certificate operation.
-/
namespace AlgoLib.Experimental.RAM.Checked.Language.Refinement

def name : Reg → String
  | .base => "base" | .count => "count" | .limit => "limit" | .cursor => "cursor"
  | .key => "key" | .next => "next" | .temp => "temp" | .live => "live"
  | _ => "$unused"

def supportedReg : Reg → Bool
  | .user _ _ | .scratch _ | .saved _ => false
  | _ => true

def slot (r : Reg) : Var .word := ⟨name r⟩
def memory : ArrayRef := ⟨⟨"$heap"⟩⟩

def view (s : Store) : State := ⟨fun r => s.vars .word (name r), s.heap⟩
def Ready (s : Store) : Prop := s.vars .ptr memory.base.name = 0

def atom : Operand → Expr .word
  | .lit n => .lit n
  | .reg r => .var (slot r)

@[simp] theorem atom_eval (a : Operand) (s : Store) : (atom a).eval s = a.eval (view s) := by
  cases a <;> rfl
@[simp] theorem atom_cost (a : Operand) : (atom a).cost = 1 := by cases a <;> rfl

def operation : BinOp → Op .word .word .word
  | .add => .add | .sub => .sub | .mul => .mul

@[simp] theorem operation_eval (op : BinOp) (x y : Nat) :
    (operation op).eval x y = op.eval x y := by cases op <;> rfl

theorem view_set (s : Store) (r : Reg) (n : Nat) (hr : supportedReg r = true) :
    view (s.set (slot r) n) = (view s).set r n := by
  unfold view Store.set State.set slot
  congr 1
  funext q
  cases r <;> cases q <;> simp_all [supportedReg, name]

@[simp] theorem ready_set (s : Store) (r : Reg) (n : Nat) :
    Ready (s.set (slot r) n) ↔ Ready s := by simp [Ready]
@[simp] theorem ready_write (s : Store) (a v : Nat) : Ready (s.write a v) ↔ Ready s := Iff.rfl

def instruction : Instr → Cmd
  | .mov r a => .assign (slot r) (atom a)
  | .bin op r a b => .assign (slot r) (.bin (operation op) (atom a) (atom b))
  | .load r a => memory.get (atom a) (slot r)
  | .store a b => memory.put (atom a) (atom b)

def supportedInstr : Instr → Bool
  | .mov r _ | .bin _ r _ _ | .load r _ => supportedReg r
  | .store _ _ => true

theorem instruction_correct (i : Instr) (s : Store) (hi : supportedInstr i = true)
    (hs : Ready s) : ∃ k t, Eval (instruction i) s k t ∧ Ready t ∧
      view t = i.eval (view s) ∧ k ≤ 5 := by
  cases i with
  | mov r a =>
    refine ⟨_, _, .assign _ _ _, (ready_set _ _ _).mpr hs, ?_, by simp⟩
    simpa [Instr.eval] using view_set s r ((atom a).eval s) hi
  | bin op r a b =>
    refine ⟨_, _, .assign _ _ _, (ready_set _ _ _).mpr hs, ?_, by simp [Expr.cost]⟩
    simpa [Instr.eval, Expr.eval] using view_set s r
      ((Expr.bin (operation op) (atom a) (atom b)).eval s) hi
  | load r a =>
    refine ⟨_, _, .assign _ _ _, (ready_set _ _ _).mpr hs, ?_, ?_⟩
    · simpa [Instr.eval, ArrayRef.cell, ArrayRef.address, Expr.eval, Op.eval, Op.machine,
        BinOp.eval, show s.vars .ptr memory.base.name = 0 from hs, view] using
        view_set s r ((memory.cell (atom a)).eval s) hi
    · simp [ArrayRef.cell, ArrayRef.address, Expr.cost]
  | store a b =>
    refine ⟨_, _, .write _ _ _, hs, ?_, ?_⟩
    · simp [view, Store.write, Instr.eval, ArrayRef.address, Expr.eval, Op.eval, Op.machine,
        BinOp.eval, show s.vars .ptr memory.base.name = 0 from hs]
    · simp [ArrayRef.address, Expr.cost]

def block : List Instr → Cmd
  | [] => .skip
  | i :: is => .seq (instruction i) (block is)

theorem block_correct (is : List Instr) (s : Store) (hi : is.all supportedInstr = true)
    (hs : Ready s) : ∃ k t, Eval (block is) s k t ∧ Ready t ∧
      view t = blockEval is (view s) ∧ k ≤ 5 * is.length := by
  induction is generalizing s with
  | nil => exact ⟨0, s, .skip _, hs, rfl, by simp⟩
  | cons i is ih =>
    obtain ⟨hfirst, hrest⟩ :=
      (show supportedInstr i = true ∧ is.all supportedInstr = true by simpa using hi)
    obtain ⟨k, u, hu, hready, hview, hk⟩ := instruction_correct i s hfirst hs
    obtain ⟨j, t, ht, htready, htview, hj⟩ := ih u hrest hready
    refine ⟨k + j, t, .seq hu ht, htready, ?_, ?_⟩
    · simpa [blockEval, hview] using htview
    · simp only [List.length_cons]; omega

def condition : Test → Condition
  | .lt a b => ⟨.word, .lt, atom a, atom b⟩
  | .le a b => ⟨.word, .le, atom a, atom b⟩
  | .eq a b => ⟨.word, .eq, atom a, atom b⟩

@[simp] theorem condition_eval (q : Test) (s : Store) :
    (condition q).eval s = q.eval (view s) := by
  cases q <;> simp [condition, Condition.eval, Comparison.eval, Test.eval]
@[simp] theorem condition_cost (q : Test) : (condition q).cost = 3 := by
  cases q <;> simp [condition, Condition.cost]

def lift : Code → Cmd
  | .block is => block is
  | .seq a b => .seq (lift a) (lift b)
  | .ite q a b => .branch (condition q) (lift a) (lift b)
  | .while q b => .loop (condition q) (lift b)

def supported : Code → Bool
  | .block is => is.all supportedInstr
  | .seq a b | .ite _ a b => supported a && supported b
  | .while _ b => supported b

/-- Every certificate execution produces a source execution with the same
memory and visible slots, and with all source overhead explicitly bounded. -/
theorem lift_correct {c : Code} {r t : State} {k : Nat} (h : Exec c r k t)
    (hc : supported c = true) : ∀ s, Ready s → view s = r →
      ∃ j u, Eval (lift c) s j u ∧ Ready u ∧ view u = t ∧ j ≤ 5 * k := by
  induction h with
  | block is r =>
    intro s hs hr
    simpa [lift, hr] using block_correct is s hc hs
  | seq ha hb iha ihb =>
    obtain ⟨hca, hcb⟩ := Bool.and_eq_true_iff.mp hc
    intro s hs hr
    obtain ⟨i, u, hu, huReady, huView, hi⟩ := iha hca s hs hr
    obtain ⟨j, v, hv, hvReady, hvView, hj⟩ := ihb hcb u huReady huView
    exact ⟨i + j, v, .seq hu hv, hvReady, hvView, by omega⟩
  | ifTrue hq hb ih =>
    intro s hs hr
    obtain ⟨j, u, hu, huReady, huView, hj⟩ := ih (Bool.and_eq_true_iff.mp hc).1 s hs hr
    exact ⟨_, u, .ifTrue (by simpa [hr] using hq) hu, huReady, huView, by simp; omega⟩
  | ifFalse hq hb ih =>
    intro s hs hr
    obtain ⟨j, u, hu, huReady, huView, hj⟩ := ih (Bool.and_eq_true_iff.mp hc).2 s hs hr
    exact ⟨_, u, .ifFalse (by simpa [hr] using hq) hu, huReady, huView, by simp; omega⟩
  | whileFalse hq =>
    intro s hs hr
    exact ⟨_, s, .whileFalse (by simpa [hr] using hq), hs, hr, by simp⟩
  | whileTrue hq hb hl ihb ihl =>
    intro s hs hr
    obtain ⟨i, u, hu, huReady, huView, hi⟩ := ihb hc s hs hr
    obtain ⟨j, v, hv, hvReady, hvView, hj⟩ := ihl hc u huReady huView
    exact ⟨_, v, .whileTrue (by simpa [hr] using hq) hu hv, hvReady, hvView, by simp; omega⟩

end AlgoLib.Experimental.RAM.Checked.Language.Refinement
