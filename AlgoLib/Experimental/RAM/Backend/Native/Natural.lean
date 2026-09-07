/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Native.Execution
import AlgoLib.Experimental.RAM.Backend.Language.Basic

/-!
# Reusing natural implementation certificates with native compilation

The historical natural implementation IR translates to the native typed IR,
without invoking the Nat machine compiler. This adapter preserves existing
implementation proofs during migration. It is not the signed frontend lowering:
native signed implementations use the integer constructors directly.
-/
namespace AlgoLib.Experimental.RAM.Native.Natural
set_option autoImplicit true
set_option relaxedAutoImplicit true

abbrev ty : Checked.Language.Ty → Native.Ty | .word => .word | .ptr => .ptr

def var {t : Checked.Language.Ty} (v : Checked.Language.Var t) : Native.Var (ty t) := ⟨v.name⟩

def store (s : Checked.Language.Store) : Native.Store where
  vars t name := match t with
    | .word => s.vars .word name
    | .ptr => s.vars .ptr name
    | .integer => 0
  heap a := s.heap a

def project (s : Native.Store) : Checked.Language.Store where
  vars t name := (s.vars (ty t) name).toNat
  heap a := (s.heap a).toNat

@[simp] theorem project_store (s : Checked.Language.Store) : project (store s) = s := by
  cases s
  unfold project store
  congr 1
  funext t name
  cases t <;> simp [ty]

@[simp] theorem store_set (s : Checked.Language.Store) (v : Checked.Language.Var t) (n : Nat) :
    store (s.set v n) = (store s).set (var v) n := by
  unfold store Checked.Language.Store.set Native.Store.set var
  congr 1
  funext u name
  cases t <;> cases u <;> simp [ty]

@[simp] theorem store_write (s : Checked.Language.Store) (a n : Nat) :
    store (s.write a n) = (store s).write a n := by
  unfold store Checked.Language.Store.write Native.Store.write
  congr 1
  funext i
  by_cases hi : i = a <;> simp [hi, Function.update_apply]

def op : Checked.Language.Op a b c → Native.Op (ty a) (ty b) (ty c)
  | .add => .add | .sub => .sub | .mul => .mul | .offset => .offset

def expr : Checked.Language.Expr t → Native.Expr (ty t)
  | .lit n => .lit n
  | .var v => .var (var v)
  | .bin o x y => .bin (op o) (expr x) (expr y)
  | .load a => .load (expr a)

@[simp] theorem expr_eval (e : Checked.Language.Expr t) (s : Checked.Language.Store) :
    (expr e).eval (store s) = (e.eval s : Int) := by
  induction e with
  | @lit t n => cases t <;> simp [expr, Native.Expr.eval, Checked.Language.Expr.eval, ty, Ty.normalize]
  | @var t v => cases t <;> simp [expr, Native.Expr.eval, Checked.Language.Expr.eval, ty,
      Ty.normalize, store, var]
  | bin o x y ihx ihy =>
    cases o <;> simp [expr, Native.Expr.eval, Checked.Language.Expr.eval, op,
      Native.Op.eval, Native.Op.machine, Checked.Language.Op.eval, Checked.Language.Op.machine,
      Checked.BinOp.eval, Integer.BinOp.eval, ihx, ihy, Int.ofNat_sub] <;> omega
  | load a ih =>
    change max (s.heap ((expr a).eval (store s)).toNat : Int) 0 = _
    rw [ih]
    simp [Checked.Language.Expr.eval]

theorem expr_cost (e : Checked.Language.Expr t) : (expr e).cost ≤ 2 * e.cost := by
  induction e with
  | @lit t n => cases t <;> simp [expr, Native.Expr.cost, Checked.Language.Expr.cost]
  | @var t v =>
    cases t <;> simp [expr, Native.Expr.cost, Checked.Language.Expr.cost, ty, Ty.readCost]
  | bin o x y ihx ihy =>
    cases o <;>
      simp only [expr, Native.Expr.cost, Checked.Language.Expr.cost, op, Native.Op.cost] <;> omega
  | load a ih =>
    change (expr a).cost + 2 ≤ 2 * (a.cost + 1)
    omega

def comparison : Checked.Language.Comparison → Native.Comparison
  | .lt => .lt | .le => .le | .eq => .eq

def condition (q : Checked.Language.Condition) : Native.Condition :=
  ⟨ty q.ty, comparison q.comparison, expr q.left, expr q.right⟩

@[simp] theorem condition_eval (q : Checked.Language.Condition) (s : Checked.Language.Store) :
    (condition q).eval (store s) = q.eval s := by
  cases h : q.comparison <;>
    simp [condition, Native.Condition.eval, Checked.Language.Condition.eval,
    comparison, h, Native.Comparison.eval, Checked.Language.Comparison.eval]

theorem condition_cost (q : Checked.Language.Condition) : (condition q).cost ≤ 2 * q.cost := by
  have := expr_cost q.left
  have := expr_cost q.right
  simp only [condition, Native.Condition.cost, Checked.Language.Condition.cost]
  omega

def command : Checked.Language.Cmd → Native.Cmd
  | .skip => .skip
  | .assign v e => .assign (var v) (expr e)
  | .write a e => .write (expr a) (expr e)
  | .seq a b => .seq (command a) (command b)
  | .branch q a b => .branch (condition q) (command a) (command b)
  | .loop q b => .loop (condition q) (command b)
  | .localVar v e b => .localVar (var v) (expr e) (command b)

/-- Old implementation certificates reconstruct native certificates compositionally.
Only the cost bound changes; the entire final mathematical store is preserved. -/
theorem preserves {c : Checked.Language.Cmd} {s t : Checked.Language.Store} {k : Nat}
    (h : Checked.Language.Eval c s k t) :
    ∃ j, Native.Eval (command c) (store s) j (store t) ∧ j ≤ 2 * k := by
  induction h with
  | skip s => exact ⟨0, .skip _, by omega⟩
  | assign v e s =>
    refine ⟨(expr e).cost + 1, ?_, ?_⟩
    · simpa [command] using Native.Eval.assign (var v) (expr e) (store s)
    · have := expr_cost e; omega
  | write a e s =>
    refine ⟨(expr a).cost + (expr e).cost + 1, ?_, ?_⟩
    · have he := Native.Eval.write (expr a) (expr e) (store s)
      rw [expr_eval a, expr_eval e] at he
      simpa only [command, store_write, Int.toNat_natCast] using he
    · have := expr_cost a; have := expr_cost e; omega
  | seq _ _ iha ihb =>
    obtain ⟨i, hi, hci⟩ := iha
    obtain ⟨j, hj, hcj⟩ := ihb
    exact ⟨_, .seq hi hj, by omega⟩
  | @ifTrue q a b s t k hq _ ih =>
    obtain ⟨j, hj, hc⟩ := ih
    exact ⟨_, .ifTrue (by simpa using hq) hj, by have := condition_cost q; omega⟩
  | @ifFalse q a b s t k hq _ ih =>
    obtain ⟨j, hj, hc⟩ := ih
    exact ⟨_, .ifFalse (by simpa using hq) hj, by have := condition_cost q; omega⟩
  | @whileFalse q b s hq =>
    exact ⟨_, .whileFalse (by simpa using hq), condition_cost q⟩
  | @whileTrue q b s u t i j hq _ _ ihb ihl =>
    obtain ⟨i', hi, hci⟩ := ihb
    obtain ⟨j', hj, hcj⟩ := ihl
    exact ⟨_, .whileTrue (by simpa using hq) hi hj, by have := condition_cost q; omega⟩
  | @localVar t v e b s u k _ ih =>
    obtain ⟨j, hj, hc⟩ := ih
    have he : Native.Eval (command b)
        ((store s).set (var v) ((expr e).eval (store s))) j (store u) := by
      simpa using hj
    refine ⟨(expr e).cost + 3 + j, ?_, ?_⟩
    · have hv : (store s).vars (ty t) (var v).name = (s.vars t v.name : Int) := by
        cases t <;> rfl
      simpa [command, hv] using Native.Eval.localVar he
    · have := expr_cost e; omega

end AlgoLib.Experimental.RAM.Native.Natural
