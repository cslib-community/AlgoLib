/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Native.Expressions
import AlgoLib.Experimental.RAM.Machine.Integer.Frame

/-!
# Native integer compilation

Typed expressions and structured commands lower directly to the integer machine.
The preservation theorem connects independent source evaluation to target execution
with exactly the same instruction count, including loops and saved local variables.
-/
namespace AlgoLib.Experimental.RAM.Native
open Integer
open Checked (Reg)

def Condition.prepare (q : Condition) : Code :=
  .seq (q.left.compile 0) (q.right.compile 1)

def Condition.test (q : Condition) : Test :=
  match q.comparison with
  | .lt => .lt (.reg (.scratch 0)) (.reg (.scratch 1))
  | .le => .le (.reg (.scratch 0)) (.reg (.scratch 1))
  | .eq => .eq (.reg (.scratch 0)) (.reg (.scratch 1))

theorem Condition.correct (q : Condition) (s : State) :
    ∃ t, Exec q.prepare s (q.left.cost + q.right.cost) t ∧
      observe t = observe s ∧ q.test.eval t = q.eval (observe s) := by
  obtain ⟨u, hu, hf, hl⟩ := q.left.correct 0 s
  obtain ⟨t, ht, hg, hr⟩ := q.right.correct 1 u
  refine ⟨t, .seq hu ht, hg.observe.trans hf.observe, ?_⟩
  have hl' := hg.2 (.scratch 0) (by simp)
  rw [hf.observe] at hr
  cases hc : q.comparison <;>
    simp [Condition.test, Condition.eval, Comparison.eval, Test.eval, Operand.eval, hc, hl', hl, hr]

def Cmd.compileAt : Cmd → Nat → Code
  | .skip, _ => .block []
  | .assign v e, _ => .seq (e.compile 0) (.block [.mov v.reg (.reg (.scratch 0))])
  | .write a v, _ => .seq (a.compile 0) (.seq (v.compile 1)
      (.block [.store (.reg (.scratch 0)) (.reg (.scratch 1))]))
  | .seq a b, d => .seq (a.compileAt d) (b.compileAt d)
  | .branch q a b, d => .seq q.prepare (.ite q.test (a.compileAt d) (b.compileAt d))
  | .loop q b, d => .seq q.prepare (.while q.test (.seq (b.compileAt d) q.prepare))
  | .localVar v e b, d => .seq (.block [.mov (.saved d) (.reg v.reg)])
      (.seq (e.compile 0) (.seq (.block [.mov v.reg (.reg (.scratch 0))])
        (.seq (b.compileAt (d + 1)) (.block [.mov v.reg (.reg (.saved d))]))))

def Cmd.compile (c : Cmd) : Code := c.compileAt 0

@[simp] theorem Expr.writes_saved {ty : Ty} (e : Expr ty) (n i : Nat) :
    (e.compile n).writes (.saved i) = false := by
  induction e generalizing n with
  | lit => simp [Expr.compile, Code.writes, Instr.writes]
  | @var ty v => cases ty <;> simp [Expr.compile, normalize, Code.writes, Instr.writes]
  | bin op x y ihx ihy =>
    cases op <;> simp [Expr.compile, Op.finish, normalize, Code.writes, Instr.writes, ihx, ihy]
  | @load ty a ih => cases ty <;> simp [Expr.compile, normalize, Code.writes, Instr.writes, ih]
  | ofNat a ih | pointer a ih => exact ih n
  | toNat a ih => simp [Expr.compile, normalize, Code.writes, Instr.writes, ih]

@[simp] theorem Condition.writes_saved (q : Condition) (i : Nat) :
    q.prepare.writes (.saved i) = false := by
  simp [Condition.prepare, Code.writes]

theorem Cmd.writes_saved (c : Cmd) (d i : Nat) (hi : i < d) :
    (c.compileAt d).writes (.saved i) = false := by
  induction c generalizing d with
  | skip | assign | write => simp [Cmd.compileAt, Code.writes, Instr.writes, Var.reg]
  | seq a b iha ihb => simp [Cmd.compileAt, Code.writes, iha d hi, ihb d hi]
  | branch q a b iha ihb => simp [Cmd.compileAt, Code.writes, iha d hi, ihb d hi]
  | loop q b ih => simp [Cmd.compileAt, Code.writes, ih d hi]
  | localVar v e b ih =>
    have hn : d ≠ i := by omega
    simp [Cmd.compileAt, Code.writes, Instr.writes, Var.reg, hn, ih (d + 1) (by omega)]

@[simp] theorem observe_saved (s : State) (d : Nat) (n : Int) :
    observe (s.set (.saved d) n) = observe s := by
  unfold observe State.set
  congr 1

private theorem mov_exec (s : State) (r : Reg) (v : Operand) :
    Exec (.block [.mov r v]) s 1 (s.set r (v.eval s)) := .block rfl

/-- Independent source execution implies a RAM execution with exactly the same
cost and observable store, for arbitrary initial compiler temporaries. -/
theorem Eval.compileAt {c : Cmd} {s t : Store} {k : Nat} (h : Eval c s k t) :
    ∀ (d : Nat) (r : State), observe r = s → ∃ u, Exec (c.compileAt d) r k u ∧ observe u = t := by
  induction h with
  | skip s => intro d r hr; exact ⟨r, .block rfl, hr⟩
  | assign v e s =>
    intro d r hr
    obtain ⟨u, hx, hf, hv⟩ := e.correct 0 r
    refine ⟨_, .seq hx (.block rfl), ?_⟩
    simp [Operand.eval, hv, hf.observe, hr]
  | write a v s =>
    intro d r hr
    obtain ⟨u, hx, hf, ha⟩ := a.correct 0 r
    obtain ⟨w, hy, hg, hv⟩ := v.correct 1 u
    have ha' := hg.2 (.scratch 0) (by simp)
    refine ⟨{w with memory := (Function.update w.memory (w.regs (.scratch 0)).toNat
      (w.regs (.scratch 1)))}, ?_, ?_⟩
    · have hnonneg : 0 ≤ w.regs (.scratch 0) := by
        rw [ha', ha]
        exact a.nonnegative (observe r) (by decide)
      have hs : Exec (.block [.store (.reg (.scratch 0)) (.reg (.scratch 1))]) w 1
          { w with memory := (Function.update w.memory (w.regs (.scratch 0)).toNat
              (w.regs (.scratch 1))) } :=
        .block (by simp [blockEval, Instr.eval, Operand.eval, address, hnonneg])
      simpa [Cmd.compileAt, Nat.add_assoc] using Exec.seq hx (Exec.seq hy hs)
    · simp [ha', ha, hv, observe_write,
        hg.observe, hf.observe, hr]
  | seq _ _ iha ihb =>
    intro d r hr
    obtain ⟨u, hu, heu⟩ := iha d r hr
    obtain ⟨v, hv, hev⟩ := ihb d u heu
    exact ⟨v, .seq hu hv, hev⟩
  | @ifTrue q a b s t k hq _ ih =>
    intro d r hr
    obtain ⟨u, hu, heu, htest⟩ := q.correct r
    obtain ⟨v, hv, hev⟩ := ih d u (heu.trans hr)
    refine ⟨v, ?_, hev⟩
    simpa [Condition.cost, Nat.add_assoc] using
      Exec.seq hu (Exec.ifTrue (htest.trans (hr ▸ hq)) hv)
  | @ifFalse q a b s t k hq _ ih =>
    intro d r hr
    obtain ⟨u, hu, heu, htest⟩ := q.correct r
    obtain ⟨v, hv, hev⟩ := ih d u (heu.trans hr)
    refine ⟨v, ?_, hev⟩
    simpa [Condition.cost, Nat.add_assoc] using
      Exec.seq hu (Exec.ifFalse (htest.trans (hr ▸ hq)) hv)
  | @whileFalse q b s hq =>
    intro d r hr
    obtain ⟨u, hu, heu, htest⟩ := q.correct r
    exact ⟨u, .seq hu (.whileFalse (htest.trans (hr ▸ hq))), heu.trans hr⟩
  | @whileTrue q b s u t i j hq _ _ ihb ihl =>
    intro d r hr
    obtain ⟨v, hv, hev, htest⟩ := q.correct r
    obtain ⟨w, hw, hew⟩ := ihb d v (hev.trans hr)
    obtain ⟨z, hz, hez⟩ := ihl d w hew
    cases hz with
    | seq hp hl =>
      refine ⟨z, ?_, hez⟩
      simpa [Cmd.compileAt, Condition.cost, Nat.add_assoc] using
        Exec.seq hv (Exec.whileTrue (htest.trans (hr ▸ hq)) (Exec.seq hw hp) hl)
  | @localVar ty v e body s t k hb ih =>
    intro d r hr
    let saved := r.set (.saved d) (r.regs v.reg)
    have hsaved : observe saved = s := by simp [saved, hr]
    obtain ⟨u, hu, hf, he⟩ := e.correct 0 saved
    let entry := u.set v.reg (u.regs (.scratch 0))
    have hentry : observe entry = s.set v (e.eval s) := by
      simp [entry, he, hf.observe, hsaved]
    obtain ⟨w, hw, ht⟩ := ih (d + 1) entry hentry
    have hframe := hw.frame_register (.saved d) (body.writes_saved (d + 1) d (by omega))
    have hsave : w.regs (.saved d) = r.regs v.reg := by
      rw [hframe]
      simp [entry, State.set, Var.reg, hf.2 (.saved d) trivial, saved]
    refine ⟨w.set v.reg (w.regs (.saved d)), ?_, ?_⟩
    · have hx := Exec.seq (mov_exec r (.saved d) (.reg v.reg))
        (Exec.seq hu (Exec.seq (mov_exec u v.reg (.reg (.scratch 0)))
          (Exec.seq hw (mov_exec w v.reg (.reg (.saved d))))))
      convert hx using 1
      omega
    · rw [observe_set, ht, hsave]
      have hv : r.regs v.reg = s.vars ty v.name :=
        congrArg (fun s : Store => s.vars ty v.name) hr
      rw [hv]

/-- Public entry point starts with an empty saved-register stack. -/
theorem Eval.compile {c : Cmd} {s t : Store} {k : Nat} (h : Eval c s k t)
    (r : State) (hr : observe r = s) : ∃ u, Exec c.compile r k u ∧ observe u = t :=
  h.compileAt 0 r hr

end AlgoLib.Experimental.RAM.Native
