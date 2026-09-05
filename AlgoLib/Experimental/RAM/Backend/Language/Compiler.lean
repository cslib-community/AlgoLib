/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Basic
import AlgoLib.Experimental.RAM.Machine.Output

/-!
# Typed source-to-RAM compiler

Compiles typed expressions and commands to RAM and proves that evaluation is realized by the
compiled instructions with matching observation and charged cost.

Eval.compile is consumed by the generic verified runner. Register and temporary-storage proofs are
implementation responsibilities.

## Further details

# Compilation to RAM, with exact cost and source-state preservation
-/
namespace AlgoLib.Experimental.RAM.Checked.Language

def observe (s : State) : Store := ⟨fun ty name => s.regs (.user ty.tag name), s.memory⟩

def encode (s : Store) : State where
  regs r := match r with
    | .user 0 name => s.vars .word name
    | .user 1 name => s.vars .ptr name
    | _ => 0
  memory := s.heap

@[simp] theorem observe_encode (s : Store) : observe (encode s) = s := by
  cases s with
  | mk vars heap =>
    unfold observe encode
    congr 1
    funext ty name
    cases ty <;> rfl

/-- Preserve all user registers, memory, and earlier temporaries. -/
def Frame (n : Nat) (s t : State) : Prop :=
  t.memory = s.memory ∧ ∀ r, (match r with | .scratch i => i < n | _ => True) →
    t.regs r = s.regs r

theorem Frame.refl (n : Nat) (s : State) : Frame n s s := ⟨rfl, fun _ _ => rfl⟩
theorem Frame.trans {n : Nat} {s t u : State} (h : Frame n s t) (g : Frame n t u) :
    Frame n s u := ⟨g.1.trans h.1, fun r hr => (g.2 r hr).trans (h.2 r hr)⟩
theorem Frame.mono {n m : Nat} {s t : State} (h : Frame n s t) (hm : m ≤ n) :
    Frame m s t := by
  refine ⟨h.1, fun r hr => h.2 r ?_⟩
  cases r <;> simp_all
  omega

theorem Frame.observe {n : Nat} {s t : State} (h : Frame n s t) : observe t = observe s := by
  obtain ⟨hm, hr⟩ := h
  unfold Language.observe
  congr 1
  funext ty name
  exact hr _ trivial

theorem frame_set (s : State) (n v : Nat) : Frame n s (s.set (.scratch n) v) := by
  refine ⟨rfl, ?_⟩
  intro r hr
  have hn : r ≠ .scratch n := by
    cases r <;> simp_all
    omega
  simp [State.set, hn]

@[simp] theorem observe_scratch (s : State) (n v : Nat) :
    observe (s.set (.scratch n) v) = observe s := (frame_set s n v).observe

@[simp] theorem observe_set {ty : Ty} (s : State) (v : Var ty) (n : Nat) :
    observe (s.set v.reg n) = (observe s).set v n := by
  unfold observe Store.set State.set Var.reg
  congr 1
  funext t name
  cases ty <;> cases t <;> simp [Ty.tag, Function.update_apply]

@[simp] theorem observe_write (s : State) (a v : Nat) :
    observe {s with memory := Function.update s.memory a v} = (observe s).write a v := rfl

def Expr.compile {ty : Ty} : Expr ty → Nat → Code
  | .lit v, n => .block [.mov (.scratch n) (.lit v)]
  | .var v, n => .block [.mov (.scratch n) (.reg v.reg)]
  | .bin op x y, n => .seq (x.compile (n + 1)) (.seq (y.compile (n + 2))
      (.block [.bin op.machine (.scratch n) (.reg (.scratch (n + 1)))
        (.reg (.scratch (n + 2)))]))
  | .load a, n => .seq (a.compile n) (.block [.load (.scratch n) (.reg (.scratch n))])

/-- Expression compilation also proves freshness: later expressions cannot clobber
an earlier result. This theorem applies to every expression tree. -/
theorem Expr.correct {ty : Ty} (e : Expr ty) (n : Nat) (s : State) :
    ∃ t, Exec (e.compile n) s e.cost t ∧ Frame n s t ∧
      t.regs (.scratch n) = e.eval (observe s) := by
  induction e generalizing n s with
  | lit v =>
    refine ⟨_, .block _ _, frame_set _ _ _, ?_⟩
    simp [blockEval, Instr.eval, State.set, Operand.eval, Expr.eval]
  | var v =>
    refine ⟨_, .block _ _, frame_set _ _ _, ?_⟩
    simp [blockEval, Instr.eval, State.set, Operand.eval, Expr.eval, observe, Var.reg]
  | bin op x y ihx ihy =>
    obtain ⟨u, hx, hf, hv⟩ := ihx (n + 1) s
    obtain ⟨v, hy, hg, hw⟩ := ihy (n + 2) u
    have hleft := hg.2 (.scratch (n + 1)) (by simp)
    have heval : y.eval (observe u) = y.eval (observe s) := congrArg y.eval hf.observe
    refine ⟨v.set (.scratch n) (op.eval (v.regs (.scratch (n + 1)))
      (v.regs (.scratch (n + 2)))), ?_,
      (hf.mono (by omega)).trans ((hg.mono (by omega)).trans (frame_set v n _)), ?_⟩
    · simpa [Expr.compile, Expr.cost, Nat.add_assoc] using
        Exec.seq hx (Exec.seq hy (Exec.block [.bin op.machine (.scratch n)
          (.reg (.scratch (n + 1))) (.reg (.scratch (n + 2)))] v))
    · simp [State.set, hleft, hv, hw,
        heval, Expr.eval, Op.eval]
  | load a ih =>
    obtain ⟨u, hx, hf, hv⟩ := ih n s
    refine ⟨_, .seq hx (.block _ _), hf.trans (frame_set _ _ _), ?_⟩
    simp [blockEval, Instr.eval, Operand.eval, State.set, hv, hf.1, Expr.eval, observe]

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
  | lit | var => simp [Expr.compile, Code.writes, Instr.writes]
  | bin op x y ihx ihy => simp [Expr.compile, Code.writes, Instr.writes, ihx, ihy]
  | load a ih => simp [Expr.compile, Code.writes, Instr.writes, ih]

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

@[simp] theorem observe_saved (s : State) (d n : Nat) :
    observe (s.set (.saved d) n) = observe s := by
  unfold observe State.set
  congr 1

/-- Independent source execution implies a RAM execution with exactly the same
cost and observable store, for arbitrary initial compiler temporaries. -/
theorem Eval.compileAt {c : Cmd} {s t : Store} {k : Nat} (h : Eval c s k t) :
    ∀ (d : Nat) (r : State), observe r = s → ∃ u, Exec (c.compileAt d) r k u ∧ observe u = t := by
  induction h with
  | skip s => intro d r hr; exact ⟨r, .block [] r, hr⟩
  | assign v e s =>
    intro d r hr
    obtain ⟨u, hx, hf, hv⟩ := e.correct 0 r
    refine ⟨_, .seq hx (.block _ _), ?_⟩
    simp [blockEval, Instr.eval, Operand.eval, hv, hf.observe, hr]
  | write a v s =>
    intro d r hr
    obtain ⟨u, hx, hf, ha⟩ := a.correct 0 r
    obtain ⟨w, hy, hg, hv⟩ := v.correct 1 u
    have ha' := hg.2 (.scratch 0) (by simp)
    refine ⟨{w with memory := (Function.update w.memory (w.regs (.scratch 0))
      (w.regs (.scratch 1)))}, ?_, ?_⟩
    · simpa [Cmd.compileAt, Expr.cost, Nat.add_assoc] using
        Exec.seq hx (Exec.seq hy (Exec.block [.store (.reg (.scratch 0))
          (.reg (.scratch 1))] w))
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
    · have hx := Exec.seq (Exec.block [.mov (.saved d) (.reg v.reg)] r)
        (Exec.seq hu (Exec.seq (Exec.block [.mov v.reg (.reg (.scratch 0))] u)
          (Exec.seq hw (Exec.block [.mov v.reg (.reg (.saved d))] w))))
      convert hx using 1
      simp
      omega
    · rw [observe_set, ht, hsave]
      have hv : r.regs v.reg = s.vars ty v.name :=
        congrArg (fun s : Store => s.vars ty v.name) hr
      rw [hv]

/-- Public entry point starts with an empty saved-register stack. -/
theorem Eval.compile {c : Cmd} {s t : Store} {k : Nat} (h : Eval c s k t)
    (r : State) (hr : observe r = s) : ∃ u, Exec c.compile r k u ∧ observe u = t :=
  h.compileAt 0 r hr

end AlgoLib.Experimental.RAM.Checked.Language
