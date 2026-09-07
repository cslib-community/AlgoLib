/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Compiler.Native.Basic

/-!
# Verified native integer expression compilation

Every typed expression lowers directly to Int-RAM instructions. The theorem proves
its exact instruction count, integer result, and preservation of user storage and
older temporaries. It does not invoke the Nat compiler or encode signed values as
pairs. Natural reads and subtraction carry explicit normalization instructions.
-/
namespace AlgoLib.Experimental.RAM.Native
open Integer
open Checked (Reg)

def observe (s : State) : Store := ⟨fun ty name => s.regs (.user ty.tag name), s.memory⟩

def encode (s : Store) : State where
  regs r := match r with
    | .user 0 name => s.vars .word name
    | .user 1 name => s.vars .ptr name
    | .user 2 name => s.vars .integer name
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
  unfold Native.observe
  congr 1
  funext ty name
  exact hr _ trivial

theorem frame_set (s : State) (n : Nat) (v : Int) : Frame n s (s.set (.scratch n) v) := by
  refine ⟨rfl, ?_⟩
  intro r hr
  have hn : r ≠ .scratch n := by
    cases r <;> simp_all
    omega
  simp [State.set, hn]

@[simp] theorem observe_scratch (s : State) (n : Nat) (v : Int) :
    observe (s.set (.scratch n) v) = observe s := (frame_set s n v).observe

@[simp] theorem observe_set {ty : Ty} (s : State) (v : Var ty) (n : Int) :
    observe (s.set v.reg n) = (observe s).set v n := by
  unfold observe Store.set State.set Var.reg
  congr 1
  funext t name
  cases ty <;> cases t <;> simp [Ty.tag, Function.update_apply]

@[simp] theorem observe_write (s : State) (a : Nat) (v : Int) :
    observe {s with memory := Function.update s.memory a v} = (observe s).write a v := rfl

/-- Normalization is an explicit target instruction only for natural types. -/
def normalize (ty : Ty) (n : Nat) : Code :=
  match ty with
  | .integer => .block []
  | _ => .block [.bin .max (.scratch n) (.reg (.scratch n)) (.lit 0)]

theorem normalize_correct (ty : Ty) (n : Nat) (s : State) :
    ∃ t, Exec (normalize ty n) s (ty.readCost - 1) t ∧ Frame n s t ∧
      t.regs (.scratch n) = ty.normalize (s.regs (.scratch n)) := by
  cases ty
  all_goals first
    | exact ⟨s, .block rfl, Frame.refl _ _, rfl⟩
    | refine ⟨_, .block (by rfl), frame_set _ _ _, ?_⟩
      simp [State.set, BinOp.eval, Ty.normalize, Operand.eval]

def Op.finish {a b c : Ty} (op : Op a b c) (n : Nat) : Code :=
  let first := Code.block [.bin op.machine (.scratch n)
    (.reg (.scratch (n + 1))) (.reg (.scratch (n + 2)))]
  match op with
  | .sub => .seq first (normalize .word n)
  | _ => first

theorem Op.finish_correct {a b c : Ty} (op : Op a b c) (n : Nat) (s : State) :
    ∃ t, Exec (op.finish n) s op.cost t ∧ Frame n s t ∧
      t.regs (.scratch n) = op.eval (s.regs (.scratch (n + 1)))
        (s.regs (.scratch (n + 2))) := by
  cases op
  all_goals first
    | refine ⟨_, .seq (.block (by rfl))
        (.block (by rfl)),
        (frame_set _ _ _).trans (frame_set _ _ _), ?_⟩
      simp [State.set, Op.eval, Op.machine, BinOp.eval, Operand.eval]
    | refine ⟨_, .block (by rfl), frame_set _ _ _, ?_⟩
      simp [State.set, Op.eval, Op.machine, BinOp.eval, Operand.eval]

def Expr.compile {ty : Ty} : Expr ty → Nat → Code
  | .lit v, n => .block [.mov (.scratch n) (.lit (ty.normalize v))]
  | .var v, n => .seq (.block [.mov (.scratch n) (.reg v.reg)]) (normalize ty n)
  | .bin op x y, n => .seq (x.compile (n + 1))
      (.seq (y.compile (n + 2)) (op.finish n))
  | .load a, n => .seq (a.compile n)
      (.seq (.block [.load (.scratch n) (.reg (.scratch n))]) (normalize ty n))
  | .ofNat a, n | .pointer a, n => a.compile n
  | .toNat a, n => .seq (a.compile n) (normalize .word n)

/-- Exact native execution and a compositional temporary-register frame. -/
theorem Expr.correct {ty : Ty} (e : Expr ty) (n : Nat) (s : State) :
    ∃ t, Exec (e.compile n) s e.cost t ∧ Frame n s t ∧
      t.regs (.scratch n) = e.eval (observe s) := by
  induction e generalizing n s with
  | @lit ty v =>
    refine ⟨_, .block (by rfl), frame_set _ _ _, ?_⟩
    simp [State.set, Expr.eval, Operand.eval]
  | @var ty v =>
    let u := s.set (.scratch n) (s.regs v.reg)
    obtain ⟨t, hx, hf, hv⟩ := normalize_correct ty n u
    have hm : Exec (.block [.mov (.scratch n) (.reg v.reg)]) s 1 u :=
      .block (by simp [blockEval, Instr.eval, Operand.eval, u])
    refine ⟨t, ?_, (frame_set _ _ _).trans hf, ?_⟩
    · have hc : 1 + (ty.readCost - 1) = ty.readCost := by cases ty <;> rfl
      simpa [Expr.compile, Expr.cost, hc] using Exec.seq hm hx
    · simpa [u, State.set, Expr.eval, observe, Var.reg] using hv
  | bin op x y ihx ihy =>
    obtain ⟨u, hx, hf, hv⟩ := ihx (n + 1) s
    obtain ⟨v, hy, hg, hw⟩ := ihy (n + 2) u
    obtain ⟨t, ht, hi, hr⟩ := op.finish_correct n v
    have hleft := hg.2 (.scratch (n + 1)) (by simp)
    have heval : y.eval (observe u) = y.eval (observe s) := congrArg y.eval hf.observe
    refine ⟨t, ?_, (hf.mono (by omega)).trans ((hg.mono (by omega)).trans hi), ?_⟩
    · simpa [Expr.compile, Expr.cost, Nat.add_assoc] using Exec.seq hx (Exec.seq hy ht)
    · simpa [hleft, hv, hw, heval, Expr.eval] using hr
  | @load ty a ih =>
    obtain ⟨u, hx, hf, hv⟩ := ih n s
    have ha := a.nonnegative (observe s) (by decide)
    let v := u.set (.scratch n) (u.memory (u.regs (.scratch n)).toNat)
    have hl : Exec (.block [.load (.scratch n) (.reg (.scratch n))]) u 1 v := by
      apply Exec.block
      simp [blockEval, Instr.eval, Operand.eval, address, hv, ha, v]
    obtain ⟨t, ht, hg, hw⟩ := normalize_correct ty n v
    refine ⟨t, ?_, hf.trans ((frame_set _ _ _).trans hg), ?_⟩
    · have hc : 1 + (ty.readCost - 1) = ty.readCost := by cases ty <;> rfl
      simpa [Expr.compile, Expr.cost, hc] using Exec.seq hx (Exec.seq hl ht)
    · simpa [v, State.set, hv, hf.1, Expr.eval, observe] using hw
  | ofNat a ih => exact ih n s
  | pointer a ih => exact ih n s
  | toNat a ih =>
    obtain ⟨u, hx, hf, hv⟩ := ih n s
    obtain ⟨t, ht, hg, hw⟩ := normalize_correct .word n u
    exact ⟨t, .seq hx ht, hf.trans hg, by simpa [hv, Expr.eval, Ty.normalize] using hw⟩

end AlgoLib.Experimental.RAM.Native
