/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Compiler
import AlgoLib.Experimental.RAM.Backend.Native.Natural

/-!
# Typed total contracts and runner binding

Defines implementation-level contracts and packages them as Methods that can execute without fuel.

The runner obtains termination and cost from the same certificate used to establish the
postcondition. The public method wrapper is in Authoring/Methods.

## Further details

# Reusable total-correctness and time-credit contracts
-/
namespace AlgoLib.Experimental.RAM.Checked.Language

/-- A total functional and cost contract, stated entirely at source level. -/
def Contract (c : Cmd) (P : Store → Prop) (Q : Store → Store → Prop)
    (budget : Store → Nat) : Prop :=
  ∀ s, P s → ∃ k t, Eval c s k t ∧ Q s t ∧ k ≤ budget s

/-- Time credits compose without guessing intermediate execution lengths. -/
def Triple (c : Cmd) (P Q : Store → Nat → Prop) : Prop :=
  ∀ s credits, P s credits → ∃ k t, Eval c s k t ∧ k ≤ credits ∧ Q t (credits - k)

theorem Triple.seq {a b : Cmd} {P R Q : Store → Nat → Prop}
    (ha : Triple a P R) (hb : Triple b R Q) : Triple (.seq a b) P Q := by
  intro s credits hs
  obtain ⟨i, u, hi, hci, hu⟩ := ha s credits hs
  obtain ⟨j, t, hj, hcj, ht⟩ := hb u (credits - i) hu
  refine ⟨i + j, t, .seq hi hj, by omega, ?_⟩
  simpa [Nat.sub_sub] using ht

/-- Assignment and store VCs are substitution plus a credit check. -/
theorem Triple.assign {ty : Ty} (v : Var ty) (e : Expr ty) (Q : Store → Nat → Prop) :
    Triple (.assign v e) (fun s credits => e.cost + 1 ≤ credits ∧
      Q (s.set v (e.eval s)) (credits - (e.cost + 1))) Q := by
  intro s credits h
  exact ⟨_, _, .assign _ _ _, h.1, h.2⟩

theorem Triple.write (a : Expr .ptr) (v : Expr .word) (Q : Store → Nat → Prop) :
    Triple (.write a v) (fun s credits => a.cost + v.cost + 1 ≤ credits ∧
      Q (s.write (a.eval s) (v.eval s)) (credits - (a.cost + v.cost + 1))) Q := by
  intro s credits h
  exact ⟨_, _, .write _ _ _, h.1, h.2⟩

/-- Initialization, maintenance/payment, and exit are the only loop obligations.
The potential may use arbitrary ghost mathematics. It cannot affect runtime.
A positive guard cost makes the payment obligation imply termination. -/
structure LoopVC (q : Condition) (body : Cmd) (I Q : Store → Prop)
    (potential : Store → Nat) : Prop where
  step : ∀ s, I s → q.eval s = true →
    ∃ k t, Eval body s k t ∧ I t ∧ q.cost + k + potential t ≤ potential s
  exit : ∀ s, I s → q.eval s = false → Q s

theorem Condition.cost_pos (q : Condition) : 0 < q.cost := by
  unfold Condition.cost
  omega

theorem LoopVC.sound {q : Condition} {body : Cmd} {I Q : Store → Prop}
    {potential : Store → Nat} (h : LoopVC q body I Q potential) :
    Contract (.loop q body) I (fun _ t => Q t) (fun s => potential s + q.cost) := by
  intro s hs
  change ∃ k t, Eval (.loop q body) s k t ∧ Q t ∧ k ≤ potential s + q.cost
  generalize hn : potential s = n
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    cases hq : q.eval s with
    | false => exact ⟨_, s, .whileFalse hq, h.exit s hs hq, by omega⟩
    | true =>
      obtain ⟨i, u, hu, hi, hp⟩ := h.step s hs hq
      have hpos := q.cost_pos
      obtain ⟨j, t, ht, hQ, hj⟩ := ih (potential u) (by omega) u hi rfl
      exact ⟨_, t, .whileTrue hq hu ht, hQ, by omega⟩

/-- Package verification once. Running needs input and its precondition, never fuel. -/
structure Method where
  body : Cmd
  requires : Store → Prop
  ensures : Store → Store → Prop
  budget : Store → Nat
  verification : Contract body requires ensures budget

/-- Natural observation of the legacy implementation contract's cells. -/
def integerObserve (s : Integer.State) : Store :=
  Native.Natural.project (Native.observe s)

/-- Input encoding uses native integer cells directly. -/
def integerEncode (s : Store) : Integer.State := Native.encode (Native.Natural.store s)

@[simp] theorem integerObserve_encode (s : Store) :
    integerObserve (integerEncode s) = s := by
  simp [integerObserve, integerEncode]

/-- Default execution compiles through the native integer compiler only. -/
def Method.integerCode (p : Method) : Integer.Code :=
  (Native.Natural.command p.body).compile

private theorem Method.integerTerminates (p : Method) (s : Store) (hs : p.requires s) :
    Integer.Terminates p.integerCode (integerEncode s) := by
  obtain ⟨k, t, hx, _, _⟩ := p.verification s hs
  obtain ⟨j, hj, _⟩ := Native.Natural.preserves hx
  exact Native.terminates _ _ ⟨j, _, hj⟩

/-- Actual integer-machine result and exact instruction count, with no fuel. -/
def Method.run (p : Method) (s : Store) (hs : p.requires s) : Nat × Store :=
  let result := Integer.run p.integerCode (integerEncode s) (p.integerTerminates s hs)
  (result.1, integerObserve result.2)

/-- The returned count belongs to actual integer instructions, not the old IR semantics. -/
theorem Method.run_exec (p : Method) (s : Store) (hs : p.requires s) :
    ∃ final, Integer.Exec p.integerCode (integerEncode s)
      (p.run s hs).1 final ∧ (p.run s hs).2 = integerObserve final :=
  ⟨_, Integer.run_correct _ _ (p.integerTerminates s hs), rfl⟩

/-- Source contracts and public bounds survive replacement of the compiler. -/
theorem Method.correct (p : Method) (s : Store) (hs : p.requires s) :
    (∃ k, Eval p.body s k (p.run s hs).2) ∧
      p.ensures s (p.run s hs).2 ∧ (p.run s hs).1 ≤ 2 * p.budget s := by
  obtain ⟨k, t, hx, post, paid⟩ := p.verification s hs
  obtain ⟨j, hj, cost⟩ := Native.Natural.preserves hx
  obtain ⟨u, hu, observed⟩ := hj.compile _ (Native.observe_encode _)
  simp only [Method.run, Method.integerCode, integerEncode, Integer.run_eq hu,
    integerObserve, observed, Native.Natural.project_store]
  exact ⟨⟨k, hx⟩, post, by omega⟩


/-- Source credit contracts certify actual native integer execution. The bound
includes lowering overhead; source and machine step counts need not coincide. -/
theorem Contract.ram {c : Cmd} {P : Store → Prop} {Q : Store → Store → Prop}
    {budget : Store → Nat} (h : Contract c P Q budget) (s : Store) (hs : P s) :
    ∃ k t, Integer.Exec (Native.Natural.command c).compile (integerEncode s) k t ∧
      Q s (integerObserve t) ∧ k ≤ 2 * budget s := by
  obtain ⟨k, t, hx, hQ, hk⟩ := h s hs
  obtain ⟨j, hj, cost⟩ := Native.Natural.preserves hx
  obtain ⟨u, hu, observed⟩ := hj.compile _ (Native.observe_encode _)
  refine ⟨j, u, hu, ?_, by omega⟩
  simpa only [integerObserve, observed, Native.Natural.project_store] using hQ

end AlgoLib.Experimental.RAM.Checked.Language
