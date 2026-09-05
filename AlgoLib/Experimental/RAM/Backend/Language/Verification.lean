/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Compiler

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

def Method.run (p : Method) (s : Store) (hs : p.requires s) : Nat × Store :=
  let result := Checked.run p.body.compile (encode s) (by
    obtain ⟨k, t, hx, _, _⟩ := p.verification s hs
    obtain ⟨u, hu, _⟩ := hx.compile (encode s) (observe_encode s)
    exact ⟨k, u, hu⟩)
  (result.1, observe result.2)

theorem Method.correct (p : Method) (s : Store) (hs : p.requires s) :
    Eval p.body s (p.run s hs).1 (p.run s hs).2 ∧
      p.ensures s (p.run s hs).2 ∧ (p.run s hs).1 ≤ p.budget s := by
  obtain ⟨k, t, hx, hQ, hk⟩ := p.verification s hs
  obtain ⟨u, hu, ht⟩ := hx.compile (encode s) (observe_encode s)
  simp only [Method.run, run_eq hu, ht]
  exact ⟨hx, hQ, hk⟩

/-- A contract always certifies actual RAM work, not just a source cost annotation. -/
theorem Contract.ram {c : Cmd} {P : Store → Prop} {Q : Store → Store → Prop}
    {budget : Store → Nat} (h : Contract c P Q budget) (s : State) (hs : P (observe s)) :
    ∃ k t, Exec c.compile s k t ∧ Q (observe s) (observe t) ∧ k ≤ budget (observe s) := by
  obtain ⟨k, t, hx, hQ, hk⟩ := h (observe s) hs
  obtain ⟨u, hu, ht⟩ := hx.compile s rfl
  exact ⟨k, u, hu, ht ▸ hQ, hk⟩

end AlgoLib.Experimental.RAM.Checked.Language
