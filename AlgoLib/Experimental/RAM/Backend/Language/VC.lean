/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Verification

/-!
# Typed verification conditions

Generates obligations for the lower typed language and connects them to its independent costed
semantics.

This layer supports implementation authors. Algorithm-level logical VCs live in
Authoring/Semantics and are exposed by method_vc and paper_steps.

## Further details

# Compositional verification-condition generation

`VC` computes substitutions and payments for every source construct. At a loop,
the user supplies an invariant over the store and remaining credits. The three
obligations are initialization, preservation/payment, and exit. Credits also
prove termination; the runner never takes a fuel argument.
-/
namespace AlgoLib.Experimental.RAM.Checked.Language

def VC : Cmd → (Store → Nat → Prop) → Store → Nat → Prop
  | .skip, Q, s, credits => Q s credits
  | .assign v e, Q, s, credits => e.cost + 1 ≤ credits ∧
      Q (s.set v (e.eval s)) (credits - (e.cost + 1))
  | .write a v, Q, s, credits => a.cost + v.cost + 1 ≤ credits ∧
      Q (s.write (a.eval s) (v.eval s)) (credits - (a.cost + v.cost + 1))
  | @Cmd.localVar ty v e b, Q, s, credits => e.cost + 3 ≤ credits ∧
      VC b (fun t remaining => Q (t.set v (s.vars ty v.name)) remaining)
        (s.set v (e.eval s)) (credits - (e.cost + 3))
  | .seq a b, Q, s, credits => VC a (VC b Q) s credits
  | .branch q a b, Q, s, credits => q.cost ≤ credits ∧
      if q.eval s then VC a Q s (credits - q.cost) else VC b Q s (credits - q.cost)
  | .loop q b, Q, s, credits => ∃ I : Store → Nat → Prop, I s credits ∧
      ∀ t remaining, I t remaining → q.cost ≤ remaining ∧
        if q.eval t then VC b I t (remaining - q.cost) else Q t (remaining - q.cost)

/-- Generated obligations imply source termination, functional correctness,
and the cost bound. This theorem is generic over all programs. -/
theorem VC.sound (c : Cmd) (Q : Store → Nat → Prop) : Triple c (VC c Q) Q := by
  induction c generalizing Q with
  | skip => intro s credits h; exact ⟨0, s, .skip s, by omega, by simpa using h⟩
  | assign v e => exact Triple.assign v e Q
  | write a v => exact Triple.write a v Q
  | seq a b iha ihb => exact Triple.seq (iha (VC b Q)) (ihb Q)
  | branch q a b iha ihb =>
    intro s credits ⟨hc, h⟩
    cases hq : q.eval s with
    | false =>
      obtain ⟨k, t, hx, hk, ht⟩ := ihb Q s (credits - q.cost) (by simpa [hq] using h)
      exact ⟨_, t, .ifFalse hq hx, by omega, by simpa [Nat.sub_sub] using ht⟩
    | true =>
      obtain ⟨k, t, hx, hk, ht⟩ := iha Q s (credits - q.cost) (by simpa [hq] using h)
      exact ⟨_, t, .ifTrue hq hx, by omega, by simpa [Nat.sub_sub] using ht⟩
  | localVar v e b ih =>
    intro s credits ⟨hc, h⟩
    obtain ⟨k, t, hx, hk, ht⟩ := ih _ _ _ h
    exact ⟨_, _, .localVar hx, by omega, by simpa [Nat.sub_sub] using ht⟩
  | loop q b ihb =>
    intro s credits ⟨I, hinit, hstep⟩
    have go : ∀ n t, I t n → ∃ k u, Eval (.loop q b) t k u ∧ k ≤ n ∧ Q u (n - k) := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro t ht
        obtain ⟨hc, hnext⟩ := hstep t n ht
        cases hq : q.eval t with
        | false => exact ⟨_, t, .whileFalse hq, hc, by simpa [hq] using hnext⟩
        | true =>
          obtain ⟨i, u, hu, hi, hI⟩ := ihb I t (n - q.cost) (by simpa [hq] using hnext)
          have hpos := q.cost_pos
          obtain ⟨j, v, hv, hj, hQ⟩ := ih (n - q.cost - i) (by omega) u hI
          refine ⟨_, v, .whileTrue hq hu hv, by omega, ?_⟩
          simpa [Nat.sub_sub, Nat.add_assoc] using hQ
    exact go credits s hinit

/-- Turn a generated VC proof into a reusable method contract. -/
theorem VC.contract (c : Cmd) (P : Store → Prop) (Q : Store → Store → Prop)
    (budget : Store → Nat)
    (h : ∀ s, P s → VC c (fun t _ => Q s t) s (budget s)) : Contract c P Q budget := by
  intro s hs
  obtain ⟨k, t, hx, hk, ht⟩ := VC.sound c (fun t _ => Q s t) s (budget s) (h s hs)
  exact ⟨k, t, hx, ht, hk⟩

/-- Existing semantic contracts can discharge the same generated VCs. Loop
invariants may describe remaining certified executions. This proof rule lets
instruction-level invariant certificates be reused without an alternate runner. -/
theorem VC.complete (c : Cmd) {s t : Store} {k : Nat} (hx : Eval c s k t)
    (Q : Store → Nat → Prop) (credits : Nat) (hk : k ≤ credits) (hQ : Q t (credits - k)) :
    VC c Q s credits := by
  induction c generalizing s t k Q credits with
  | skip => cases hx; simpa [VC] using hQ
  | assign v e => cases hx; exact ⟨hk, hQ⟩
  | write a v => cases hx; exact ⟨hk, hQ⟩
  | seq a b iha ihb =>
    cases hx with
    | @seq _ _ _ u _ i j ha hb =>
      exact iha ha (VC b Q) credits (by omega)
        (ihb hb Q (credits - i) (by omega) (by simpa [Nat.sub_sub] using hQ))
  | branch q a b iha ihb =>
    cases hx with
    | ifTrue hq ha =>
      refine ⟨by omega, ?_⟩
      simpa [hq] using iha ha Q (credits - q.cost) (by omega)
        (by simpa [Nat.sub_sub] using hQ)
    | ifFalse hq hb =>
      refine ⟨by omega, ?_⟩
      simpa [hq] using ihb hb Q (credits - q.cost) (by omega)
        (by simpa [Nat.sub_sub] using hQ)
  | localVar v e b ih =>
    cases hx with
    | localVar hb =>
      refine ⟨by omega, ?_⟩
      exact ih hb _ (credits - (e.cost + 3)) (by omega)
        (by simpa [Nat.sub_sub] using hQ)
  | loop q b ih =>
    refine ⟨fun u remaining => ∃ j v, Eval (.loop q b) u j v ∧
      j ≤ remaining ∧ Q v (remaining - j), ⟨k, t, hx, hk, hQ⟩, ?_⟩
    rintro u remaining ⟨j, v, hrun, hj, hv⟩
    cases hrun with
    | whileFalse hq => exact ⟨hj, by simpa [hq] using hv⟩
    | @whileTrue _ _ _ w _ a bcost hq ha hb =>
      refine ⟨by omega, ?_⟩
      simp only [hq, if_true]
      apply ih ha _ (remaining - q.cost) (by omega)
      refine ⟨bcost, v, hb, by omega, ?_⟩
      simpa [Nat.sub_sub, Nat.add_assoc] using hv

/-- A source contract and the generated total-correctness VCs are equivalent. -/
theorem Contract.vc {c : Cmd} {P : Store → Prop} {Q : Store → Store → Prop}
    {budget : Store → Nat} (h : Contract c P Q budget) (s : Store) (hs : P s) :
    VC c (fun t _ => Q s t) s (budget s) := by
  obtain ⟨k, t, hx, ht, hk⟩ := h s hs
  exact VC.complete c hx _ _ hk ht

end AlgoLib.Experimental.RAM.Checked.Language
