/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Mathlib.Tactic

/-!
# Authoring semantics and proof rules

Defines the logical states and independent costed execution used by algorithm proofs.
Actions contain only preconditions, mathematical effects, and logical credit charges.
This module imports no RAM machine or compiler. Programs and their proofs can be
realized by different backends without changing the algorithm.

Read Program, Run, VC, and LoopProof for the proof API. Backend/Realization supplies
separate implementation certificates and compositional compilation.

## Further details

# Mathematical programs with certified implementations

Algorithm authors reason about `State`, never the compiler's store. An operation
has a mathematical effect and a cost contract. Its implementation proof belongs
to the library. Every control-flow construct compiles compositionally.
-/
namespace AlgoLib.Experimental.RAM.Authoring

/-- A backend-independent functional contract and logical credit charge. -/
structure Action (State : Type) where
  requires : State → Prop
  effect : State → State
  /-- Logical credit allowance, independent of any instruction count. -/
  work : State → Nat

/-- Tests consume one logical credit; a backend must implement and pay for them. -/
structure Guard (State : Type) where
  test : State → Bool

inductive Program (State : Type) where
  | skip
  | action (a : Action State)
  | seq (a b : Program State)
  | branch (q : Guard State) (a b : Program State)
  | loop (q : Guard State) (body : Program State)

/-- Independent mathematical semantics. Ghost state is not executed by Lean
at runtime; only the certified implementation is compiled and run. -/
inductive Run {State : Type} : Program State → State → Nat → State → Prop where
  | skip (s) : Run .skip s 0 s
  | action (a : Action State) (s) : a.requires s → Run (.action a) s (a.work s) (a.effect s)
  | seq {a b s u t i j} : Run a s i u → Run b u j t → Run (.seq a b) s (i+j) t
  | ifTrue {q a b s t k} : q.test s = true → Run a s k t → Run (.branch q a b) s (1+k) t
  | ifFalse {q a b s t k} : q.test s = false → Run b s k t → Run (.branch q a b) s (1+k) t
  | whileFalse {q b s} : q.test s = false → Run (.loop q b) s 1 s
  | whileTrue {q b s u t i j} : q.test s = true → Run b s i u →
      Run (.loop q b) u j t → Run (.loop q b) s (1+i+j) t

def Correct {State : Type} (p : Program State)
    (P : State → Prop) (Q : State → State → Prop) (budget : State → Nat) : Prop :=
  ∀ a, P a → ∃ k b, Run p a k b ∧ Q a b ∧ k ≤ budget a

/-- Symbolic execution substitutes only mathematical effects. A loop asks for
an invariant over mathematical state and remaining credits. -/
def VC {State : Type} : Program State → (State → Nat → Prop) → State → Nat → Prop
  | .skip, Q, s, c => Q s c
  | .action a, Q, s, c => a.requires s ∧ a.work s ≤ c ∧ Q (a.effect s) (c - a.work s)
  | .seq a b, Q, s, c => VC a (VC b Q) s c
  | .branch q a b, Q, s, c => 1 ≤ c ∧
      if q.test s then VC a Q s (c-1) else VC b Q s (c-1)
  | .loop q b, Q, s, c => ∃ I : State → Nat → Prop, I s c ∧
      ∀ t d, I t d → 1 ≤ d ∧ if q.test t then VC b I t (d-1) else Q t (d-1)

theorem VC.sound {State : Type} (p : Program State)
    (Q : State → Nat → Prop) (s : State) (c : Nat) (h : VC p Q s c) :
    ∃ k t, Run p s k t ∧ k ≤ c ∧ Q t (c-k) := by
  induction p generalizing Q s c with
  | skip => exact ⟨0, s, .skip s, by omega, by simpa [VC] using h⟩
  | action a => exact ⟨_, _, .action a s h.1, h.2.1, h.2.2⟩
  | seq a b iha ihb =>
    obtain ⟨i, u, hu, hi, hI⟩ := iha _ _ _ h
    obtain ⟨j, t, ht, hj, hQ⟩ := ihb _ _ _ hI
    exact ⟨_, t, .seq hu ht, by omega, by simpa [Nat.sub_sub] using hQ⟩
  | branch q a b iha ihb =>
    obtain ⟨hc, h⟩ := h
    cases hq : q.test s with
    | false =>
      obtain ⟨k, t, hx, hk, ht⟩ := ihb Q s (c-1) (by simpa [hq] using h)
      exact ⟨_, t, .ifFalse hq hx, by omega, by simpa [Nat.sub_sub, Nat.add_comm] using ht⟩
    | true =>
      obtain ⟨k, t, hx, hk, ht⟩ := iha Q s (c-1) (by simpa [hq] using h)
      exact ⟨_, t, .ifTrue hq hx, by omega, by simpa [Nat.sub_sub, Nat.add_comm] using ht⟩
  | loop q b ihb =>
    obtain ⟨I, hinit, hstep⟩ := h
    have go : ∀ c a, I a c → ∃ k z, Run (.loop q b) a k z ∧ k ≤ c ∧ Q z (c-k) := by
      intro c
      induction c using Nat.strongRecOn with
      | ind c ih =>
        intro a ha
        obtain ⟨hc, hn⟩ := hstep a c ha
        cases hq : q.test a with
        | false => exact ⟨_, a, .whileFalse hq, hc, by simpa [hq] using hn⟩
        | true =>
          obtain ⟨i, u, hu, hi, hI⟩ := ihb I a (c-1) (by simpa [hq] using hn)
          obtain ⟨j, z, hz, hj, hQ⟩ := ih (c-1-i) (by omega) u hI
          exact ⟨_, z, .whileTrue hq hu hz, by omega,
            by simpa [Nat.sub_sub, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hQ⟩
    exact go c s hinit

theorem VC.correct {State : Type} {p : Program State}
    {P : State → Prop} {Q : State → State → Prop} {budget : State → Nat}
    (h : ∀ a, P a → VC p (fun b _ => Q a b) a (budget a)) : Correct p P Q budget := by
  intro a ha
  obtain ⟨k, b, hb, hk, hQ⟩ := VC.sound _ _ _ _ (h a ha)
  exact ⟨k, b, hb, hQ, hk⟩

/-- Authoring loop proof: preservation and payment share the same post-state.
The guard's positive cost turns the credit argument into termination. -/
structure LoopProof {State : Type} (q : Guard State) (body : Program State)
    (invariant : State → Prop) (potential : State → Nat) (post : State → Prop) : Prop where
  preservation : ∀ s, invariant s → q.test s = true →
    VC body (fun t remaining => invariant t ∧ potential t ≤ remaining) s (potential s - 1)
  payment : ∀ s, invariant s → q.test s = true → 1 ≤ potential s
  exit : ∀ s, invariant s → q.test s = false → post s

theorem LoopProof.correct {State : Type} {q : Guard State} {body : Program State}
    {I Q : State → Prop} {potential : State → Nat} (h : LoopProof q body I potential Q) :
    Correct (.loop q body) I (fun _ t => Q t) (fun s => potential s + 1) := by
  intro s hs
  change ∃ k t, Run (.loop q body) s k t ∧ Q t ∧ k ≤ potential s + 1
  generalize hn : potential s = n
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    cases hq : q.test s with
    | false => exact ⟨1, s, .whileFalse hq, h.exit s hs hq, by omega⟩
    | true =>
      obtain ⟨i, u, hu, hi, hI, hp⟩ := VC.sound _ _ _ _ (h.preservation s hs hq)
      have hpos := h.payment s hs hq
      obtain ⟨j, t, ht, hQ, hj⟩ := ih (potential u) (by omega) u hI rfl
      exact ⟨_, t, .whileTrue hq hu ht, hQ, by omega⟩

/-- Procedures are verified once and used through a functional/cost contract.
`call` hides their body from symbolic execution, but not from the compiler. -/
structure Procedure (State : Type) where
  body : Program State
  requires : State → Prop
  effect : State → State
  /-- Logical credit allowance, independent of any instruction count. -/
  work : State → Nat
  verification : Correct body requires (fun s t => t = effect s) work

def Procedure.call {State : Type} (p : Procedure State) : Action State where
  requires := p.requires
  effect := p.effect
  work := p.work
/-- Ghost assertions about untouched logical fields are framed by substitution;
no address-level frame obligation reaches an algorithm author. -/
theorem Action.frame {State : Type} (a : Action State)
    (F : State → Prop) (preserved : ∀ s, a.requires s → F s → F (a.effect s))
    (s : State) (hs : a.requires s) (hf : F s) :
    VC (.action a) (fun t _ => F t) s (a.work s) :=
  ⟨hs, Nat.le_refl _, preserved s hs hf⟩

end AlgoLib.Experimental.RAM.Authoring
