/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalInterpretation
import AlgoLib.Experimental.RAM.Authoring.Syntax
import AlgoLib.Experimental.RAM.Authoring.Contracts

/-!
# Proof annotations and generated conditions

`Plan p` annotates an EXISTING program `p`; its index prevents verifying one body
and compiling another. Loops ask for user-supplied invariants over state and
remaining credits. Calls substitute reusable functional/cost contracts. The VCG
is justified directly by the Loom-style observation laws, not by a sorting theorem.

`reconstructAlgorithm` converts the annotated proof into pure Specification.VCs.
No model, compiler, memory representation, or instruction-cost conversion is needed.
LoomObservation connects this generator to the actual upstream algebra; the separate
Verification module is the compatibility adapter for backend-indexed methods.
The frontend supplies indexed plans for mutable code and nested loops. `atEntry`
automatically frames unchanged locals; assertions and variants remain checked
obligations. `LoomObservation` connects this generator to the upstream algebra.
-/
namespace AlgoLib.Experimental.RAM.Prototype
open Authoring

variable {State : Type}

/-- A modular procedure contract for an actual program body. Calls inline that body;
only verification uses the summary. The cost is an upper bound, not an oracle charge. -/
structure Routine (State : Type) where
  body : Program State
  requires : State → Prop
  ensures : State → State → Prop
  work : State → Nat
  verification : Correct body requires ensures work

/-- Proof-only annotations, indexed by the single supported program representation. -/
inductive Plan : Program State → Type where
  | skip : Plan .skip
  | call (routine : Routine State) : Plan routine.body
  | action (a : Action State) : Plan (.action a)
  | seq {a b : Program State} : Plan a → Plan b → Plan (.seq a b)
  | branch (q : Guard State) {a b : Program State} : Plan a → Plan b → Plan (.branch q a b)
  | loop (q : Guard State) {body : Program State} (invariant : State → Nat → Prop) :
      Plan body → Plan (.loop q body)
  | loopVariant (q : Guard State) {body : Program State} (invariant : State → Nat → Prop)
      (variant : State → Nat) : Plan body → Plan (.loop q body)
  | atEntry {p : Program State} : (State → Plan p) → Plan p
  | assert (assertion : State → Prop) : Plan .skip
  | ensure {p : Program State} (assertion : State → Prop) : Plan p → Plan p

/-- Generate purely mathematical obligations by structural symbolic execution. -/
def Plan.vc {p : Program State} : Plan p → (State → Nat → Prop) → State → Nat → Prop
  | .skip, Q, s, c => Q s c
  | .call routine, Q, s, c => routine.requires s ∧ routine.work s ≤ c ∧
      ∀ t k, routine.ensures s t → k ≤ routine.work s → Q t (c - k)
  | .action a, Q, s, c => a.requires s ∧ a.work s ≤ c ∧ Q (a.effect s) (c - a.work s)
  | .seq a b, Q, s, c => a.vc (b.vc Q) s c
  | .branch q a b, Q, s, c => 1 ≤ c ∧
      if q.test s then a.vc Q s (c - 1) else b.vc Q s (c - 1)
  | .loop q I body, Q, s, c => I s c ∧ ∀ t d, I t d → 1 ≤ d ∧
      if q.test t then body.vc I t (d - 1) else Q t (d - 1)
  | .loopVariant q I variant body, Q, s, c => I s c ∧ ∀ t d, I t d → 1 ≤ d ∧
      if q.test t then body.vc (fun u r => variant u < variant t ∧ I u r) t (d - 1)
      else Q t (d - 1)
  | .atEntry plan, Q, s, c => (plan s).vc Q s c
  | .assert assertion, Q, s, c => assertion s ∧ Q s c
  | .ensure assertion plan, Q, s, c => plan.vc (fun t r => assertion t ∧ Q t r) s c

/-- VCG soundness is proved through the independent costed observation. -/
theorem Plan.sound {p : Program State} (plan : Plan p) (Q : State → Nat → Prop)
    (s : State) (c : Nat) (h : plan.vc Q s c) : (denote p).wp (fun _ => Q) s c := by
  induction plan generalizing Q s c with
  | skip => exact (Computation.wp_pure () _ _ _).mpr h
  | «call» routine =>
    obtain ⟨k, t, run, post, cost⟩ := routine.verification s h.1
    exact ⟨k, t, (), run_denote run, cost.trans h.2.1, h.2.2 t k post cost⟩
  | action a => exact ⟨_, _, (), ⟨h.1, rfl, rfl⟩, h.2⟩
  | seq a b iha ihb =>
    apply (Computation.wp_bind _ _ _ _ _).mpr
    exact Computation.wp_mono (fun _ t d ht => ihb Q t d ht) (iha _ s c h)
  | branch q a b iha ihb =>
    obtain ⟨hc, hb⟩ := h
    cases hq : q.test s with
    | true =>
      obtain ⟨k, t, u, ht, hk, hQ⟩ := iha Q s (c - 1) (by simpa [hq] using hb)
      cases u
      exact ⟨1 + k, t, (), ⟨k, rfl, by simpa [hq] using ht⟩, by omega,
        by simpa [Nat.sub_sub] using hQ⟩
    | false =>
      obtain ⟨k, t, u, ht, hk, hQ⟩ := ihb Q s (c - 1) (by simpa [hq] using hb)
      cases u
      exact ⟨1 + k, t, (), ⟨k, rfl, by simpa [hq] using ht⟩, by omega,
        by simpa [Nat.sub_sub] using hQ⟩
  | loop q I body ih =>
    apply Computation.wp_loop q.test _ I _ _ s c h.1
    intro t d ht
    obtain ⟨hd, hn⟩ := h.2 t d ht
    refine ⟨hd, ?_⟩
    cases hq : q.test t with
    | true => simpa [hq] using ih I t (d - 1) (by simpa [hq] using hn)
    | false => simpa [hq] using hn
  | loopVariant q I variant body ih =>
    apply Computation.wp_loop q.test _ I _ _ s c h.1
    intro t d ht
    obtain ⟨hd, hn⟩ := h.2 t d ht
    refine ⟨hd, ?_⟩
    cases hq : q.test t with
    | true =>
      simp only [hq, ↓reduceIte] at hn ⊢
      exact Computation.wp_mono (fun _ _ _ hu => hu.2) (ih _ _ _ hn)
    | false => simpa [hq] using hn
  | atEntry plan ih => exact ih s Q s c h
  | assert assertion => exact (Computation.wp_pure () _ _ _).mpr h.2
  | ensure assertion plan ih => exact Computation.wp_mono (fun _ _ _ ht => ht.2) (ih _ _ _ h)

/-- One compositional program with annotations; both interpretations use `body`. -/
structure Annotated (State : Type) where
  body : Program State
  plan : Plan body

/-- Generate and solve a procedure's VCs once. Callers use only its contract. -/
def Annotated.verify (code : Annotated State) (requires : State → Prop)
    (ensures : State → State → Prop) (work : State → Nat)
    (proof : ∀ s, requires s → code.plan.vc (fun t _ => ensures s t) s (work s)) :
    Routine State where
  body := code.body
  requires := requires
  ensures := ensures
  work := work
  verification s hs := by
    obtain ⟨k, t, u, run, cost, post⟩ := code.plan.sound _ _ _ (proof s hs)
    cases u
    exact ⟨k, t, denote_run _ run, post, cost⟩

/-- Generated obligations for a complete backend-independent algorithm. -/
def AlgorithmObligations {Input Output : Type} (spec : Specification State Input Output)
    (plan : Input → Plan spec.body) : Prop :=
  ∀ i, spec.requires i → (plan i).vc
    (fun t _ => ∀ out, spec.observes t out → spec.ensures i out) (spec.initial i) (spec.credits i)

/-- Reuse the existing observation/VC soundness proofs; no new verification logic. -/
theorem reconstructAlgorithm {Input Output : Type} {spec : Specification State Input Output}
    {plan : Input → Plan spec.body} (proof : AlgorithmObligations spec plan) : spec.VCs := by
  intro i hi
  obtain ⟨k, t, u, ht, hk, hQ⟩ := (plan i).sound _ _ _ (proof i hi)
  cases u
  exact Run.vc _ (denote_run _ ht) _ _ hk hQ

end AlgoLib.Experimental.RAM.Prototype
