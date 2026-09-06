/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Interpretation
import AlgoLib.Experimental.RAM.Authoring.Methods

/-!
# Proof annotations and generated conditions

`Plan p` annotates an EXISTING program `p`; its index prevents verifying one body
and compiling another. Loops ask for user-supplied invariants over state and
remaining credits. Calls substitute reusable functional/cost contracts. The VCG
is justified directly by the Loom-style observation laws, not by a sorting theorem.

`certify` reconstructs the existing backend certificate automatically from this
observation proof. This preserves the existing executable runner and axiom boundary.
No SMT answers, native decision axioms, compiler obligations, or fuel reach the user.
The frontend supplies indexed plans for mutable code and nested loops. `atEntry`
automatically frames unchanged locals; assertions and variants remain checked
obligations. `LoomObservation` connects this generator to the upstream algebra.
-/
namespace AlgoLib.Experimental.RAM.Prototype
open Authoring

variable {State Input Output : Type} {M : Model State}

/-- A modular procedure contract for an actual program body. Calls inline that body;
only verification uses the summary. The cost is an upper bound, not an oracle charge. -/
structure Routine (M : Model State) where
  body : Program M
  requires : State → Prop
  ensures : State → State → Prop
  work : State → Nat
  verification : Correct body requires ensures work

/-- Proof-only annotations, indexed by the single supported program representation. -/
inductive Plan : Program M → Type where
  | skip : Plan .skip
  | call (routine : Routine M) : Plan routine.body
  | action (a : Action M) : Plan (.action a)
  | seq {a b : Program M} : Plan a → Plan b → Plan (.seq a b)
  | branch (q : Guard M) {a b : Program M} : Plan a → Plan b → Plan (.branch q a b)
  | loop (q : Guard M) {body : Program M} (invariant : State → Nat → Prop) :
      Plan body → Plan (.loop q body)
  | loopVariant (q : Guard M) {body : Program M} (invariant : State → Nat → Prop)
      (variant : State → Nat) : Plan body → Plan (.loop q body)
  | atEntry {p : Program M} : (State → Plan p) → Plan p
  | assert (assertion : State → Prop) : Plan .skip
  | ensure {p : Program M} (assertion : State → Prop) : Plan p → Plan p

/-- Generate purely mathematical obligations by structural symbolic execution. -/
def Plan.vc {p : Program M} : Plan p → (State → Nat → Prop) → State → Nat → Prop
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
theorem Plan.sound {p : Program M} (plan : Plan p) (Q : State → Nat → Prop)
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
structure Annotated (M : Model State) where
  body : Program M
  plan : Plan body

/-- Generate and solve a procedure's VCs once. Callers use only its contract. -/
def Annotated.verify (code : Annotated M) (requires : State → Prop)
    (ensures : State → State → Prop) (work : State → Nat)
    (proof : ∀ s, requires s → code.plan.vc (fun t _ => ensures s t) s (work s)) :
    Routine M where
  body := code.body
  requires := requires
  ensures := ensures
  work := work
  verification s hs := by
    obtain ⟨k, t, u, run, cost, post⟩ := code.plan.sound _ _ _ (proof s hs)
    cases u
    exact ⟨k, t, denote_run _ run, post, cost⟩

/-- Input/output and time obligations, with proof annotations separate from runtime input. -/
def Obligations {api : Interface M Input Output} (method : Method api)
    (plan : Input → Plan method.body) : Prop :=
  ∀ i, method.requires i →
    (plan i).vc (fun t _ => ∀ out, api.Observes t out → method.ensures i out)
      (api.initial i) (method.credits i) ∧
    api.preparationCost i + M.overhead * method.credits i ≤ method.time i

/-- Reconstruct a backend certificate, entirely inside Lean's kernel. -/
theorem reconstruct {api : Interface M Input Output} {method : Method api}
    {plan : Input → Plan method.body} (proof : Obligations method plan) : method.VCs := by
  intro i hi
  obtain ⟨hp, hc⟩ := proof i hi
  obtain ⟨k, t, u, ht, hk, hQ⟩ := (plan i).sound _ _ _ hp
  cases u
  exact ⟨Run.vc _ (denote_run _ ht) _ _ hk hQ, hc⟩

/-- The executable is the existing verified RAM runner, not a host list implementation. -/
def certify {api : Interface M Input Output} (method : Method api)
    {plan : Input → Plan method.body} (proof : Obligations method plan) : VerifiedMethod api :=
  ⟨method, reconstruct proof⟩

/-- Proof annotations cannot change the compiled body. -/
theorem certify_body {api : Interface M Input Output} (method : Method api)
    {plan : Input → Plan method.body} (proof : Obligations method plan) :
    (certify method proof).method.body = method.body := rfl

/-- Substitute logical contracts and propagate credits, leaving invariants to the user. -/
macro "prototype_steps" " [" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [Plan.vc, paper_simps, $ds,*] at *)

end AlgoLib.Experimental.RAM.Prototype
