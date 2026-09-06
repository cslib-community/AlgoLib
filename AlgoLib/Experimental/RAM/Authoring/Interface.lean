/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Realization

/-!
# Certified input preparation and output observation

A library adapter relates ordinary inputs and output views to a logical model. Preparation is
executed and charged; the observation describes the returned result.

Concrete adapters are in Backend/Adapters and exposed by Library. Methods.lean packages this
interface with a displayed input/output contract and generated obligations.
-/
namespace AlgoLib.Experimental.RAM.Authoring
open Checked.Language

/-- A library supplies input preparation and output interpretation once. Input
preparation is compiled and charged; output observations are host-side views. -/
structure Interface {State : Type} (M : Model State) (Input Output : Type) where
  initial : Input → State
  encode : Input → Store
  prepare : Cmd
  preparationCost : Input → Nat
  preparation : ∀ i, ∃ k t, Eval prepare (encode i) k t ∧
    M.Represents (initial i) t ∧ k ≤ preparationCost i
  decode : Input → Store → Output
  Observes : State → Output → Prop
  output : ∀ i g s, M.Represents g s → Observes g (decode i s)

structure Result (Output : Type) where
  value : Output
  steps : Nat

/-- Compile, prove termination, run, and decode. No fuel or compilation proof
is an argument of the resulting executable. -/
def Interface.method {State Input Output : Type} {M : Model State}
    (api : Interface M Input Output) {p : Program State} [Compilation M p] {P : State → Prop}
    {Q : State → State → Prop} {budget : State → Nat}
    (proof : Correct p P Q budget) (input : Input) (valid : P (api.initial input)) : Method where
  body := .seq api.prepare (p.source M)
  requires s := s = api.encode input
  ensures _ t := ∃ b, Q (api.initial input) b ∧ M.Represents b t
  budget _ := api.preparationCost input + M.overhead * budget (api.initial input)
  verification s hs := by
    subst s
    obtain ⟨i, u, hu, hr, hi⟩ := api.preparation input
    obtain ⟨j, t, ht, hQ, hj⟩ := (proof.method _ valid).verification u hr
    refine ⟨i+j, t, .seq hu ht, hQ, ?_⟩
    change j ≤ M.overhead * budget (api.initial input) at hj
    dsimp only
    omega

def Interface.run {State Input Output : Type} {M : Model State}
    (api : Interface M Input Output) {p : Program State} [Compilation M p] {P : State → Prop}
    {Q : State → State → Prop} {budget : State → Nat}
    (proof : Correct p P Q budget) (input : Input) (valid : P (api.initial input)) :
    Result Output :=
  let r := (api.method proof input valid).run (api.encode input) rfl
  ⟨api.decode input r.2, r.1⟩

theorem Interface.correct {State Input Output : Type} {M : Model State}
    (api : Interface M Input Output) {p : Program State} [Compilation M p] {P : State → Prop}
    {Q : State → State → Prop} {budget : State → Nat}
    (proof : Correct p P Q budget) (input : Input) (valid : P (api.initial input)) :
    (∃ b, Q (api.initial input) b ∧ api.Observes b (api.run proof input valid).value) ∧
      (api.run proof input valid).steps ≤
        api.preparationCost input + M.overhead * budget (api.initial input) := by
  have h := (api.method proof input valid).correct (api.encode input) rfl
  obtain ⟨b, hb, hr⟩ := h.2.1
  exact ⟨⟨b, hb, api.output input b _ hr⟩, h.2.2⟩

end AlgoLib.Experimental.RAM.Authoring
