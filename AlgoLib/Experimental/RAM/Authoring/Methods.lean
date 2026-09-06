/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Interface
import AlgoLib.Experimental.RAM.Authoring.Syntax
import AlgoLib.Experimental.RAM.Authoring.Contracts

/-!
# Procedures with explicit input, output, and logical credit contracts

Algorithm authors declare one fixed `body`, logical `requires`/`ensures`, an
abstract credit allowance. `Method.VCs` generates functional and logical credit
obligations. The selected backend derives the compiled-step bound.
A `VerifiedMethod` packages their proof;
its `run` executes the certified body through the existing input/output adapter.

The body is deliberately independent of the input value: the header cannot
perform the algorithm during compilation. Encoding, preparation, observation,
and compiler transport remain responsibilities of the chosen library adapter.
-/
namespace AlgoLib.Experimental.RAM.Authoring

/-- Reuse a logical loop/body contract. Only its initial condition, output
meaning, and sufficient credits remain; no machine state is exposed. -/
theorem Correct.output_vc {State Input Output : Type} {M : Model State}
    {api : Interface M Input Output} {p : Program State} {P : State → Prop}
    {Q : State → State → Prop} {work : State → Nat}
    (proof : Correct p P Q work) (input : Input) (post : Output → Prop) (credits : Nat)
    (initially : P (api.initial input)) (enough : work (api.initial input) ≤ credits)
    (result : ∀ t, Q (api.initial input) t → ∀ out, api.Observes t out → post out) :
    VC p (fun t _ => ∀ out, api.Observes t out → post out) (api.initial input) credits := by
  obtain ⟨k, t, run, hQ, hk⟩ := proof _ initially
  exact Run.vc p run _ _ (hk.trans enough) (result t hQ)

/-- A displayed procedure contract and one fixed high-level program body. -/
structure Method {State Input Output : Type} {M : Model State}
    (api : Interface M Input Output) where
  body : Program State
  requires : Input → Prop
  ensures : Input → Output → Prop
  credits : Input → Nat

/-- Generated obligations: symbolic correctness within the declared logical credits. -/
def Method.VCs {State Input Output : Type} {M : Model State}
    {api : Interface M Input Output} (method : Method api) : Prop :=
  ∀ i, method.requires i →
    VC method.body (fun t _ => ∀ out, api.Observes t out → method.ensures i out)
      (api.initial i) (method.credits i)

/-- Forget the execution backend: retain only the complete logical algorithm. -/
def Method.specification {State Input Output : Type} {M : Model State}
    {api : Interface M Input Output} (method : Method api) : Specification State Input Output where
  body := method.body
  initial := api.initial
  observes := api.Observes
  requires := method.requires
  ensures := method.ensures
  credits := method.credits

/-- The backend derives a RAM upper bound from logical credits and input preparation. -/
def Method.time {State Input Output : Type} {M : Model State}
    {api : Interface M Input Output} (method : Method api) (i : Input) : Nat :=
  api.preparationCost i + M.overhead * method.credits i

/-- A method cannot run until its generated verification conditions are proved. -/
structure VerifiedMethod {State Input Output : Type} {M : Model State}
    (api : Interface M Input Output) where
  method : Method api
  verification : method.VCs
  compilation : Compilation M method.body

/-- Supply only the logical proof. Backend certificates are assembled automatically. -/
def Method.certify {State Input Output : Type} {M : Model State}
    {api : Interface M Input Output} (method : Method api) (proof : method.VCs)
    (supported : Supported M method.body := by ram_supported) : VerifiedMethod api :=
  ⟨method, proof, supported.compile⟩

/-- Attach any implementation of the same input/output view to one logical proof.
The source program, specification, and proof are supplied unchanged. -/
def Interface.realize {State Input Output : Type} {M : Model State}
    (api : Interface M Input Output) (spec : Specification State Input Output)
    (proof : spec.VCs)
    (initial : api.initial = spec.initial := by rfl)
    (observes : api.Observes = spec.observes := by rfl)
    (supported : Supported M spec.body := by ram_supported) : VerifiedMethod api :=
  { method := ⟨spec.body, spec.requires, spec.ensures, spec.credits⟩
    compilation := supported.compile
    verification := by
      intro i hi
      simpa only [initial, observes] using proof i hi }

private theorem VerifiedMethod.body_correct {State Input Output : Type} {M : Model State}
    {api : Interface M Input Output} (p : VerifiedMethod api) (i : Input)
    (valid : p.method.requires i) :
    Correct p.method.body (fun s => s = api.initial i)
      (fun _ t => ∀ out, api.Observes t out → p.method.ensures i out)
      (fun _ => p.method.credits i) := by
  apply VC.correct
  intro s hs
  subst s
  exact p.verification i valid

/-- Fuel-free execution of the body displayed in the method declaration. -/
def VerifiedMethod.run {State Input Output : Type} {M : Model State}
    {api : Interface M Input Output} (p : VerifiedMethod api) (i : Input)
    (valid : p.method.requires i) : Result Output :=
  letI := p.compilation
  api.run (p.body_correct i valid) i rfl

/-- The public result: the declared output property and the inferred RAM bound
hold for the same run. Initialization is included in the bound. -/
theorem VerifiedMethod.correct {State Input Output : Type} {M : Model State}
    {api : Interface M Input Output} (p : VerifiedMethod api) (i : Input)
    (valid : p.method.requires i) :
    p.method.ensures i (p.run i valid).value ∧ (p.run i valid).steps ≤ p.method.time i := by
  letI := p.compilation
  obtain ⟨⟨t, ht, ho⟩, hk⟩ := api.correct (p.body_correct i valid) i rfl
  exact ⟨ht _ ho, hk⟩

/-- Declaring an input/output contract never turns its input into a code generator.
The input and output binders scope only over contracts and budgets. -/
macro "ram_method" "(" input:ident " : " inputType:term ")"
    "returns" "(" output:ident " : " outputType:term ")"
    "using" api:term ";"
    &"requires" pre:term ";" &"ensures" post:term ";"
    &"credits" credits:term ";"
    "do" "{" body:mathStmt* "}" : term =>
  `(({ body := paper { $body* }
       requires := fun ($input : $inputType) => $pre
       ensures := fun ($input : $inputType) ($output : $outputType) => $post
       credits := fun ($input : $inputType) => $credits } : Method $api))

/-- Library adapters register logical observation and accounting equations here.
Algorithm authors never unfold the adapter's implementation. -/
register_simp_attr method_simps

/-- Open the input/output and logical credit obligations of the declared method.
The remaining goals concern logical state and credit accounting only. -/
macro "method_vc" " [" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [Method.VCs, $ds,*])

/-- Reduce only registered logical adapter equations, then solve a routine
payment inequality. No compiler or memory definition is unfolded by the client. -/
macro "method_time" : tactic =>
  `(tactic| (simp only [method_simps]; first | omega | nlinarith))

end AlgoLib.Experimental.RAM.Authoring
