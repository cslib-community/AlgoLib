/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.LogicalFrontend
import AlgoLib.Experimental.RAM.Prototype.Composition.SignedArrays

/-!
# Assemble an executable and its correctness/cost theorem

A certified backend determines the machine model, representation and conversion rate.
`CertifiedExecutable.ofEncoded` packages those choices for any typed procedure.
The `compile_array_method` command selects resident Nat or Int arrays executed on Int-RAM:
it reconstructs local storage and linking, then emits a fuel-free ordinary-list runner,
an inferred bound, and their joint theorem. No simulation proof is requested from the
algorithm author. Array encoding and output observation remain host-side conventions.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

/-- A backend package retains its interpretation certificates, not an arbitrary runner.
Execution, the bound, and their theorem are derived definitions below. -/
structure CertifiedExecutable (proc : Procedure A B) where
  input : A → Representation A
  output : A → Representation B
  encoder : ∀ a, Encoder (input a)
  rate : Nat
  linked : ∀ a, Linked rate (input a) proc.body (output a)
  decoder : ∀ a, Decoder (output a)
  resident : ∀ a, proc.requires a → (encoder a).requires a
  codeIndependent : ∀ a b,
    (linked a).supported.compile.code = (linked b).supported.compile.code

/-- Generic assembly: logical proofs are unchanged when the verified backend changes. -/
def CertifiedExecutable.ofEncoded (proc : Procedure A B)
    (P : A → Representation A) (Q : A → Representation B)
    (encoder : ∀ a, Encoder (P a)) (rate : Nat)
    [linked : ∀ a, Linked rate (P a) proc.body (Q a)] [decoder : ∀ a, Decoder (Q a)]
    (resident : ∀ a, proc.requires a → (encoder a).requires a)
    (fixed : ∀ a b, (linked a).supported.compile.code = (linked b).supported.compile.code) :
    CertifiedExecutable proc :=
  ⟨P, Q, encoder, rate, linked, decoder, resident, fixed⟩

/-- Always execute the linked RAM code, with the existing proof-directed termination. -/
def CertifiedExecutable.run {proc : Procedure A B} (e : CertifiedExecutable proc)
    (a : A) (h : proc.requires a) :
    Result B :=
  letI := e.linked a
  letI := e.decoder a
  runEncoded (rate := e.rate) (Q := e.output a) proc (e.encoder a) a h (e.resident a h)

/-- The selected backend supplies the conversion rate and any initial private potential. -/
def CertifiedExecutable.bound {proc : Procedure A B} (e : CertifiedExecutable proc) (a : A) : Nat :=
  2 * (e.rate * proc.credits a + (e.encoder a).saved a)

/-- Functional correctness and the RAM bound refer to this exact executable. -/
theorem CertifiedExecutable.correct {proc : Procedure A B} (e : CertifiedExecutable proc)
    (a : A) (h : proc.requires a) :
    proc.ensures a (e.run a h).value ∧ (e.run a h).steps ≤ e.bound a := by
  letI := e.linked a
  letI := e.decoder a
  exact runEncoded_correct (rate := e.rate) (Q := e.output a)
    proc (e.encoder a) a h (e.resident a h)

open Lean Elab Command

private def arrayElementType (name : Ident) : CommandElabM Term :=
  Command.runTermElabM fun _ => do
    let value ← Term.elabTerm (← `($name)) none
    let ty ← Lean.Meta.whnf (← Lean.Meta.inferType value)
    unless ty.isAppOfArity ``Algorithm 2 do throwErrorAt name "Expected a RAM algorithm"
    let input ← Lean.Meta.whnf ty.getAppArgs[0]!
    unless input.isAppOfArity ``Array 1 do
      throwErrorAt name "compile_array_method expects one Array Nat or Array Int input"
    let element := input.getAppArgs[0]!
    unless element.isConstOf ``Int || element.isConstOf ``Nat do
      throwErrorAt name "Compiled array elements must be Nat or Int"
    if element.isConstOf ``Int then `(Int) else `(Nat)

/-- Reconstruct layout and code certificates from the body alone, before any algorithm proof. -/
def declareArrayBackend (name : Ident) : CommandElabM Unit := do
  let element ← arrayElementType name
  let signed := element.raw.getId.eraseMacroScopes == `Int
  let locals := mkIdent (name.getId.appendAfter "Locals")
  let stem := quote name.getId.toString
  let scratch := mkIdent (name.getId.appendAfter "Scratch")
  let layout := mkIdent (name.getId.appendAfter "Layout")
  let encoder := mkIdent (name.getId.appendAfter "Encoder")
  let linked := mkIdent (name.getId.appendAfter "Linked")
  let fixed := mkIdent (name.getId.appendAfter "CodeIndependent")
  let hasLocals := (← getEnv).contains ((← getCurrNamespace) ++ locals.getId) ||
    (← getEnv).contains locals.getId
  if hasLocals then
    elabCommand (← `(command| abbrev $scratch := local_storage% $stem:str : $locals))
  else
    elabCommand (← `(command| abbrev $scratch := ()))
  if signed then
    elabCommand (← `(command| abbrev $layout (n : Nat) : SignedArrays.Layout :=
      ⟨SignedStorageImpl.Layout.named $(quote (name.getId.toString ++ ".array")), 0, n⟩))
  else
    elabCommand (← `(command| abbrev $layout (n : Nat) : Storage.ArrayLayout :=
      ⟨⟨$(quote (name.getId.toString ++ ".array.size"))⟩, 0, n⟩))
  let encode := if signed then mkIdent ``SignedArrays.encoder else mkIdent ``arrayEncoder
  if hasLocals then
    elabCommand (← `(command| abbrev $encoder (n : Nat) :=
      ($encode ($layout n)).hide $scratch
        (by simp [$scratch:term, Encoder.sep, scalarEncoder, signedEncoder,
          SignedStorageImpl.encoder])
        (by simp [arrayEncoder, $layout:term, Storage.ArrayLayout.footprint, $scratch:term,
          Encoder.sep, scalarEncoder, signedEncoder, SignedStorageImpl.encoder,
          SignedStorageImpl.Layout.footprint, SignedArrays.encoder, SignedArrays.Layout.footprint,
          SignedStorageImpl.Layout.named, Fin.forall_fin_succ, Fin.exists_fin_succ,
          Finset.disjoint_left] <;> aesop)))
  else
    elabCommand (← `(command| abbrev $encoder (n : Nat) := $encode ($layout n)))
  elabCommand (← `(command| instance $linked:ident (n : Nat) :
    Linked 24 ($encoder n).representation ($name).body ($encoder n).representation := by
      ram_link))
  -- Comparing large reconstructed certificates is backend work, not a user proof setting.
  withScope (fun scope =>
      { scope with opts := scope.opts.set `maxHeartbeats (2000000 : Nat) }) do
    elabCommand (← `(command| theorem $fixed (m n : Nat) :
      ($linked m).supported.compile.code = ($linked n).supported.compile.code := by ram_code_eq))

/-- Place this command in a module importing the program specification, not its proofs. -/
syntax "compile_array_backend " ident : command
elab_rules : command
  | `(command| compile_array_backend $name:ident) => declareArrayBackend name

/-- Assemble the executable using an imported backend certificate when one is available. -/
syntax "compile_array_method " ident : command
elab_rules : command
  | `(command| compile_array_method $name:ident) => do
    let element ← arrayElementType name
    let linked := mkIdent (name.getId.appendAfter "Linked")
    unless (← getEnv).contains ((← getCurrNamespace) ++ linked.getId) ||
        (← getEnv).contains linked.getId do
      declareArrayBackend name
    let proc := mkIdent (name.getId.appendAfter "Procedure")
    let encoder := mkIdent (name.getId.appendAfter "Encoder")
    let layout := mkIdent (name.getId.appendAfter "Layout")
    let scratch := mkIdent (name.getId.appendAfter "Scratch")
    let run := mkIdent (name.getId.appendAfter "Run")
    let bound := mkIdent (name.getId.appendAfter "Bound")
    let correct := mkIdent (name.getId.appendAfter "Correct")
    elabCommand (← `(command| def $run (xs : List $element)
        (valid : ($proc).requires xs.toArray := by trivial) : Result (List $element) :=
      let r := runEncoded (rate := 24) (Q := ($encoder xs.length).representation)
        $proc ($encoder xs.length) xs.toArray valid
        (by simp [Encoder.hide, arrayEncoder, SignedArrays.encoder, $layout:term])
      ⟨r.value.toList, r.steps⟩))
    elabCommand (← `(command| def $bound (xs : List $element) : Nat :=
      2 * (24 * ($proc).credits xs.toArray)))
    elabCommand (← `(command| theorem $correct (xs : List $element)
        (valid : ($proc).requires xs.toArray) :
        ($proc).ensures xs.toArray (($run xs valid).value.toArray) ∧
          ($run xs valid).steps ≤ $bound xs := by
      have h := runEncoded_correct (rate := 24) (Q := ($encoder xs.length).representation)
        $proc ($encoder xs.length) xs.toArray valid
        (by simp [Encoder.hide, arrayEncoder, SignedArrays.encoder, $layout:term])
      simpa [$run:term, $bound:term, Encoder.hide, $encoder:term, $scratch:term, Encoder.sep,
        scalarEncoder, arrayEncoder, signedEncoder, SignedStorageImpl.encoder,
        SignedArrays.encoder] using h))

/-- Assemble a typed scalar method with private local storage and a fuel-free runner. -/
syntax "compile_scalar_method " ident : command
elab_rules : command
  | `(command| compile_scalar_method $name:ident) => do
    let proc := mkIdent (name.getId.appendAfter "Procedure")
    let locals := mkIdent (name.getId.appendAfter "Locals")
    let scratch := mkIdent (name.getId.appendAfter "Scratch")
    let encoder := mkIdent (name.getId.appendAfter "Encoder")
    let linked := mkIdent (name.getId.appendAfter "Linked")
    let run := mkIdent (name.getId.appendAfter "Run")
    let bound := mkIdent (name.getId.appendAfter "Bound")
    let correct := mkIdent (name.getId.appendAfter "Correct")
    let ty ← Command.runTermElabM fun _ => do
      let value ← Term.elabTerm (← `($name)) none
      let ty ← Lean.Meta.whnf (← Lean.Meta.inferType value)
      unless ty.isAppOfArity ``Algorithm 2 do throwErrorAt name "Expected a RAM algorithm"
      let input := ty.getAppArgs[0]!
      unless input.isConstOf ``Int || input.isConstOf ``Nat do
        throwErrorAt name "compile_scalar_method expects one Nat or Int input"
      if input.isConstOf ``Int then `(Int) else `(Nat)
    let input ← if ty.raw.isIdent && ty.raw.getId.eraseMacroScopes == `Nat then
        `(scalarEncoder ⟨$(quote (name.getId.toString ++ ".input"))⟩)
      else `(signedEncoder $(quote (name.getId.toString ++ ".input")))
    let hasLocals := (← getEnv).contains ((← getCurrNamespace) ++ locals.getId) ||
      (← getEnv).contains locals.getId
    if hasLocals then
      elabCommand (← `(command| abbrev $scratch :=
        local_storage% $(quote (name.getId.toString ++ ".locals")):str : $locals))
      elabCommand (← `(command| abbrev $encoder := ($input).hide $scratch
        (by simp [$scratch:term, Encoder.sep, scalarEncoder, signedEncoder,
          SignedStorageImpl.encoder])
        (by decide)))
    else
      elabCommand (← `(command| abbrev $encoder := $input))
    elabCommand (← `(command| instance $linked:ident :
      Linked 24 ($encoder).representation ($name).body ($encoder).representation := by ram_link))
    elabCommand (← `(command| def $run (x : $ty)
        (valid : ($proc).requires x := by trivial) : Result $ty :=
      runEncoded (rate := 24) (Q := ($encoder).representation) $proc $encoder x valid (by trivial)))
    elabCommand (← `(command| def $bound (x : $ty) : Nat :=
      2 * (24 * ($proc).credits x + ($encoder).saved x)))
    elabCommand (← `(command| theorem $correct (x : $ty) (valid : ($proc).requires x) :
        ($proc).ensures x ($run x valid).value ∧ ($run x valid).steps ≤ $bound x :=
      runEncoded_correct (rate := 24) (Q := ($encoder).representation)
        $proc $encoder x valid (by trivial)))

/-- Beginner entry point: prove the algorithm and assemble its standard list executable. -/
syntax "verify_array_method " ident " by " tacticSeq : command
elab_rules : command
  | `(command| verify_array_method $name:ident by $proof:tacticSeq) => do
    elabCommand (← `(command| prove_algorithm $name by $proof))
    elabCommand (← `(command| compile_array_method $name))

open AlgoLib.Experimental.RAM.Prototype.Frontend

/-- Named proof blocks also support the single-command teaching interface. -/
syntax "verify_array_method " ident " where " namedProofBlock* : command
elab_rules : command
  | `(command| verify_array_method $name:ident where $blocks:namedProofBlock*) => do
    elabCommand (← `(command| prove_algorithm $name where $blocks*))
    elabCommand (← `(command| compile_array_method $name))

end AlgoLib.Experimental.RAM.Prototype.Composition
