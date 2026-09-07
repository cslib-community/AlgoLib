/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Language.Frontend
import AlgoLib.Experimental.RAM.Compiler.Assembly.Tactics
import AlgoLib.Experimental.RAM.Compiler.Assembly.Native.Execution

/-!
# Assemble an executable and its correctness/cost theorem

Native storage and linking supply the representation and conversion certificates.
Shared tactics reconstruct evidence without importing compatibility implementations.
The `compile_array_method` command selects resident Nat or Int arrays executed on Int-RAM:
it reconstructs local storage and linking, then emits a fuel-free ordinary-list runner,
an inferred bound, and their joint theorem. No simulation proof is requested from the
algorithm author. Array encoding and output observation remain host-side conventions.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

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
    elabCommand (← `(command| abbrev $scratch := native_local_storage% $stem:str : $locals))
  else
    elabCommand (← `(command| abbrev $scratch := ()))
  elabCommand (← `(command| abbrev $layout (n : Nat) : Native.ArrayLayout :=
    ⟨⟨$(quote (name.getId.toString ++ ".array.size"))⟩, 0, n⟩))
  let encode ← if signed then `(id) else `(Int.ofNat)
  if hasLocals then
    elabCommand (← `(command| abbrev $encoder (n : Nat) :=
      (Native.arrayEncoder $encode ($layout n)).hide $scratch
        (by simp [$scratch:term, Native.Encoder.sep, Native.naturalEncoder, Native.signedEncoder])
        (by simp [Native.arrayEncoder, $layout:term, Native.ArrayLayout.footprint, $scratch:term,
          Native.Encoder.sep, Native.naturalEncoder, Native.signedEncoder,
          Finset.disjoint_left] <;> aesop)))
  else
    elabCommand (← `(command| abbrev $encoder (n : Nat) :=
      Native.arrayEncoder $encode ($layout n)))
  elabCommand (← `(command| instance $linked:ident (n : Nat) :
    Native.Linked 24 ($encoder n).representation ($name).body ($encoder n).representation := by
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
      let r := Native.runEncoded (rate := 24) (Q := ($encoder xs.length).representation)
        $proc ($encoder xs.length) xs.toArray valid
        (by simp [Native.Encoder.hide, Native.arrayEncoder, $layout:term])
      ⟨r.value.toList, r.steps⟩))
    elabCommand (← `(command| def $bound (xs : List $element) : Nat :=
      2 * (24 * ($proc).credits xs.toArray)))
    elabCommand (← `(command| theorem $correct (xs : List $element)
        (valid : ($proc).requires xs.toArray) :
        ($proc).ensures xs.toArray (($run xs valid).value.toArray) ∧
          ($run xs valid).steps ≤ $bound xs := by
      have h := Native.runEncoded_correct (rate := 24) (Q := ($encoder xs.length).representation)
        $proc ($encoder xs.length) xs.toArray valid
        (by simp [Native.Encoder.hide, Native.arrayEncoder, $layout:term])
      simpa [$run:term, $bound:term, Native.Encoder.hide, $encoder:term, $scratch:term, Native.Encoder.sep,
        Native.naturalEncoder, Native.arrayEncoder, Native.signedEncoder] using h))

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
        `(Native.naturalEncoder ⟨$(quote (name.getId.toString ++ ".input"))⟩)
      else `(Native.signedEncoder ⟨$(quote (name.getId.toString ++ ".input"))⟩)
    let hasLocals := (← getEnv).contains ((← getCurrNamespace) ++ locals.getId) ||
      (← getEnv).contains locals.getId
    if hasLocals then
      elabCommand (← `(command| abbrev $scratch :=
        native_local_storage% $(quote (name.getId.toString ++ ".locals")):str : $locals))
      elabCommand (← `(command| abbrev $encoder := ($input).hide $scratch
        (by simp [$scratch:term, Native.Encoder.sep, Native.naturalEncoder, Native.signedEncoder])
        (by decide)))
    else
      elabCommand (← `(command| abbrev $encoder := $input))
    elabCommand (← `(command| instance $linked:ident :
      Native.Linked 24 ($encoder).representation ($name).body ($encoder).representation := by ram_link))
    elabCommand (← `(command| def $run (x : $ty)
        (valid : ($proc).requires x := by trivial) : Result $ty :=
      Native.runEncoded (rate := 24) (Q := ($encoder).representation) $proc $encoder x valid (by trivial)))
    elabCommand (← `(command| def $bound (x : $ty) : Nat :=
      2 * (24 * ($proc).credits x + ($encoder).saved x)))
    elabCommand (← `(command| theorem $correct (x : $ty) (valid : ($proc).requires x) :
        ($proc).ensures x ($run x valid).value ∧ ($run x valid).steps ≤ $bound x :=
      Native.runEncoded_correct (rate := 24) (Q := ($encoder).representation)
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
