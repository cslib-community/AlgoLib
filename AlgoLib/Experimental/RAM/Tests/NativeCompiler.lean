/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Compiler.Native.Execution

/-!
# Native compiler regression

These tests execute the native compiler, without the Nat compiler or embedding.
Signed and saturating natural subtraction have distinct results and exact costs.
A signed store occupies one machine cell, and the compiler certificate supplies
termination rather than a runtime fuel argument.
-/
namespace AlgoLib.Experimental.RAM.Tests.NativeCompiler
open Native

private def initial : Store := ⟨fun _ _ => 0, fun _ => 0⟩
private def signedSub : Expr .integer := .bin .intSub (.lit 3) (.lit 5)
private def naturalSub : Expr .word := .bin .sub (.lit 3) (.lit 5)
private def signedVar : Var .integer := ⟨"result"⟩
private def naturalVar : Var .word := ⟨"result"⟩

def signed : Method Unit where
  body := .assign signedVar signedSub
  input := fun _ => initial
  terminates := fun _ => ⟨_, _, .assign _ _ _⟩

def natural : Method Unit where
  body := .assign naturalVar naturalSub
  input := fun _ => initial
  terminates := fun _ => ⟨_, _, .assign _ _ _⟩

def signedCell : Method Unit where
  body := .write (.lit 7) signedSub
  input := fun _ => initial
  terminates := fun _ => ⟨_, _, .write _ _ _⟩

/-- Signed subtraction is represented by an actual negative register value. -/
example : (signed.run ()).2.vars .integer "result" = -2 := by
  rw [signed.run_eq () (.assign _ _ _)]
  rfl

/-- Source Nat subtraction retains its original saturating semantics. -/
example : (natural.run ()).2.vars .word "result" = 0 := by
  rw [natural.run_eq () (.assign _ _ _)]
  rfl

set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  let a := signed.run ()
  let b := natural.run ()
  let c := signedCell.run ()
  unless a.1 == 4 && a.2.vars .integer "result" == -2 do
    throw <| IO.userError "native signed subtraction"
  unless b.1 == 5 && b.2.vars .word "result" == 0 do
    throw <| IO.userError "native natural subtraction"
  unless c.1 == 5 && c.2.heap 7 == -2 && c.2.heap 8 == 0 do
    throw <| IO.userError "native single-cell signed storage"

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Native.Expr.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Native.Expr.correct
set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Native.Eval.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Native.Eval.compile
set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Native.run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Native.run_eq

end AlgoLib.Experimental.RAM.Tests.NativeCompiler
