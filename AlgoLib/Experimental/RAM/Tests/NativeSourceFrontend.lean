/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Compiler.Assembly
import AlgoLib.Experimental.RAM.Implementations.Native.ScalarStorage

/-!
# Existing source frontend linked to single-cell native signed storage

The source program and its logical proof use the ordinary obligation API.
A native representation supplies the implementation; execution uses the shared
linker and verified native compiler. The surrounding negative heap is preserved.
-/
namespace AlgoLib.Experimental.RAM.Tests.NativeSourceFrontend
open Prototype.Composition Prototype.Frontend

ram method subtractFive (mut x : Int) return (result : Int)
  ensures result = xOld - 5
  do
    x := x - 5

generate_obligations subtractFive
complete_algorithm subtractFive
compile_scalar_method subtractFive

private abbrev slot : Native.Var .integer := ⟨"x"⟩
private abbrev rep := Native.signedScalar slot
private abbrev footprint : Native.Footprint := {Native.Location.register .integer "x"}

private def input (x : Int) : Native.Store :=
  ⟨fun ty name => if ty = .integer ∧ name = "x" then x else 0, fun _ => -99⟩

private theorem input_rep (x : Int) : rep.holds x footprint (input x) 0 := by
  exact ⟨rfl, by simp [input, slot], rfl⟩

private instance : Native.Linked 24 rep subtractFiveProcedure.body rep := by ram_link

private def supported : Native.Supported 24 rep rep subtractFiveProcedure.body :=
  (inferInstance : Native.Linked 24 rep subtractFiveProcedure.body rep).supported

private theorem terminates (x : Int) :
    ∃ k t, Native.Eval supported.compile.code (input x) k t := by
  obtain ⟨k, b, run, _, _⟩ := subtractFiveProcedure.correct x trivial
  obtain ⟨steps, t, left, he, _, _, _⟩ := supported.compile.sound run _ _ 0 (input_rep x)
  exact ⟨steps, t, he⟩

private def execute (x : Int) : Nat × Native.Store :=
  Native.run supported.compile.code (input x) (terminates x)

set_option linter.hashCommand false in
#guard_msgs in
#eval show IO Unit from do
  for x in [-10, -1, 0, 3, 5, 20] do
    let result := execute x
    unless result.2.vars .integer "x" == x - 5 && result.1 == 4 do
      throw <| IO.userError s!"native source signed subtraction: {x}, steps={result.1}"
    unless (subtractFiveRun x).value == result.2.vars .integer "x" do
      throw <| IO.userError "the unchanged source proof disagrees across storage implementations"
    unless result.2.heap 0 == -99 do
      throw <| IO.userError "native source framing changed an unowned negative cell"

/-- Negation exchanges code views instead of charging unbounded syntax overhead. -/
private abbrev twiceNegated : SignedValue Int := .neg (.neg (.scalar .here))

example : (inferInstance : Native.SignedExpression rep twiceNegated).code.cost = 1 := rfl

/-- Truncating a negative natural expression keeps its original constant allowance. -/
private abbrev cheapZero : Value Nat := .toNat (.neg (.ofNat
  (.binary .mul (.scalar .here) (.binary .add (.scalar .here) (.literal 100)))))

example : cheapZero.credits = 1 := rfl
example : (inferInstance : Native.Expression (Native.naturalScalar ⟨"n"⟩) cheapZero).code.cost = 1 := rfl

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Native.client_linking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Native.client_linking

end AlgoLib.Experimental.RAM.Tests.NativeSourceFrontend
