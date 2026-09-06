/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.ArraySubstitution
import AlgoLib.Experimental.RAM.Prototype.SupportedCompilation

/-!
# Executable substitution and supported-language regressions

Both algorithms reuse one declaration and one logical proof with two separately
verified array representations. Compare the actual RAM runs to independent host
references, including empty arrays and duplicates. Check that the indirect backend
really executes extra pointer loads. No result is supplied by a logical effect.
-/
namespace AlgoLib.Experimental.RAM.Tests.ArraySubstitution
open Authoring Prototype Prototype.ArraySubstitution

/-- Every supported source program receives actual Loom-to-RAM correctness. -/
example (s : Mutable.State) (budget : Nat) (post : Mutable.State → Prop)
    (p : Program Mutable.State) (supported : Supported IndirectArrays.model p)
    (h : _root_.wp (denote p) (fun _ t _ => post t) s budget)
    (machine : Checked.State) (rep : IndirectArrays.model.Represents s
      (Checked.Language.observe machine)) :
    ∃ steps final t, Checked.Exec supported.compile.source.compile machine steps final ∧
      IndirectArrays.model.Represents t (Checked.Language.observe final) ∧ post t ∧
      steps ≤ IndirectArrays.model.overhead * budget :=
  loom_to_supported_ram supported post s budget h machine rep

/-- A complete matrix of source constructors, independent of a terminating input. -/
def constructors : Program Mutable.State :=
  .seq .skip (.branch (Mutable.compare .lt "i" "n")
    (.loop (Mutable.compare .lt "i" "n")
      (.seq (.action (Mutable.read "x" (.local "i")))
        (.seq (.action (Mutable.write (.local "i") (.local "x")))
          (.action (Mutable.assign "i" (.add (.local "i") (.literal 1)))))))
    .skip)

example : Supported Mutable.model constructors := by ram_supported
example : Supported IndirectArrays.model constructors := by ram_supported

/-- Unregistered effects are rejected even inside an unreachable branch. -/
def missing : Action Mutable.State := ⟨fun _ => True, id, fun _ => 0⟩

example : True := by
  let code : Program Mutable.State := .branch (Mutable.compare .eq "x" "x") .skip (.action missing)
  fail_if_success
    have : Supported Mutable.model code := by ram_supported
  trivial

/-- Implemented syntax alone is not a termination proof or a budget proof. -/
example (s : Mutable.State) :
    ¬ VC (.loop (Mutable.compare .eq "x" "x") .skip) (fun _ _ => True) s 0 := by
  rintro ⟨I, initial, step⟩
  have impossible := (step s 0 initial).1
  omega

set_option linter.hashCommand false in
#eval show IO Unit from do
  for n in List.range 6 do
    for mask in List.range (3 ^ n) do
      let xs := ((List.range n).map (fun i => mask / 3 ^ i % 3)).toArray
      let dense := denseSort.run xs (by trivial)
      let indirect := indirectSort.run xs (by trivial)
      let expected := xs.toList.mergeSort (· ≤ ·)
      unless dense.value.toList == expected && indirect.value.toList == expected do
        throw <| IO.userError s!"array substitution sort: {xs}"
      unless dense.steps ≤ denseSort.method.time xs &&
          indirect.steps ≤ indirectSort.method.time xs do
        throw <| IO.userError s!"array substitution sort budget: {xs}"
      let zeros := Array.replicate n 0
      let left := denseZero.run xs (by trivial)
      let right := indirectZero.run xs (by trivial)
      unless left.value == zeros && right.value == zeros do
        throw <| IO.userError s!"array substitution zero: {xs}"
      unless left.steps ≤ denseZero.method.time xs && right.steps ≤ indirectZero.method.time xs do
        throw <| IO.userError s!"array substitution zero budget: {xs}"
  let xs := #[3, 1, 2]
  unless (indirectSort.run xs (by trivial)).steps > (denseSort.run xs (by trivial)).steps do
    throw <| IO.userError "the indirect implementation did not execute additional pointer loads"

end AlgoLib.Experimental.RAM.Tests.ArraySubstitution
