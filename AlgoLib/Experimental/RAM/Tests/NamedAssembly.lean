/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly

/-!
# Named proof blocks through final executable assembly

One command checks the obligations and emits the actual RAM list runner and its
joint functional/cost theorem. The scan reads every input cell and preserves the array.
-/
namespace AlgoLib.Experimental.RAM.Tests.NamedAssembly
open Prototype.Composition

ram method scanInput (mut arr : Array Nat) return (result : Unit)
  require True
  ensures arr = arrOld
  do
    let mut i := 0
    while i < arr.size named scan
      invariant "index" i ≤ arr.size
      iterations_at_most arr.size - i
      do
        let item := arr[i]!
        i := i + 1

verify_array_method scanInput where
  case scan.terminate => by first | omega | trivial
  case scan.account => by first | omega | trivial

set_option linter.hashCommand false in
#eval show IO Unit from do
  for xs in [[], [3], [3, 1, 2]] do
    let r := scanInputRun xs
    unless r.value == xs && r.steps ≤ scanInputBound xs do
      throw <| IO.userError "named proof assembly"

set_option linter.hashCommand false in
/-- info: 'AlgoLib.Experimental.RAM.Tests.NamedAssembly.scanInputCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scanInputCorrect

end AlgoLib.Experimental.RAM.Tests.NamedAssembly
