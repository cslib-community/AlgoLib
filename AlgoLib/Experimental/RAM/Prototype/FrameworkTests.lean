/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Velvet.Std
import AlgoLib.Experimental.RAM.Prototype.LoomObservation

/-!
# Regression checks for the actual upstream framework integration

These checks exercise the full Loom hierarchy and composed transformers, plus
Velvet's own method parser, mutable locals, annotated loops, procedure calls,
`prove_correct`, `loom_solve`, and executable extraction. They are framework tests;
RAM time claims come from the separate checked adapter and its shared program.
-/
namespace AlgoLib.Experimental.RAM.Prototype.FrameworkTests

noncomputable section Algebras
open TotalCorrectness ExceptionAsFailure

example : MAlg Id Prop := inferInstance
example : MAlgDet Id Prop := inferInstance
example : MAlgTotal DivM := inferInstance
example : MAlgOrdered (StateT Nat (ReaderT Nat DivM)) (Nat → Nat → Prop) := inferInstance
example : MAlgDet (StateT Nat (ReaderT Nat DivM)) (Nat → Nat → Prop) := inferInstance
example : MAlgTotal (StateT Nat (ReaderT Nat DivM)) := inferInstance
example : MAlgOrdered (ExceptT Unit (StateT Nat DivM)) (Nat → Prop) := inferInstance
example : MAlgDet (ExceptT Unit (StateT Nat DivM)) (Nat → Prop) := inferInstance
example : MAlgTotal (ExceptT Unit (StateT Nat DivM)) := inferInstance
example : MAlgLift DivM Prop (StateT Nat DivM) (Nat → Prop) := inferInstance
example : MAlgLift DivM Prop (ReaderT Nat DivM) (Nat → Prop) := inferInstance
example : MAlgLift DivM Prop (ExceptT Unit DivM) Prop := inferInstance
example : MAlgLiftT DivM Prop (StateT Nat (ReaderT Nat DivM))
    (Nat → Nat → Prop) := inferInstance
end Algebras

section PartialAlgebras
open PartialCorrectness ExceptionAsSuccess
noncomputable example : MAlgPartial (StateT Nat (ReaderT Nat DivM)) := inferInstance
noncomputable example : NoFailure (ExceptT Unit (StateT Nat DivM)) := inferInstance
end PartialAlgebras

section Velvet
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

method counter (n : Nat) return (r : Nat)
  ensures r = n
  do
    let mut i := 0
    while i < n
      invariant i ≤ n
      decreasing n - i
      do
        i := i + 1
    return i

prove_correct counter by
  loom_solve

method callCounter (n : Nat) return (r : Nat)
  ensures r = n
  do
    let x ← counter n
    return x

prove_correct callCounter by
  loom_solve

extract_program_for callCounter

set_option linter.hashCommand false in
/-- info: 7 -/
#guard_msgs in
#eval (callCounterExec 7).run

method arrayPasses (mut a : Array Nat) return (u : Unit)
  ensures a.size = aOld.size
  do
    let mut pass := 0
    while pass < 2
      invariant pass ≤ 2
      invariant a.size = aOld.size
      decreasing 2 - pass
      do
        let mut i := 0
        while i < a.size
          invariant i ≤ a.size
          invariant a.size = aOld.size
          decreasing a.size - i
          do
            a[i] := pass
            i := i + 1
        pass := pass + 1
    return

prove_correct arrayPasses by
  loom_solve

extract_program_for arrayPasses

set_option linter.hashCommand false in
/-- info: (PUnit.unit, #[1, 1]) -/
#guard_msgs in
#eval (arrayPassesExec #[7, 8]).run
end Velvet

end AlgoLib.Experimental.RAM.Prototype.FrameworkTests
