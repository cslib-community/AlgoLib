/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Compiler.Assembly.Natural.Execution

/-!
# Owned procedure contracts linked to native integer execution

Existing natural implementation certificates lower into the native typed IR,
then compile directly to integer instructions. The theorem preserves ownership,
private potential, and the algorithm's unchanged logical-credit contract.
There is no Nat-machine instruction compilation or simulation in this path.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

/-- Uniform transport of the existing owned procedure linking theorem to Int-RAM.
Initial private potential is scaled with the instruction simulation overhead. -/
theorem integer_procedure_linking {A B : Type} {rate : Nat} {P : Representation A}
    {Q : Representation B} (proc : Procedure A B)
    (supported : Supported rate P Q proc.body) (a : A) (valid : proc.requires a)
    (r : Footprint) (initial : Store) (saved : Nat)
    (rep : P.holds a r initial saved) :
    ∃ steps final b left,
      Integer.Exec (Native.Natural.command supported.compile.code).compile
        (integerEncode initial) steps final ∧
      Q.holds b r (integerObserve final) left ∧ proc.ensures a b ∧
      Writes r initial (integerObserve final) ∧
      steps + 2 * left ≤ 2 * (rate * proc.credits a + saved) :=
  procedure_linking proc supported a valid r initial saved rep

end AlgoLib.Experimental.RAM.Prototype.Composition
