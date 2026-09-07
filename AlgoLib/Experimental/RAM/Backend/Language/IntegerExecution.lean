/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Verification
import AlgoLib.Experimental.RAM.Backend.Native.Natural

/-!
# Default execution of natural-valued compiler IR on Int-RAM

The existing typed command language is an intermediate representation. Execution
uses integer instructions, including explicit clamping for Nat subtraction. The
natural observation is used only on states certified to represent natural values.
No old interpreter is called to compute the result. Logical contracts retain their
original budgets; the final machine bound includes the verified lowering overhead.
-/
namespace AlgoLib.Experimental.RAM.Checked.Language

/-- Compatibility spelling; the ordinary method runner now uses Int-RAM. -/
abbrev Method.integerRun := Method.run

/-- Compatibility spelling for the native execution witness. -/
abbrev Method.integerRun_exec := Method.run_exec

/-- Compatibility spelling for the native correctness theorem. -/
abbrev Method.integerCorrect := Method.correct

end AlgoLib.Experimental.RAM.Checked.Language
