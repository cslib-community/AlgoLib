/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Machine.Integer.Runner
import AlgoLib.Experimental.RAM.Machine.Output

/-!
# Machine: supported public entry point

Import this module for the documented machine API. Layer-aligned exported
names are the preferred spelling for new clients; the original names remain valid
compatibility spellings. Exports refer to the same definitions and checked proofs,
not copied implementations. See Machine/README.md and docs/PUBLIC-API.md.
-/

namespace AlgoLib.Experimental.RAM.Machine
export AlgoLib.Experimental.RAM.Checked (Reg Bitmap Execution)
end AlgoLib.Experimental.RAM.Machine

namespace AlgoLib.Experimental.RAM.Machine
export AlgoLib.Experimental.RAM.Integer (State Operand Instr Code Exec Terminates TotalProgram run run_eq run_correct)
end AlgoLib.Experimental.RAM.Machine
