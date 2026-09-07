/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Compiler.Assembly

/-!
# Compiler: supported public entry point

Import this module for the documented compiler API. Layer-aligned exported
names are the preferred spelling for new clients; the original names remain valid
compatibility spellings. Exports refer to the same definitions and checked proofs,
not copied implementations. See Compiler/README.md and docs/PUBLIC-API.md.
-/

namespace AlgoLib.Experimental.RAM.Compiler
export AlgoLib.Experimental.RAM.Native (runEncoded runEncoded_correct)
end AlgoLib.Experimental.RAM.Compiler

namespace AlgoLib.Experimental.RAM.Compiler
export AlgoLib.Experimental.RAM.Prototype.Composition (Result)
end AlgoLib.Experimental.RAM.Compiler
