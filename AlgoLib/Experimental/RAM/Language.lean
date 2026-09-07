/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Language.Frontend

/-!
# Language: supported public entry point

Import this module for the documented language API. Layer-aligned exported
names are the preferred spelling for new clients; the original names remain valid
compatibility spellings. Exports refer to the same definitions and checked proofs,
not copied implementations. See Language/README.md and docs/PUBLIC-API.md.
-/

namespace AlgoLib.Experimental.RAM.Language
export AlgoLib.Experimental.RAM.Prototype.Composition (Operation Program Run VC Procedure Contract UniformCredits)
end AlgoLib.Experimental.RAM.Language

namespace AlgoLib.Experimental.RAM.Language.Program
export AlgoLib.Experimental.RAM.Prototype.Composition.Program (identity swap invoke seq frame branch loop call)
end AlgoLib.Experimental.RAM.Language.Program

namespace AlgoLib.Experimental.RAM.Language.Contract
export AlgoLib.Experimental.RAM.Prototype.Composition.Contract (implement)
end AlgoLib.Experimental.RAM.Language.Contract

namespace AlgoLib.Experimental.RAM.Language.Procedure
export AlgoLib.Experimental.RAM.Prototype.Composition.Procedure (verify uniform)
end AlgoLib.Experimental.RAM.Language.Procedure
