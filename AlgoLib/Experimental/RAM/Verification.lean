/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Verification.ObligationExplorer
import AlgoLib.Experimental.RAM.Verification.Loom

/-!
# Verification: supported public entry point

Import this module for the documented verification API. Layer-aligned exported
names are the preferred spelling for new clients; the original names remain valid
compatibility spellings. Exports refer to the same definitions and checked proofs,
not copied implementations. See Verification/README.md and docs/PUBLIC-API.md.
-/

namespace AlgoLib.Experimental.RAM.Verification
export AlgoLib.Experimental.RAM.Prototype.Composition (Plan Algorithm Obligation ObligationAt SourceShape SourceForall)
end AlgoLib.Experimental.RAM.Verification

namespace AlgoLib.Experimental.RAM.Verification.Plan
export AlgoLib.Experimental.RAM.Prototype.Composition.Plan (vc sound call_implementation_independent)
end AlgoLib.Experimental.RAM.Verification.Plan

namespace AlgoLib.Experimental.RAM.Verification.Algorithm
export AlgoLib.Experimental.RAM.Prototype.Composition.Algorithm (Obligations certify loom_correct)
end AlgoLib.Experimental.RAM.Verification.Algorithm
