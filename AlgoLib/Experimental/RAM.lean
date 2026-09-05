/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Programs.Sorting
import AlgoLib.Experimental.RAM.Programs.Connectivity
import AlgoLib.Experimental.RAM.Specification.GraphBridge

/-!
# Verified RAM algorithms: the public entry point

Start with `Programs/Sorting.lean` or `Programs/Connectivity.lean`. Each contains
its target specification, input/output method, generated VCs, invariant proof,
executable, and main theorem. `Authoring` supplies the shared proof API; `Library`
supplies certified operations. Memory, compiler, and machine details are below
those interfaces. Older alternative demos require an explicit `Legacy` import.
-/
