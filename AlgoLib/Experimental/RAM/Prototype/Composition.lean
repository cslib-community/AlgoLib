/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Language
import AlgoLib.Experimental.RAM.Prototype.Composition.Loom
import AlgoLib.Experimental.RAM.Prototype.Composition.Compatibility

/-!
# Public proof vocabulary for compositional clients

Import this module to write typed clients, supply mathematical invariants, compose
procedure contracts, and reuse existing Authoring proofs. It has no RAM dependency.
Implementers separately import Composition.Execution and their owned operation
packages. See Composition/README.md for the four boundaries and executable examples.
-/
