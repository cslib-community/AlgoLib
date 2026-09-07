/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Language.Frontend
import AlgoLib.Experimental.RAM.Language.Contracts
import AlgoLib.Experimental.RAM.Verification.Loom

/-!
# Public proof vocabulary for compositional clients

Import this module to write typed clients, supply mathematical invariants, compose
procedure contracts, and reason in Loom. It has no RAM dependency.
Implementers separately import Compiler.Assembly and their owned operation
packages. See RAM/README.md for the four boundaries and executable examples.
-/
