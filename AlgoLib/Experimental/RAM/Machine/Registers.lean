/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Mathlib.Data.List.Basic

/-!
# Register identifiers

Shared names for machine registers; the identifiers do not constrain their value type.
-/
namespace AlgoLib.Experimental.RAM.Checked

/-- Named registers and compiler temporaries. Each finite program uses finitely many. -/
inductive Reg where
  | base | count | limit | cursor | key | next | temp | live
  | user (kind : Nat) (name : String)
  | scratch (index : Nat)
  | saved (depth : Nat)
  deriving DecidableEq, Repr

end AlgoLib.Experimental.RAM.Checked
