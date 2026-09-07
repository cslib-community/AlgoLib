/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Ownership
import AlgoLib.Experimental.RAM.Backend.Native.Execution

/-!
# Ownership of native integer storage

A cell stores one integer. Natural words, pointers, and signed variables have
distinct register locations; heap locations are shared and require exclusive
ownership. Framing preserves the exact integer in every unowned cell, including
negative values, and preserves the frame's private potential.
-/
namespace AlgoLib.Experimental.RAM.Native

inductive Location where
  | register (ty : Ty) (name : String)
  | heap (address : Nat)
  deriving DecidableEq

def cell (s : Store) : Location → Int
  | .register ty name => s.vars ty name
  | .heap address => s.heap address

abbrev ownershipModel : Ownership.Model :=
  ⟨Store, Location, Int, inferInstance, cell⟩

abbrev Footprint := Ownership.Footprint ownershipModel
abbrev Agree := @Ownership.Agree ownershipModel
abbrev Writes := @Ownership.Writes ownershipModel
abbrev Representation := Ownership.Representation ownershipModel

/-- Register assignment cannot alter any other owned component's representation. -/
theorem writes_set {ty : Ty} {r : Footprint} (s : Store) (v : Var ty) (n : Int)
    (owned : Location.register ty v.name ∈ r) : Writes r s (s.set v n) := by
  intro l hl
  cases l with
  | heap i => rfl
  | register t name =>
    have hn : ¬ (t = ty ∧ name = v.name) := by
      rintro ⟨rfl, rfl⟩
      exact hl owned
    simp [ownershipModel, cell, Store.set, hn]

/-- Heap writes preserve all registers and every different heap cell. -/
theorem writes_write {r : Footprint} (s : Store) (address : Nat) (value : Int)
    (owned : Location.heap address ∈ r) : Writes r s (s.write address value) := by
  intro l hl
  cases l with
  | register t name => rfl
  | heap i =>
    have hn : i ≠ address := fun h => hl (h ▸ owned)
    simp [ownershipModel, cell, Store.write, hn]

end AlgoLib.Experimental.RAM.Native
