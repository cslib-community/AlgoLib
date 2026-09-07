/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Natural.Language.VC
import AlgoLib.Experimental.RAM.Implementations.Contracts.Ownership
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Local ownership of registers, heap cells, and private potential

A representation observes only its owned finite footprint. Separating product
requires disjoint footprints and adds the saved resources; neither exclusive cells
nor saved credits can be duplicated. Potential is existential implementation state,
not a field in the algorithm's mathematical model. Fixed footprints may reserve
unused storage. Allocation and shared read permissions require additional contracts.

Design credit: separation logic with amortized resources (Atkey), and Sepref's
refinement-based imperative data structures (Lammich); see README.md for citations.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

inductive Location where
  | register (ty : Ty) (name : String)
  | heap (address : Nat)
  deriving DecidableEq

abbrev Footprint := Finset Location

def cell (s : Store) : Location → Nat
  | .register ty name => s.vars ty name
  | .heap address => s.heap address

/-- Legacy store view; the separation algebra itself is shared with native storage. -/
abbrev ownershipModel : Ownership.Model :=
  ⟨Store, Location, Nat, inferInstance, cell⟩

abbrev Agree := @Ownership.Agree ownershipModel
abbrev Writes := @Ownership.Writes ownershipModel

theorem Writes.refl (r : Footprint) (s : Store) : Writes r s s :=
  Ownership.Writes.refl (M := ownershipModel) r s

theorem Writes.trans {r : Footprint} {s t u : Store} (h : Writes r s t) (k : Writes r t u) :
    Writes r s u := Ownership.Writes.trans h k

theorem Writes.mono {r v : Footprint} (h : r ⊆ v) {s t : Store} (w : Writes r s t) :
    Writes v s t := Ownership.Writes.mono h w

theorem Writes.agree {r f : Footprint} {s t : Store} (h : Writes r s t) (d : Disjoint r f) :
    Agree f s t := Ownership.Writes.agree h d

/-- Primitive mutations preserve every unowned register and heap cell. -/
theorem Writes.set {r : Footprint} (s : Store) (v : Var ty) (n : Nat)
    (owned : Location.register ty v.name ∈ r) : Writes r s (s.set v n) := by
  intro l hl
  cases l with
  | heap i => rfl
  | register t name =>
    have hn : ¬ (t = ty ∧ name = v.name) := by
      rintro ⟨rfl, rfl⟩
      exact hl owned
    simp [cell, Store.set, hn]

theorem Writes.write {r : Footprint} (s : Store) (address value : Nat)
    (owned : Location.heap address ∈ r) : Writes r s (s.write address value) := by
  intro l hl
  cases l with
  | register t name => rfl
  | heap i =>
    have hn : i ≠ address := fun h => hl (h ▸ owned)
    simp [cell, Store.write, hn]

/-- Compatibility name for the store-independent representation interface. -/
abbrev Representation := Ownership.Representation ownershipModel

abbrev Representation.sep (P : Representation A) (Q : Representation B) :
    Representation (A × B) := Ownership.Representation.sep P Q

abbrev Representation.unit : Representation Unit := Ownership.Representation.unit

theorem Representation.frame (Q : Representation B) {b f r s t p}
    (hq : Q.holds b f s p) (hd : Disjoint r f) (writes : Writes r s t) : Q.holds b f t p :=
  Ownership.Representation.frame Q hq hd writes

theorem Representation.sep_comm (P : Representation A) (Q : Representation B) :
    (P.sep Q).holds (a, b) r s p ↔ (Q.sep P).holds (b, a) r s p :=
  Ownership.Representation.sep_comm P Q

theorem Representation.sep_unit (P : Representation A) :
    (P.sep Representation.unit).holds (a, ()) r s p ↔ P.holds a r s p :=
  Ownership.Representation.sep_unit P

theorem Representation.sep_assoc (P : Representation A) (Q : Representation B)
    (S : Representation C) :
    ((P.sep Q).sep S).holds ((a, b), c) r s saved ↔
      (P.sep (Q.sep S)).holds (a, (b, c)) r s saved :=
  Ownership.Representation.sep_assoc P Q S

theorem no_duplicate (r : Footprint) (nonempty : r.Nonempty) : ¬ Disjoint r r :=
  Ownership.no_duplicate (M := ownershipModel) r nonempty

end AlgoLib.Experimental.RAM.Prototype.Composition
