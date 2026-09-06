/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.VC
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

def Agree (r : Footprint) (s t : Store) : Prop := ∀ l ∈ r, cell t l = cell s l

def Writes (r : Footprint) (s t : Store) : Prop := ∀ l, l ∉ r → cell t l = cell s l

theorem Writes.refl (r : Footprint) (s : Store) : Writes r s s := fun _ _ => rfl

theorem Writes.trans {r : Footprint} {s t u : Store} (h : Writes r s t) (k : Writes r t u) :
    Writes r s u := fun l hl => (k l hl).trans (h l hl)

theorem Writes.mono {r v : Footprint} (h : r ⊆ v) {s t : Store} (w : Writes r s t) :
    Writes v s t := fun l hl => w l (fun hr => hl (h hr))

theorem Writes.agree {r f : Footprint} {s t : Store} (h : Writes r s t) (d : Disjoint r f) :
    Agree f s t := by
  intro l hl
  exact h l (fun hr => Finset.disjoint_left.mp d hr hl)

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

/-- An owned abstract value and its private saved potential. -/
structure Representation (A : Type) where
  holds : A → Footprint → Store → Nat → Prop
  locality : ∀ {a r s t p}, Agree r s t → holds a r s p → holds a r t p

/-- Ownership and saved potential of separate components combine together. -/
def Representation.sep (P : Representation A) (Q : Representation B) : Representation (A × B) where
  holds a r s p := ∃ r₁ r₂ p₁ p₂, Disjoint r₁ r₂ ∧ r = r₁ ∪ r₂ ∧ p = p₁ + p₂ ∧
    P.holds a.1 r₁ s p₁ ∧ Q.holds a.2 r₂ s p₂
  locality := by
    rintro a r s t p h ⟨r₁, r₂, p₁, p₂, hd, rfl, rfl, hP, hQ⟩
    exact ⟨r₁, r₂, p₁, p₂, hd, rfl, rfl,
      P.locality (fun l hl => h l (Finset.mem_union_left _ hl)) hP,
      Q.locality (fun l hl => h l (Finset.mem_union_right _ hl)) hQ⟩

/-- Empty ownership has zero saved resources. -/
def Representation.unit : Representation Unit where
  holds _ r _ p := r = ∅ ∧ p = 0
  locality _ h := h

/-- The frame lemma preserves the assertion AND the frame's saved potential. -/
theorem Representation.frame (Q : Representation B) {b f r s t p}
    (hq : Q.holds b f s p) (hd : Disjoint r f) (writes : Writes r s t) : Q.holds b f t p :=
  Q.locality (writes.agree hd) hq

/-- Spatial symmetry is an ownership/resource law, not a runtime copy. -/
theorem Representation.sep_comm (P : Representation A) (Q : Representation B) :
    (P.sep Q).holds (a, b) r s p ↔ (Q.sep P).holds (b, a) r s p := by
  constructor <;> rintro ⟨r₁, r₂, p₁, p₂, hd, hr, hp, hP, hQ⟩
  · exact ⟨r₂, r₁, p₂, p₁, hd.symm, by simpa [Finset.union_comm] using hr,
      by omega, hQ, hP⟩
  · exact ⟨r₂, r₁, p₂, p₁, hd.symm, by simpa [Finset.union_comm] using hr,
      by omega, hQ, hP⟩

theorem Representation.sep_unit (P : Representation A) :
    (P.sep Representation.unit).holds (a, ()) r s p ↔ P.holds a r s p := by
  constructor
  · rintro ⟨r₁, r₂, p₁, p₂, _, hr, hp, hP, he, hz⟩
    subst r₂; subst p₂
    simpa [hr, hp] using hP
  · intro h
    exact ⟨r, ∅, p, 0, Finset.disjoint_empty_right _, by simp, by omega, h, rfl, rfl⟩

/-- Spatial associativity preserves both the ownership split and total saved credits. -/
theorem Representation.sep_assoc (P : Representation A) (Q : Representation B)
    (S : Representation C) :
    ((P.sep Q).sep S).holds ((a, b), c) r s saved ↔
      (P.sep (Q.sep S)).holds (a, (b, c)) r s saved := by
  constructor
  · rintro ⟨r₁₂, r₃, p₁₂, p₃, hd, hr, hp, hPQ, hS⟩
    obtain ⟨r₁, r₂, p₁, p₂, hd₁₂, rfl, rfl, hP, hQ⟩ := hPQ
    obtain ⟨hd₁₃, hd₂₃⟩ := Finset.disjoint_union_left.mp hd
    exact ⟨r₁, r₂ ∪ r₃, p₁, p₂ + p₃, Finset.disjoint_union_right.mpr ⟨hd₁₂, hd₁₃⟩,
      by simpa [Finset.union_assoc] using hr, by omega, hP,
      ⟨r₂, r₃, p₂, p₃, hd₂₃, rfl, rfl, hQ, hS⟩⟩
  · rintro ⟨r₁, r₂₃, p₁, p₂₃, hd, hr, hp, hP, hQS⟩
    obtain ⟨r₂, r₃, p₂, p₃, hd₂₃, rfl, rfl, hQ, hS⟩ := hQS
    obtain ⟨hd₁₂, hd₁₃⟩ := Finset.disjoint_union_right.mp hd
    exact ⟨r₁ ∪ r₂, r₃, p₁ + p₂, p₃, Finset.disjoint_union_left.mpr ⟨hd₁₃, hd₂₃⟩,
      by simpa [Finset.union_assoc] using hr, by omega,
      ⟨r₁, r₂, p₁, p₂, hd₁₂, rfl, rfl, hP, hQ⟩, hS⟩

/-- Exclusive ownership cannot be duplicated across two separately owned components. -/
theorem no_duplicate (r : Footprint) (nonempty : r.Nonempty) : ¬ Disjoint r r := by
  intro h
  obtain ⟨l, hl⟩ := nonempty
  exact Finset.disjoint_left.mp h hl hl

end AlgoLib.Experimental.RAM.Prototype.Composition
