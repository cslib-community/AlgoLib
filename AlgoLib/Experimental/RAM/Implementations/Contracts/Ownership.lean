/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Store-independent ownership and private potential

The laws depend only on observable cells, equality, and finite exclusive footprints.
They do not depend on Nat-valued storage, an instruction set, or a compiler.
Both legacy implementation contracts and native integer contracts instantiate this
same model. Private potential remains Nat and adds under separating composition.

Design credit: separation logic with amortized resources (Atkey) and Sepref's
refinement-based imperative data structures (Lammich).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Ownership

structure Model where
  State : Type
  Location : Type
  Value : Type
  locationEq : DecidableEq Location
  read : State → Location → Value

attribute [instance] Model.locationEq

abbrev Footprint (M : Model) := Finset M.Location
variable {M : Model}

def Agree (r : Footprint M) (s t : M.State) : Prop := ∀ l ∈ r, M.read t l = M.read s l

def Writes (r : Footprint M) (s t : M.State) : Prop := ∀ l, l ∉ r → M.read t l = M.read s l

theorem Writes.refl (r : Footprint M) (s : M.State) : Writes r s s := fun _ _ => rfl

theorem Writes.trans {r : Footprint M} {s t u : M.State} (h : Writes r s t) (k : Writes r t u) :
    Writes r s u := fun l hl => (k l hl).trans (h l hl)

theorem Writes.mono {r v : Footprint M} (h : r ⊆ v) {s t : M.State} (w : Writes r s t) :
    Writes v s t := fun l hl => w l (fun hr => hl (h hr))

theorem Writes.agree {r f : Footprint M} {s t : M.State} (h : Writes r s t) (d : Disjoint r f) :
    Agree f s t := by
  intro l hl
  exact h l (fun hr => Finset.disjoint_left.mp d hr hl)

/-- An owned abstract value and its private saved potential. -/
structure Representation (M : Model) (A : Type) where
  holds : A → Footprint M → M.State → Nat → Prop
  locality : ∀ {a r s t p}, Agree r s t → holds a r s p → holds a r t p

/-- Ownership and saved potential of separate components combine together. -/
def Representation.sep (P : Representation M A) (Q : Representation M B) : Representation M (A × B) where
  holds a r s p := ∃ r₁ r₂ p₁ p₂, Disjoint r₁ r₂ ∧ r = r₁ ∪ r₂ ∧ p = p₁ + p₂ ∧
    P.holds a.1 r₁ s p₁ ∧ Q.holds a.2 r₂ s p₂
  locality := by
    rintro a r s t p h ⟨r₁, r₂, p₁, p₂, hd, rfl, rfl, hP, hQ⟩
    exact ⟨r₁, r₂, p₁, p₂, hd, rfl, rfl,
      P.locality (fun l hl => h l (Finset.mem_union_left _ hl)) hP,
      Q.locality (fun l hl => h l (Finset.mem_union_right _ hl)) hQ⟩

/-- Empty ownership has zero saved resources. -/
def Representation.unit : Representation M Unit where
  holds _ r _ p := r = ∅ ∧ p = 0
  locality _ h := h

/-- The frame lemma preserves the assertion AND the frame's saved potential. -/
theorem Representation.frame (Q : Representation M B) {b f r s t p}
    (hq : Q.holds b f s p) (hd : Disjoint r f) (writes : Writes r s t) : Q.holds b f t p :=
  Q.locality (writes.agree hd) hq

/-- Spatial symmetry is an ownership/resource law, not a runtime copy. -/
theorem Representation.sep_comm (P : Representation M A) (Q : Representation M B) :
    (P.sep Q).holds (a, b) r s p ↔ (Q.sep P).holds (b, a) r s p := by
  constructor <;> rintro ⟨r₁, r₂, p₁, p₂, hd, hr, hp, hP, hQ⟩
  · exact ⟨r₂, r₁, p₂, p₁, hd.symm, by simpa [Finset.union_comm] using hr,
      by omega, hQ, hP⟩
  · exact ⟨r₂, r₁, p₂, p₁, hd.symm, by simpa [Finset.union_comm] using hr,
      by omega, hQ, hP⟩

theorem Representation.sep_unit (P : Representation M A) :
    (P.sep Representation.unit).holds (a, ()) r s p ↔ P.holds a r s p := by
  constructor
  · rintro ⟨r₁, r₂, p₁, p₂, _, hr, hp, hP, he, hz⟩
    subst r₂; subst p₂
    simpa [hr, hp] using hP
  · intro h
    exact ⟨r, ∅, p, 0, Finset.disjoint_empty_right _, by simp, by omega, h, rfl, rfl⟩

/-- Spatial associativity preserves both the ownership split and total saved credits. -/
theorem Representation.sep_assoc (P : Representation M A) (Q : Representation M B)
    (S : Representation M C) :
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
theorem no_duplicate (r : Footprint M) (nonempty : r.Nonempty) : ¬ Disjoint r r := by
  intro h
  obtain ⟨l, hl⟩ := nonempty
  exact Finset.disjoint_left.mp h hl hl

end AlgoLib.Experimental.RAM.Ownership
