/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Encoding

/-!
# Public allocation and initialization contracts

An encoder publishes an upper bound on the locations it owns, independently of
its representation and store construction. Region separation proves encoder
separation without inspecting either implementation. Input contracts separately
publish sufficient initialization conditions and the initial saved resources.
These are host-side assembly contracts; they do not charge encoding as RAM work.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition
open Checked.Language

/-- Public permission envelope; implementations may own any finite subset. -/
structure MemoryRegion where
  registers : Ty → String → Prop
  heap : Nat → Prop

def MemoryRegion.contains (r : MemoryRegion) : Location → Prop
  | .register ty name => r.registers ty name
  | .heap address => r.heap address

def MemoryRegion.union (r s : MemoryRegion) : MemoryRegion where
  registers ty name := r.registers ty name ∨ s.registers ty name
  heap address := r.heap address ∨ s.heap address

/-- This contract exposes neither the exact footprint nor its private layout. -/
def Encoder.Within (e : Encoder P) (region : MemoryRegion) : Prop :=
  ∀ location ∈ e.footprint, region.contains location

variable {A B : Type} {P : Representation A} {Q : Representation B}
  {e p : Encoder P} {q : Encoder Q} {r s : MemoryRegion}

theorem Encoder.Within.mono (h : e.Within r)
    (hs : ∀ l, r.contains l → s.contains l) : e.Within s :=
  fun l hl => hs l (h l hl)

theorem Encoder.Within.sep (hp : p.Within r) (hq : q.Within s)
    (hd : Disjoint p.footprint q.footprint) : (p.sep q hd).Within (r.union s) := by
  intro l hl
  rcases Finset.mem_union.mp hl with h | h
  · have := hp l h; cases l <;> exact Or.inl this
  · have := hq l h; cases l <;> exact Or.inr this

/-- Only public permission envelopes are needed to assemble independent components. -/
theorem Encoder.Within.disjoint (hp : p.Within r) (hq : q.Within s)
    (apart : ∀ l, r.contains l → s.contains l → False) :
    Disjoint p.footprint q.footprint :=
  Finset.disjoint_left.mpr fun l hl hr => apart l (hp l hl) (hq l hr)

/-- An initializer may advertise a stronger, convenient precondition. -/
structure Encoder.InputContract (e : Encoder P) (pre : A → Prop) (saved : A → Nat) : Prop where
  accepts : ∀ a, pre a → e.requires a
  saved_eq : ∀ a, pre a → e.saved a = saved a

theorem Encoder.InputContract.sep (hp : p.InputContract pp cp)
    (hq : q.InputContract pq cq) (hd : Disjoint p.footprint q.footprint) :
    (p.sep q hd).InputContract (fun a => pp a.1 ∧ pq a.2)
      (fun a => cp a.1 + cq a.2) := by
  constructor
  · intro a h; exact ⟨hp.accepts _ h.1, hq.accepts _ h.2⟩
  · intro a h; exact congrArg₂ Nat.add (hp.saved_eq _ h.1) (hq.saved_eq _ h.2)

theorem Encoder.InputContract.hide [l : Locals B]
    (hp : p.InputContract pre cost) (hq : q.InputContract localPre localCost)
    (valid : localPre l.initial) (hd : Disjoint p.footprint q.footprint) :
    (p.hide q (hq.accepts _ valid) hd).InputContract pre
      (fun a => cost a + localCost l.initial) := by
  constructor
  · exact hp.accepts
  · intro a h; exact congrArg₂ Nat.add (hp.saved_eq _ h) (hq.saved_eq _ valid)

/-- Scalar storage reserves a public register name, regardless of the stored value. -/
def MemoryRegion.scalar (v : Var .word) : MemoryRegion where
  registers _ name := name = v.name
  heap _ := False

/-- Array storage reserves a size register and a bounded arena. -/
def MemoryRegion.array (l : Storage.ArrayLayout) : MemoryRegion where
  registers _ name := name = l.size.name
  heap address := l.base ≤ address ∧ address < l.base + l.capacity

theorem scalarEncoder_within (v : Var .word) :
    (scalarEncoder v).Within (.scalar v) := by
  intro location owned
  cases location <;> simp_all [scalarEncoder, MemoryRegion.scalar, MemoryRegion.contains]

theorem arrayEncoder_within (l : Storage.ArrayLayout) :
    (arrayEncoder l).Within (.array l) := by
  intro location owned
  cases location <;>
    simp_all [arrayEncoder, Storage.ArrayLayout.footprint, MemoryRegion.array,
      MemoryRegion.contains]
  omega

theorem scalarEncoder_input (v : Var .word) :
    (scalarEncoder v).InputContract (fun _ => True) (fun _ => 0) := ⟨fun _ h => h, fun _ _ => rfl⟩

theorem arrayEncoder_input (l : Storage.ArrayLayout) :
    (arrayEncoder l).InputContract (fun a => a.size ≤ l.capacity) (fun _ => 0) :=
  ⟨fun _ h => h, fun _ _ => rfl⟩

end AlgoLib.Experimental.RAM.Prototype.Composition
