/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Implementations.Native.Expressions

/-!
# Single-cell native scalar representations

Each scalar owns one typed register. Updating it preserves all other integer cells
exactly, so natural and signed scalars can coexist under the shared separating
representation. Neither representation has private stored potential.
-/
namespace AlgoLib.Experimental.RAM.Native

/-- A signed scalar owns one integer register, without positive/negative lanes. -/
def signedScalar (v : Var .integer) : Representation Int where
  holds a r s c := r = {Location.register .integer v.name} ∧ s.vars .integer v.name = a ∧ c = 0
  locality := by
    rintro a r s t c agree ⟨rfl, hv, hc⟩
    exact ⟨rfl, (agree _ (Finset.mem_singleton_self _)).trans hv, hc⟩

instance (v : Var .integer) : SignedStorage (signedScalar v) where
  register := v
  read _ _ _ _ h := h.2.1
  update a r s c h b := by
    obtain ⟨rfl, _, hc⟩ := h
    exact ⟨⟨rfl, by simp [Store.set], hc⟩, writes_set _ _ _ (Finset.mem_singleton_self _)⟩

/-- Natural nonnegativity belongs to its representation, not every machine cell. -/
def naturalScalar (v : Var .word) : Representation Nat where
  holds a r s c := r = {Location.register .word v.name} ∧ s.vars .word v.name = (a : Int) ∧ c = 0
  locality := by
    rintro a r s t c agree ⟨rfl, hv, hc⟩
    exact ⟨rfl, (agree _ (Finset.mem_singleton_self _)).trans hv, hc⟩

instance (v : Var .word) : ScalarStorage (naturalScalar v) where
  register := v
  read _ _ _ _ h := h.2.1
  update a r s c h b := by
    obtain ⟨rfl, _, hc⟩ := h
    exact ⟨⟨rfl, by simp [Store.set], hc⟩, writes_set _ _ _ (Finset.mem_singleton_self _)⟩

end AlgoLib.Experimental.RAM.Native
