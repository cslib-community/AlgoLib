/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Buffer

/-!
# Client proofs using only abstract buffer contracts

These clients use typed calls, separately owned values, and logical credits. The
same proof terms are linked to all implementation combinations in Demo. No physical
representation or private payment argument is available through these imports.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Buffer

/-- One client's proof, used by every implementation satisfying the abstract API. -/
abbrev recycle (capacity x y : Nat) : Program (List Nat) (List Nat) :=
  .seq (.call (push capacity x))
    (.seq (.call (push capacity y)) (.invoke clear))

theorem recycle_vc (capacity x y : Nat) (xs : List Nat) (space : xs.length + 2 ≤ capacity) :
    VC (recycle capacity x y) (fun ys _ => ys = []) xs 5 := by
  simp [VC, argument, append, clear]
  omega

/-- Frame an arbitrary mathematical object; clients do not prove address preservation. -/
theorem recycle_framed (capacity x y : Nat) (xs : List Nat) (r : R)
    (space : xs.length + 2 ≤ capacity) :
    VC (.frame (recycle capacity x y) R) (fun out _ => out = ([], r)) (xs, r) 5 := by
  simpa [VC] using recycle_vc capacity x y xs space

/-- A second component can run after the first under the same abstract proof. -/
theorem recycle_both (capacity x y z w : Nat) (xs ys : List Nat)
    (hx : xs.length + 2 ≤ capacity) (hy : ys.length + 2 ≤ capacity) :
    VC ((recycle capacity x y).both (recycle capacity z w))
      (fun out _ => out = ([], [])) (xs, ys) 10 := by
  simp [VC, argument, append, clear]
  omega

/-- A loop is checked through a supplied invariant; tests also require implementations. -/
abbrev drain : Program (List Nat) (List Nat) := .loop nonempty (.invoke clear)

theorem drain_vc (xs : List Nat) : VC drain (fun ys _ => ys = []) xs 3 := by
  refine ⟨fun ys c => (ys = [] ∧ 1 ≤ c) ∨ 3 ≤ c, Or.inr (by decide), ?_⟩
  intro ys c hi
  cases hi with
  | inl h =>
    obtain ⟨rfl, hc⟩ := h
    exact ⟨hc, by simp [nonempty]⟩
  | inr hc =>
    refine ⟨by omega, ?_⟩
    cases ht : nonempty ys with
    | true =>
      simp only [↓reduceIte, VC, clear]
      exact ⟨trivial, by omega, Or.inl ⟨trivial, by omega⟩⟩
    | false => simpa [nonempty] using ht

end AlgoLib.Experimental.RAM.Prototype.Composition.Buffer
