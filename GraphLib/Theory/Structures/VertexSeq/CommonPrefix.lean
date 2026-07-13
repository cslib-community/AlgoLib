/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import Mathlib.Data.List.Basic

/-!
# Longest common prefix of two lists

A structurally recursive `List.commonPrefix`, together with the single splitting
lemma that its clients need. Everything here is index-free: no `getElem`, no
`findIdx`, no bound arithmetic.

This is what lets `SimpleCycle` locate the point where two paths diverge without
dragging dependent `getElem` bounds through every step.

The file lives under `VertexSeq/` only because the library has no general-purpose
`List` utility module yet; it mentions no `VertexSeq`. See `AGENTS/Remark.md`.

## Main definitions

* `List.commonPrefix` — the longest common prefix of two lists.

## Main results

* `List.commonPrefix_split` — the common prefix cuts both lists, and the first
  entries after the cut differ.
-/

variable {α : Type*}

namespace List

/-- The longest common prefix of two lists. -/
@[grind] def commonPrefix [DecidableEq α] : List α → List α → List α
  | x :: xs, y :: ys => if x = y then x :: commonPrefix xs ys else []
  | _, _ => []

/-- The common prefix cuts both lists, and whatever follows the cut starts with
two different entries (when both remainders are non-empty).

This single lemma carries everything a caller needs: the two splittings and the
divergence of the successors. -/
lemma commonPrefix_split [DecidableEq α] (l₁ l₂ : List α) :
    ∃ r₁ r₂, l₁ = commonPrefix l₁ l₂ ++ r₁ ∧ l₂ = commonPrefix l₁ l₂ ++ r₂ ∧
      ∀ x ∈ r₁.head?, ∀ y ∈ r₂.head?, x ≠ y := by
  induction l₁ generalizing l₂ with
  | nil => exact ⟨[], l₂, by grind, by grind, by grind⟩
  | cons x xs ih =>
      cases l₂ with
      | nil => exact ⟨x :: xs, [], by grind, by grind, by grind⟩
      | cons y ys =>
          by_cases hxy : x = y
          · obtain ⟨r₁, r₂, h₁, h₂, hne⟩ := ih ys
            exact ⟨r₁, r₂, by grind, by grind, by grind⟩
          · exact ⟨x :: xs, y :: ys, by grind, by grind, by grind⟩

/-- Two lists starting at the same entry have a non-empty common prefix. -/
lemma commonPrefix_ne_nil [DecidableEq α] {l₁ l₂ : List α} {x : α}
    (h₁ : l₁.head? = some x) (h₂ : l₂.head? = some x) :
    commonPrefix l₁ l₂ ≠ [] := by
  cases l₁ <;> cases l₂ <;> grind

end List
