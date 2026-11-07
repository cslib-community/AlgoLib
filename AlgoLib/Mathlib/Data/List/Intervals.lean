/-
Copyright (c) 2026 Tomás Hoch, Nicolas Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomás Hoch, Nicolas Alvarez
-/
import Mathlib.Data.List.Intervals

/-!
# Additional lemmas about `List.Ico`

Lemmas that belong in `Mathlib.Data.List.Intervals`.

* `List.Ico.append_consecutive_max_min`: `List.Ico.append_consecutive` restricted to a
  window `[a, b)`. This is how a segment tree query splits at an internal node.
-/

namespace List.Ico

/-- `List.Ico.append_consecutive`, intersected with the window `[a, b)`. -/
theorem append_consecutive_max_min {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) (a b : ℕ) :
    Ico (max n a) (min m b) ++ Ico (max m a) (min l b) = Ico (max n a) (min l b) := by
  simp only [← filter_le, ← filter_lt, ← List.filter_append, append_consecutive hnm hml]

end List.Ico
