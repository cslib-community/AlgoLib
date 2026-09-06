/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Adapters.Insertion
import AlgoLib.Experimental.RAM.Backend.Adapters.InsertionInput
import AlgoLib.Experimental.RAM.Authoring.Methods

/-!
# Public insertion contracts

Use insertNext, more, initial, and interface when proving a client over an array prefix and sorted
suffix. This module is the only insertion-library import a program needs.

The backend proves physical memory preservation and cost. The equations here let symbolic
execution expose only requires, effect, work, and logical input/output facts.

## Further details

Public logical API for inserting a value into an adjacent array suffix.
-/
namespace AlgoLib.Experimental.RAM.Authoring.Insertion

attribute [paper_simps] List.orderedInsert_length

@[paper_simps] theorem insert_requires (s : State) : insertNext.requires s ↔ s.todo ≠ [] := Iff.rfl
@[paper_simps] theorem insert_effect (s : State) : insertNext.effect s = effect s := rfl
@[paper_simps] theorem insert_work (s : State) : insertNext.work s = s.sorted.length + 1 := rfl
@[simp] theorem more_test (s : State) : more.test s = !s.todo.isEmpty := rfl


/-- Stable logical initial-state equation for method verification. -/
@[method_simps] theorem input_state (xs : List Nat) : interface.initial xs = initial xs := rfl

/-- Stable logical meaning of the returned array; no address appears in clients. -/
@[method_simps] theorem output_view (s : State) (out : List Nat) :
    interface.Observes s out ↔ out = s.todo.reverse ++ s.sorted := Iff.rfl

/-- Certified preparation cost, used by automatic method payment. -/
@[method_simps] theorem preparation_work (xs : List Nat) : interface.preparationCost xs = 5 := rfl

/-- Certified implementation overhead, used by automatic method payment. -/
@[method_simps] theorem implementation_work : model.overhead = 50 := rfl

/-- Normalize the backend's inferred bound for the standard insertion credit budget. -/
theorem quadratic_of_credits (xs : List Nat) {steps : Nat}
    (h : steps ≤ interface.preparationCost xs +
      model.overhead * (xs.length * (xs.length + 2) + 1)) :
    steps ≤ 50 * xs.length ^ 2 + 100 * xs.length + 55 := by
  simp only [preparation_work, implementation_work] at h
  nlinarith

end AlgoLib.Experimental.RAM.Authoring.Insertion
