/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Internal.Insertion
import AlgoLib.Experimental.RAM.Paper.Syntax

/-! Public logical API for inserting a value into an adjacent array suffix. -/
namespace AlgoLib.Experimental.RAM.Paper.Insertion

attribute [paper_simps] List.orderedInsert_length

@[paper_simps] theorem insert_requires (s : State) : insertNext.requires s ↔ s.todo ≠ [] := Iff.rfl
@[paper_simps] theorem insert_effect (s : State) : insertNext.effect s = effect s := rfl
@[paper_simps] theorem insert_work (s : State) : insertNext.work s = s.sorted.length + 1 := rfl
@[simp] theorem more_test (s : State) : more.test s = !s.todo.isEmpty := rfl


end AlgoLib.Experimental.RAM.Paper.Insertion
