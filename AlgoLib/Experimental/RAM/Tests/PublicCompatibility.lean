/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Tests.PublicAPI

/-!
# Canonical public aliases preserve existing clients

The public and compatibility spellings denote the same definitions. These checks
require definitional equality, not a separately proved simulation or copied body.
-/
namespace AlgoLib.Experimental.RAM.Tests.PublicCompatibility

example : Language.Program = Prototype.Composition.Program := rfl
example : Language.Contract = Prototype.Composition.Contract := rfl
example : @Verification.Plan = @Prototype.Composition.Plan := rfl
example : Verification.Algorithm = Prototype.Composition.Algorithm := rfl
example : Library.Queue.enqueue = Prototype.Composition.Queue.API.enqueue := rfl
example : Machine.State = Integer.State := rfl
example : Examples.InsertionSort.run = Prototype.Composition.Sorting.run := rfl
example : Examples.BFS.search = Prototype.Composition.BreadthFirst.search := rfl

end AlgoLib.Experimental.RAM.Tests.PublicCompatibility
