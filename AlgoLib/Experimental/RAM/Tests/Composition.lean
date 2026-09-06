/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Demo
import AlgoLib.Experimental.RAM.Prototype.Composition.Compatibility
import AlgoLib.Experimental.RAM.Prototype.SortingAlgorithm

/-!
# Composition regression suite

Exercise four independently selected buffer implementations, heterogeneous call
arguments/results, loops, both branch arms, disjoint frames, missing implementations,
rejected aliasing, and preservation of an existing sorting proof. Concrete RAM counts
show that eager clearing uses stored potential and does not execute a host effect.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Tests.Composition
open Prototype.Composition Prototype.Composition.BufferImplementation
open Checked.Language (Store)

/-- The old insertion-sort proof transports without any change to its invariants. -/
example (xs : Array Nat) :
    VC (ofProgram Prototype.InsertionSort.insertionSort.body)
      (fun t _ => ∀ out, Prototype.InsertionSort.insertionSort.observes t out →
        Prototype.InsertionSort.insertionSort.ensures xs out)
      (Prototype.InsertionSort.insertionSort.initial xs)
      (Prototype.InsertionSort.insertionSort.credits xs) :=
  reuse_specification _ Prototype.InsertionSort.insertionSortCorrect xs (by trivial)

/-- The logical proof establishes actual Loom WP, with no representation parameters. -/
example (xs : List Nat) (h : xs.length + 2 ≤ 10) :
    _root_.wp (denote (Buffer.recycle 10 7 8) xs) (fun out _ _ => out = []) () 5 :=
  VC.loom _ _ xs 5 (Buffer.recycle_vc 10 7 8 xs h)

/-- Structural linking handles a client loop and both branch arms automatically. -/
example : Linked 24 (representation ⟨"buffer", 0, 10⟩ true)
    (.branch Buffer.nonempty Buffer.drain .identity) (representation ⟨"buffer", 0, 10⟩ true) :=
  inferInstance

def unsupported : Operation (List Nat) (List Nat) := ⟨fun _ => True, id, fun _ => 0⟩

/-- A logical function is not an executable primitive, even in an unchosen branch. -/
example : True := by
  fail_if_success
    have : Linked 24 (representation ⟨"buffer", 0, 10⟩ true)
        (.branch Buffer.nonempty .identity (.invoke unsupported))
        (representation ⟨"buffer", 0, 10⟩ true) := inferInstance
  trivial

/-- Owning a buffer twice is rejected, independently of its payload values. -/
example (l : Layout) (eager : Bool) (xs ys : List Nat) (r : Footprint) (s : Store) (saved : Nat) :
    ¬ ((representation l eager).sep (representation l eager)).holds (xs, ys) r s saved := by
  rintro ⟨r₁, r₂, p₁, p₂, hd, _, _, h₁, h₂⟩
  have hleft : r₁ = l.footprint := h₁.1
  have hright : r₂ = l.footprint := h₂.1
  subst r₁; subst r₂
  exact no_duplicate _ ⟨_, length_owned l⟩ hd

/-- This clear cannot satisfy a per-call constant bound without stored potential. -/
example (n : Nat) (hn : 2 ≤ n) : 24 < 12 * n + 3 := by omega

/-- Logical credit obligations still reject unpaid work. -/
example : ¬ VC (.invoke Buffer.clear) (fun _ _ => True) ([] : List Nat) 0 := by
  simp [VC, Buffer.clear]

set_option linter.hashCommand false in
#eval show IO Unit from do
  for n in List.range 7 do
    for m in List.range 7 do
      let xs := (List.range n).map (fun i => i % 3)
      let ys := (List.range m).map (fun i => (i + 1) % 4)
      for eagerLeft in [false, true] do
        for eagerRight in [false, true] do
          let result := Demo.execute eagerLeft eagerRight (n + m + 2) xs ys (by simp [xs])
            (by simp [ys])
          let expected := 44 + (if eagerLeft then 12 * (n + 2) + 3 else 2) +
            (if eagerRight then 12 * (m + 2) + 3 else 2)
          let framed := Demo.executeFramed eagerLeft eagerRight (n + m + 2) xs ys
            (by simp [xs]) (by simp [ys]; omega)
          unless framed.value == ([], ys) do
            throw <| IO.userError "framing changed an unrelated buffer"
          let pushed := Demo.executePush eagerLeft (n + 1) xs 42 (by simp [xs])
          unless pushed.value == xs ++ [42] && pushed.steps == 11 do
            throw <| IO.userError "typed append did not preserve its payload"
          let drained := Demo.executeDrain eagerLeft n xs (by simp [xs])
          let drainCost := if n == 0 then 3 else 6 + (if eagerLeft then 12 * n + 3 else 2)
          unless drained.value == [] && drained.steps == drainCost do
            throw <| IO.userError "nested client/implementation loop failed"
          unless result.value == ([], []) do
            throw <| IO.userError "composed buffers: wrong mathematical output"
          unless result.steps == expected do
            throw <| IO.userError s!"buffers: expected {expected}, got {result.steps}"
          unless result.steps ≤ 240 + potential eagerLeft n + potential eagerRight m do
            throw <| IO.userError "composed buffers: resource bound violated"

end AlgoLib.Experimental.RAM.Tests.Composition
