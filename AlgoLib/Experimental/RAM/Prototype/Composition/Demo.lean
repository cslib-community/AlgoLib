/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.BufferClient
import AlgoLib.Experimental.RAM.Prototype.Composition.BufferAlgorithms
import AlgoLib.Experimental.RAM.Prototype.Composition.BufferImplementation
import AlgoLib.Experimental.RAM.Prototype.Composition.Execution

/-!
# Execute the same client proof with independently selected buffer implementations

`BufferAlgorithms.recycleVerification` is the algorithm proof: it imports no machine, layout,
or potential. The four combinations of lazy/eager implementations link through
`Linked` instances. Spatial framing and private amortization compose automatically.
Inputs and outputs are ordinary Lean lists. Initial storage is resident, and initial
saved potential is included in the reported bound. No execution fuel is supplied.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Demo
open Checked.Language BufferImplementation

instance bufferDecoder (l : Layout) (eager : Bool) : Decoder (representation l eager) where
  decode s := (List.range (s.vars .word l.lengthVar.name)).map (fun i => s.heap (l.base + i))
  correct xs r s saved h := by
    obtain ⟨_, hv, _⟩ := h
    simp only [hv.2.1]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simpa [getElem!_pos xs i hj] using hv.2.2.1 i hj

abbrev left (capacity : Nat) : Layout := ⟨"left", 0, capacity⟩
abbrev right (capacity : Nat) : Layout := ⟨"right", capacity, capacity⟩

/-- Layout disjointness is proved by the implementation package, not by Buffer clients. -/
theorem separate (capacity : Nat) :
    Disjoint (left capacity).footprint (right capacity).footprint := by
  rw [Finset.disjoint_left]
  intro key hleft hright
  simp only [Layout.footprint, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_range] at hleft hright
  rcases hleft with (rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    rcases hright with (h | h) | ⟨j, hj, h⟩ <;>
    simp_all [Layout.lengthVar, Layout.argumentVar]
  omega

/-- Both inputs are preloaded into disjoint bounded buffers, with zero inactive cells. -/
def encode (capacity : Nat) (xs ys : List Nat) : Store where
  vars ty name := if ty = .word ∧ name = (left capacity).lengthVar.name then xs.length
    else if ty = .word ∧ name = (right capacity).lengthVar.name then ys.length else 0
  heap address := if address < capacity then xs[address]! else ys[address - capacity]!

theorem initial_left (capacity : Nat) (xs ys : List Nat) (bound : xs.length ≤ capacity)
    (eager : Bool) :
    (representation (left capacity) eager).holds xs (left capacity).footprint
      (encode capacity xs ys) (potential eager xs.length) := by
  refine ⟨rfl, ⟨bound, ?_, ?_, ?_⟩, rfl⟩
  · simp [encode, Layout.lengthVar]
  · intro i hi
    simp [encode, left, hi.trans_le bound]
  · intro _ i hi hb
    have hb' : i < capacity := hb
    simp [encode, left, hb', show ¬ i < xs.length by omega]

theorem initial_right (capacity : Nat) (xs ys : List Nat) (bound : ys.length ≤ capacity)
    (eager : Bool) :
    (representation (right capacity) eager).holds ys (right capacity).footprint
      (encode capacity xs ys) (potential eager ys.length) := by
  refine ⟨rfl, ⟨bound, ?_, ?_, ?_⟩, rfl⟩
  · simp [encode, Layout.lengthVar]
  · intro i _
    simp [encode, right, show ¬ capacity + i < capacity by omega]
  · intro _ i hi _
    simp [encode, right, show ¬ capacity + i < capacity by omega,
      show ¬ i < ys.length by omega]

def owned (capacity : Nat) : Footprint := (left capacity).footprint ∪ (right capacity).footprint

theorem initial (capacity : Nat) (xs ys : List Nat) (hx : xs.length ≤ capacity)
    (hy : ys.length ≤ capacity) (eagerLeft eagerRight : Bool) :
    ((representation (left capacity) eagerLeft).sep
      (representation (right capacity) eagerRight)).holds
      (xs, ys) (owned capacity) (encode capacity xs ys)
      (potential eagerLeft xs.length + potential eagerRight ys.length) :=
  ⟨_, _, _, _, separate capacity, rfl, rfl,
    initial_left capacity xs ys hx eagerLeft, initial_right capacity xs ys hy eagerRight⟩

/-- The algorithm proof is unchanged for all four implementation combinations. -/
def execute (eagerLeft eagerRight : Bool) (capacity : Nat) (xs ys : List Nat)
    (hx : xs.length + 2 ≤ capacity) (hy : ys.length + 2 ≤ capacity) :
    Result (List Nat × List Nat) :=
  runProcedure (rate := 24)
    (P := (representation (left capacity) eagerLeft).sep
      (representation (right capacity) eagerRight))
    (Q := (representation (left capacity) eagerLeft).sep
      (representation (right capacity) eagerRight))
    (BufferAlgorithms.recycleProcedure capacity) (xs, ys) ⟨hx, hy, trivial⟩
    (owned capacity) (encode capacity xs ys)
    (potential eagerLeft xs.length + potential eagerRight ys.length)
    (initial capacity xs ys (by omega) (by omega) eagerLeft eagerRight)

/-- The backend derives the public time bound; clients do not specify one. -/
def «time» (eagerLeft eagerRight : Bool) (xs ys : List Nat) : Nat :=
  240 + potential eagerLeft xs.length + potential eagerRight ys.length

theorem correct (eagerLeft eagerRight : Bool) (capacity : Nat) (xs ys : List Nat)
    (hx : xs.length + 2 ≤ capacity) (hy : ys.length + 2 ≤ capacity) :
    (execute eagerLeft eagerRight capacity xs ys hx hy).value = ([], []) ∧
    (execute eagerLeft eagerRight capacity xs ys hx hy).steps ≤
      «time» eagerLeft eagerRight xs ys := by
  have h := runProcedure_correct (rate := 24)
    (P := (representation (left capacity) eagerLeft).sep
      (representation (right capacity) eagerRight))
    (Q := (representation (left capacity) eagerLeft).sep
      (representation (right capacity) eagerRight))
    (BufferAlgorithms.recycleProcedure capacity) (xs, ys) ⟨hx, hy, trivial⟩
    (owned capacity) (encode capacity xs ys)
    (potential eagerLeft xs.length + potential eagerRight ys.length)
    (initial capacity xs ys (by omega) (by omega) eagerLeft eagerRight)
  exact ⟨h.1.1, by simpa only [«time», Nat.add_assoc] using h.2⟩

/-- Observe the untouched second buffer after the first has completed. -/
def executeFramed (eagerLeft eagerRight : Bool) (capacity : Nat) (xs ys : List Nat)
    (hx : xs.length + 2 ≤ capacity) (hy : ys.length ≤ capacity) : Result (List Nat × List Nat) :=
  run (rate := 24)
    (P := (representation (left capacity) eagerLeft).sep
      (representation (right capacity) eagerRight))
    (Q := (representation (left capacity) eagerLeft).sep
      (representation (right capacity) eagerRight))
    (xs, ys) 5 (fun out => out = ([], ys)) (Buffer.recycle_framed capacity 7 8 xs ys hx)
    (owned capacity) (encode capacity xs ys)
    (potential eagerLeft xs.length + potential eagerRight ys.length)
    (initial capacity xs ys (by omega) hy eagerLeft eagerRight)

/-- Execute a client loop containing the implementation's private erase loop. -/
def executeDrain (eager : Bool) (capacity : Nat) (xs : List Nat) (bound : xs.length ≤ capacity) :
    Result (List Nat) :=
  run (rate := 24) (P := representation (left capacity) eager)
    (Q := representation (left capacity) eager) xs 3 (fun out => out = []) (Buffer.drain_vc xs)
    (left capacity).footprint (encode capacity xs []) (potential eager xs.length)
    (initial_left capacity xs [] bound eager)

/-- Appending alone exposes the payload, so clearing cannot conceal a wrong write. -/
def executePush (eager : Bool) (capacity : Nat) (xs : List Nat) (value : Nat)
    (space : xs.length < capacity) : Result (List Nat) :=
  run (rate := 24) (P := representation (left capacity) eager)
    (Q := representation (left capacity) eager) xs 2 (fun out => out = xs ++ [value])
    (p := Buffer.push capacity value) (by simpa [VC, Buffer.argument, Buffer.append] using space)
    (left capacity).footprint (encode capacity xs []) (potential eager xs.length)
    (initial_left capacity xs [] (by omega) eager)

/-- Contract calls inside a conditional inside a loop use the same owned linker. -/
def executeLoop (eagerLeft eagerRight : Bool) (capacity : Nat) (xs ys : List Nat)
    (hx : xs.length ≤ capacity) (hy : ys.length ≤ capacity) : Result (List Nat × List Nat) :=
  runProcedure (rate := 24)
    (P := (representation (left capacity) eagerLeft).sep
      (representation (right capacity) eagerRight))
    (Q := (representation (left capacity) eagerLeft).sep
      (representation (right capacity) eagerRight))
    BufferAlgorithms.clearLeftProcedure (xs, ys) trivial
    (owned capacity) (encode capacity xs ys)
    (potential eagerLeft xs.length + potential eagerRight ys.length)
    (initial capacity xs ys hx hy eagerLeft eagerRight)

end AlgoLib.Experimental.RAM.Prototype.Composition.Demo
