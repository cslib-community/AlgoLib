/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Program
import Mathlib.Data.Nat.Pairing

/-!
# A reusable input encoder

Clients provide adjacency lists, not pointer proofs. Pairing a vertex identifier
with a row index assigns a distinct positive address to every adjacency entry.
The encoder and graph validation are outside the RAM routine, just as loading
an adjacency-list input is outside a textbook BFS's running time. BFS itself
clears its flags, initializes its FIFO, and traverses this encoded input.
-/
namespace AlgoLib.Experimental.RAM.BFS

/-- Zero terminates a row; all actual adjacency nodes have positive pointers. -/
def Adjacency.pointer (a : Adjacency) (v i : Nat) : Nat :=
  if i < (a.neighbors v).length then Nat.pair v i + 1 else 0

/-- Input materialization. Mutable cells deliberately start with junk: the
algorithm must initialize its own flags and live queue cells. -/
def Adjacency.encode (a : Adjacency) (address : Nat) : Nat :=
  let slot := address / 5
  let arc := Nat.unpair (slot - 1)
  match address % 5 with
  | 0 => a.pointer slot 0
  | 1 => 97
  | 2 => 89
  | 3 => (a.neighbors arc.1)[arc.2]?.getD 0
  | _ => a.pointer arc.1 (arc.2 + 1)

@[simp] theorem encode_head (a : Adjacency) (v : Nat) :
    a.encode (5 * v) = a.pointer v 0 := by simp [Adjacency.encode, Nat.mul_comm]

private theorem encode_destination (a : Adjacency) (v i : Nat)
    (hi : i < (a.neighbors v).length) :
    a.encode (5 * a.pointer v i + 3) = (a.neighbors v)[i] := by
  simp [Adjacency.encode, Adjacency.pointer, hi, Nat.add_div, Nat.mul_comm]

private theorem encode_next (a : Adjacency) (v i : Nat)
    (hi : i < (a.neighbors v).length) :
    a.encode (5 * a.pointer v i + 4) = a.pointer v (i + 1) := by
  simp [Adjacency.encode, Adjacency.pointer, hi, Nat.add_div, Nat.mul_comm]

/-- Representation refinement: decoding an encoded row returns that exact row. -/
theorem Adjacency.encode_chain (a : Adjacency) (v i : Nat) :
    Chain a.encode (a.pointer v i) ((a.neighbors v).drop i) := by
  generalize hn : (a.neighbors v).length - i = n
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih =>
    by_cases hi : i < (a.neighbors v).length
    · rw [List.drop_eq_getElem_cons hi]
      refine ⟨by simp [Adjacency.pointer, hi], encode_destination a v i hi, ?_⟩
      rw [encode_next a v i hi]
      exact ih _ (by omega) (i + 1) rfl
    · have hdrop : (a.neighbors v).drop i = [] := List.drop_eq_nil_of_le (by omega)
      simp [hdrop, Chain, Adjacency.pointer, hi]

theorem Adjacency.encode_heap (a : Adjacency) : Heap a a.encode := by
  intro v _
  rw [encode_head]
  simpa using a.encode_chain v 0

/-- The input constructor hides all pointer-layout details from algorithm users. -/
def Represents.input {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) (source : Nat) (hs : source < a.n) : Input a G where
  representation := rep
  source := source
  source_valid := hs
  memory := a.encode
  heap := a.encode_heap

end AlgoLib.Experimental.RAM.BFS
