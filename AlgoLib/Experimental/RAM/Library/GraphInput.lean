/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Library.GraphMemory
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

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


abbrev EdgeData := Nat × Nat × Nat

structure EdgeInput where
  n : Nat
  edges : List EdgeData
  distinct : edges.Nodup
  valid : ∀ e ∈ edges, e.2.1 < n ∧ e.2.2 < n

/-- Retain the entire input edge identifier as its label, so no parallel edge
can be collapsed when constructing the repository's `Graph`. -/
def labelled (e : EdgeData) : Edge Nat EdgeData := ⟨e, s(e.2.1, e.2.2)⟩

theorem labelled_injective : Function.Injective labelled := by
  intro e f h; exact congrArg Edge.endpointsLabel h

def incidences (e : EdgeData) (u : Nat) : List Nat :=
  (if u = e.2.1 then [e.2.2] else []) ++ (if u = e.2.2 then [e.2.1] else [])

@[simp] theorem mem_incidences (e : EdgeData) (u v : Nat) :
    v ∈ incidences e u ↔ (u = e.2.1 ∧ v = e.2.2) ∨ (u = e.2.2 ∧ v = e.2.1) := by
  unfold incidences
  split_ifs <;> simp_all

@[simp] theorem length_incidences (e : EdgeData) (u : Nat) :
    (incidences e u).length = (if u = e.2.1 then 1 else 0) +
      (if u = e.2.2 then 1 else 0) := by
  unfold incidences
  split_ifs <;> simp

/-- Count both ends of every edge, including a loop's two entries. -/
theorem count_incidences (n : Nat) (es : List EdgeData)
    (valid : ∀ e ∈ es, e.2.1 < n ∧ e.2.2 < n) :
    (∑ u ∈ Finset.range n, (es.flatMap (fun e => incidences e u)).length) = 2 * es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := valid e (by simp)
    have ht := ih (fun f hf => valid f (by simp [hf]))
    simp only [List.flatMap_cons, List.length_append, Finset.sum_add_distrib,
      length_incidences, List.length_cons]
    rw [ht]
    simp [he.1, he.2]
    omega

def EdgeInput.graph (input : EdgeInput) : Graph Nat EdgeData where
  vertexSet := {v | v < input.n}
  edgeSet := ↑(input.edges.toFinset.image labelled)
  incidence' := by
    intro e he v hv
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    have h := input.valid f (List.mem_toFinset.mp hf)
    simp only [labelled, Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact h.1
    · exact h.2

def EdgeInput.adjacency (input : EdgeInput) : Adjacency where
  n := input.n
  neighbors u := input.edges.flatMap (fun e => incidences e u)
  valid := by
    intro u _ v hv
    obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hv
    have h := input.valid e he
    rcases (mem_incidences e u v).mp hv with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega

/-- Adjacency-list refinement and the handshaking count are proved, not supplied
as unchecked cost annotations by callers. -/
def EdgeInput.represents (input : EdgeInput) : Represents input.adjacency input.graph where
  vertices _ := Iff.rfl
  adjacency := by
    intro u _ v
    simp only [EdgeInput.adjacency, List.mem_flatMap, mem_incidences,
      Link, EdgeInput.graph, Finset.mem_coe, Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨e, he, h⟩
      refine ⟨labelled e, ⟨e, he, rfl⟩, ?_⟩
      simp only [labelled, Sym2.eq_iff]
      tauto
    · rintro ⟨_, ⟨e, he, rfl⟩, hp⟩
      refine ⟨e, he, ?_⟩
      simp only [labelled, Sym2.eq_iff] at hp
      tauto
  edges := input.edges.toFinset.image labelled
  edgeSet _ := Iff.rfl
  incidenceBound := by
    have h := count_incidences input.n input.edges
      (fun e he => input.valid e he)
    rw [Finset.card_image_of_injective _ labelled_injective]
    simpa [Adjacency.entries, EdgeInput.adjacency,
      List.toFinset_card_of_nodup input.distinct] using h.le

/-- Ready-to-run input with graph and pointer refinements already established. -/
def EdgeInput.fromSource (input : EdgeInput) (source : Nat) (hs : source < input.n) :
    Input input.adjacency input.graph := input.represents.input source hs


end AlgoLib.Experimental.RAM.BFS
