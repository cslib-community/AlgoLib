/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Encoding

/-!
# Building certified adjacency lists from undirected edges

An edge is `(label, u, v)`. Distinct labels allow arbitrary parallel edges;
loops contribute two incidences. The builder proves the representation theorem
and the identity `sum of row lengths = 2 * number of labelled edges` once.
Clients neither assume a complexity bound nor manually construct pointer proofs.
-/
namespace AlgoLib.Experimental.RAM.BFS

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
