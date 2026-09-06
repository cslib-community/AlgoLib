/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst
import AlgoLib.Experimental.RAM.Prototype.Composition.BFSStorage
import AlgoLib.Experimental.RAM.Prototype.Composition.Assembly

/-!
# Execute one verified BFS with either FIFO backend

The algorithm certificate is BreadthFirst.bfsProcedure in both cases. Linking
reconstructs memory framing, procedure implementation certificates, private
potential accounting, and RAM compilation. No source proof is repeated here.
An arena fixes capacity and allocation independently of graph contents.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst
open Experimental.RAM.BFS BFSStorage Checked.Language

private abbrev scratch := local_storage% "bfs.locals" : bfsLocals

private def encoder (kind : FIFO) (a : Adjacency) (base capacity : Nat)
    (fits : GraphCursorImplementation.extent a ≤ base) :=
  (resident kind a base capacity fits).hide scratch
    (by simp [scratch, Encoder.sep, scalarEncoder]) (by
      cases kind <;>
        simp [resident, GraphCursorImplementation.encoder, GraphCursorImplementation.footprint,
          state, bitmap, fifo, queueEncoder, source, QueueRing.encoder,
          QueueRing.Layout.footprint, QueueRing.Layout.head, QueueRing.Layout.length,
          QueueStacksImplementation.encoder, QueueStacksImplementation.concreteEncoder,
          Encoder.sep, BufferImplementation.encoder, BufferImplementation.Layout.footprint,
          BufferImplementation.Layout.lengthVar, BufferImplementation.Layout.argumentVar,
          scalarEncoder, arrayEncoder, Storage.ArrayLayout.footprint, scratch,
          Finset.disjoint_left]
      all_goals intro location owned
      all_goals cases location <;> simp_all [GraphCursorImplementation.no_register])

set_option maxHeartbeats 2000000 in
-- Reconstruct the structural certificate for the complete nested-loop client.
@[reducible] private def linked (kind : FIFO) (a : Adjacency) (base capacity : Nat)
    (fits : GraphCursorImplementation.extent a ≤ base)
    (β : Type) (G : Graph Nat β) (rep : Represents a G) :
    Linked 24 (encoder kind a base capacity fits).representation
      (bfsProcedure β a G rep capacity).body
      (encoder kind a base capacity fits).representation := by
  unfold encoder resident state fifo
  ram_link

set_option maxHeartbeats 2000000 in
-- Erase certificates before comparing code; algorithm proofs are not involved.
/-- Compiled code is fixed once the FIFO backend and arena are chosen. -/
theorem code_independent (kind : FIFO) (base capacity : Nat)
    (a b : Adjacency) (fitsA : GraphCursorImplementation.extent a ≤ base)
    (fitsB : GraphCursorImplementation.extent b ≤ base)
    (β γ : Type) (G : Graph Nat β) (H : Graph Nat γ)
    (repA : Represents a G) (repB : Represents b H) :
    (linked kind a base capacity fitsA β G repA).supported.compile.code =
      (linked kind b base capacity fitsB γ H repB).supported.compile.code := by
  rw [Supported.compile_code, Supported.compile_code]
  cases kind <;> ram_code_eq

/-- Only the backend arena and FIFO implementation configure the executable. -/
def runIn (kind : FIFO) (a : Adjacency) (base capacity : Nat)
    (fits : GraphCursorImplementation.extent a ≤ base) (space : a.n ≤ capacity)
    (β : Type) (G : Graph Nat β) (rep : Represents a G) (s : Fin a.n) : Result (Array Nat) :=
  letI := linked kind a base capacity fits β G rep
  let input := ([], Array.replicate a.n 97, [], s.val)
  let result := runEncoded (rate := 24) (bfsProcedure β a G rep capacity)
    (encoder kind a base capacity fits) input
    (by simpa [input] using space)
    (by cases kind <;> simpa [input, encoder, resident, state, fifo, bitmap, source,
          Encoder.hide, Encoder.sep, arrayEncoder, scalarEncoder,
          GraphCursorImplementation.encoder, queueEncoder, QueueRing.encoder,
          QueueStacksImplementation.encoder] using space)
  ⟨result.value.2.1, result.steps⟩

/-- Computed from source annotations; no RAM constant is supplied by the BFS author. -/
def bound (β : Type) (a : Adjacency) (G : Graph Nat β) (rep : Represents a G)
    (capacity source : Nat) : Nat :=
  24 * (bfsProcedure β a G rep capacity).credits ([], Array.replicate a.n 97, [], source)

/-- The exact RAM runner satisfies the graph specification and inferred bound together. -/
theorem runIn_correct (kind : FIFO) (a : Adjacency) (base capacity : Nat)
    (fits : GraphCursorImplementation.extent a ≤ base) (space : a.n ≤ capacity)
    (β : Type) (G : Graph Nat β) (rep : Represents a G) (s : Fin a.n) :
    (∀ v, v ∈ BFSFacts.marked (runIn kind a base capacity fits space β G rep s).value ↔
      Reachable G s.val v) ∧
      (runIn kind a base capacity fits space β G rep s).steps ≤ bound β a G rep capacity s.val := by
  letI := linked kind a base capacity fits β G rep
  have h := runEncoded_correct (rate := 24) (bfsProcedure β a G rep capacity)
    (encoder kind a base capacity fits) ([], Array.replicate a.n 97, [], s.val)
    (by simpa using space)
    (by cases kind <;> simpa [encoder, resident, state, fifo, bitmap, source,
          Encoder.hide, Encoder.sep, arrayEncoder, scalarEncoder,
          GraphCursorImplementation.encoder, queueEncoder, QueueRing.encoder,
          QueueStacksImplementation.encoder] using space)
  refine ⟨h.1.1, ?_⟩
  have saved : (encoder kind a base capacity fits).saved
      ([], Array.replicate a.n 97, [], s.val) = 0 := by cases kind <;> rfl
  simpa only [bound, saved, Nat.add_zero] using h.2

/-- Normalizing the inferred expression exposes the linear polynomial. -/
theorem bound_eq (β : Type) (a : Adjacency) (G : Graph Nat β) (rep : Represents a G)
    (capacity source : Nat) :
    bound β a G rep capacity source = 1224 * a.n + 888 * a.entries + 1224 := by
  simp [bound, UniformCredits.amount, Value.credits, Locals.credits]
  ring

/-- Ordinary graph/source interface; queue selection never changes the source proof. -/
def search (kind : FIFO) (input : EdgeInput) (s : Fin input.n) : Result (Finset Nat) :=
  let r := runIn kind input.adjacency (GraphCursorImplementation.extent input.adjacency)
    input.n (Nat.le_refl _) (Nat.le_refl _) EdgeData input.graph input.represents s
  ⟨BFSFacts.marked r.value, r.steps⟩

theorem search_correct (kind : FIFO) (input : EdgeInput) (s : Fin input.n) :
    ∀ v, v ∈ (search kind input s).value ↔ Reachable input.graph s.val v :=
  (runIn_correct kind input.adjacency (GraphCursorImplementation.extent input.adjacency)
    input.n (Nat.le_refl _) (Nat.le_refl _) EdgeData input.graph input.represents s).1

/-- Valid sources exclude the empty graph, matching the specification's connectivity convention. -/
theorem connected (kind : FIFO) (input : EdgeInput) (s : Fin input.n) :
    Connected input.graph ↔ (search kind input s).value = Finset.range input.n := by
  have all := visits_all_iff_connected ((input.represents.vertices s.val).mpr s.isLt)
    (search_correct kind input s)
  constructor
  · intro h
    ext v
    constructor
    · intro hv
      have hv := ((search_correct kind input s v).mp hv).right_mem
      exact Finset.mem_range.mpr ((input.represents.vertices v).mp hv)
    · intro hv
      exact all.mpr h v ((input.represents.vertices v).mpr (Finset.mem_range.mp hv))
  · intro h
    apply all.mp
    intro v hv
    rw [h]
    exact Finset.mem_range.mpr ((input.represents.vertices v).mp hv)

/-- Linear in vertices plus labelled edges, including loops and parallel edges. -/
theorem linear (kind : FIFO) (input : EdgeInput) (s : Fin input.n) :
    (search kind input s).steps ≤ 2448 * (input.n + input.edges.length) := by
  have h := (runIn_correct kind input.adjacency
    (GraphCursorImplementation.extent input.adjacency) input.n
    (Nat.le_refl _) (Nat.le_refl _) EdgeData input.graph input.represents s).2
  rw [bound_eq] at h
  have incidence := input.represents.incidenceBound
  have positive : 0 < input.n := Nat.zero_lt_of_lt s.isLt
  simp only [EdgeInput.represents, Finset.card_image_of_injective _ labelled_injective,
    List.toFinset_card_of_nodup input.distinct] at incidence
  change (search kind input s).steps ≤ 1224 * input.n +
    888 * input.adjacency.entries + 1224 at h
  omega

/-- The representation-independent result is a genuine substitution theorem. -/
theorem same_result (input : EdgeInput) (s : Fin input.n) :
    (search .circular input s).value = (search .twoStacks input s).value := by
  ext v
  exact (search_correct .circular input s v).trans (search_correct .twoStacks input s v).symm

end AlgoLib.Experimental.RAM.Prototype.Composition.BreadthFirst
