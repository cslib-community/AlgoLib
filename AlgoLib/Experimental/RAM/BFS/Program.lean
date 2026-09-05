/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Algorithm

/-!
# The complete BFS program

Initialization and the public correctness, connectivity, and time contracts.
-/

namespace AlgoLib.Experimental.RAM.BFS
open Checked Checked.Source

abbrev size : Reg := .limit

def clearBody : Stmt := imperative {
  addr := 5 * head;
  addr := addr + 1;
  A[addr] := 0;
  head := head + 1;
}

def clearTest : Test := .lt (.reg head) (.reg size)
def clearCode : Code := .while clearTest clearBody.compile

private def cleared (s : State) : State := block [
  .assign addr (.bin .mul (.lit 5) (.reg head)),
  .assign addr (.bin .add (.reg addr) (.lit 1)),
  .store (.reg addr) (.lit 0),
  .assign head (.bin .add (.reg head) (.lit 1))] s

private theorem clear_correct (s : State) : Exec clearBody.compile s 4 (cleared s) ∧
    (cleared s).regs head = s.regs head + 1 ∧
    (cleared s).regs size = s.regs size ∧
    (cleared s).regs vertex = s.regs vertex ∧
    (cleared s).memory = Function.update s.memory (5 * s.regs head + 1) 0 := by
  refine ⟨(Eval.block _ s).compile, ?_, ?_, ?_, ?_⟩ <;>
    simp [cleared, block, Simple.eval, Expr.eval, State.set, Operand.eval, BinOp.eval,
      head, size, addr, vertex]

/-- The initialization VCs include clearing every flag; zeroed scratch memory is
not an assumption on the caller. Queue cells are initialized when enqueued. -/
theorem clear_vc (n source : Nat) (m : Memory) :
    LoopVC clearTest clearBody.compile
      (fun j s => s.regs head = j ∧ j ≤ n ∧ s.regs size = n ∧ s.regs vertex = source ∧
        GraphFrame m s.memory ∧ ∀ v < j, s.memory (5 * v + 1) = 0)
      (fun j => 5 * (n - j))
      (fun s => s.regs size = n ∧ s.regs vertex = source ∧ GraphFrame m s.memory ∧
        ∀ v < n, s.memory (5 * v + 1) = 0) := by
  vcgen
  · rintro j s ⟨hj, hjn, hn, hs, hf, hz⟩ hq
    have : ¬ j < n := by simpa [clearTest, Test.eval, Operand.eval, hj, hn] using hq
    have : j = n := by omega
    exact ⟨hn, hs, hf, this ▸ hz⟩
  · rintro j s ⟨hj, hjn, hn, hs, hf, hz⟩ hq
    have hjlt : j < n := by simpa [clearTest, Test.eval, Operand.eval, hj, hn] using hq
    obtain ⟨hx, hh, hn', hs', hm⟩ := clear_correct s
    refine ⟨j + 1, 4, cleared s, hx, ?_, by omega⟩
    refine ⟨hh.trans (by omega), by omega, hn'.trans hn, hs'.trans hs, ?_, ?_⟩
    · rw [hm]; exact hf.trans (graphFrame_write _ _ 0 1 (Or.inl rfl))
    · intro v hv
      rw [hm, hj]
      by_cases h : v = j
      · subst v; simp
      · rw [Function.update_of_ne (by omega)]
        exact hz v (by omega)

/-- Put the source in the FIFO and mark it before entering the BFS loop. -/
def seed : Stmt := imperative {
  addr := 5 * vertex;
  addr := addr + 1;
  A[addr] := 1;
  A[2] := vertex;
  head := 0;
  tail := 1;
}

private def seeded (s : State) : State := block [
  .assign addr (.bin .mul (.lit 5) (.reg vertex)),
  .assign addr (.bin .add (.reg addr) (.lit 1)),
  .store (.reg addr) (.lit 1),
  .store (.lit 2) (.reg vertex),
  .assign head (.atom (.lit 0)),
  .assign tail (.atom (.lit 1))] s

private theorem seed_correct (s : State) : Exec seed.compile s 6 (seeded s) ∧
    (seeded s).regs head = 0 ∧ (seeded s).regs tail = 1 ∧
    (seeded s).memory = enqueueMemory s.memory (s.regs vertex) 0 := by
  refine ⟨(Eval.block _ s).compile, ?_, ?_, ?_⟩ <;>
    simp [seeded, block, Simple.eval, Expr.eval, State.set, Operand.eval, BinOp.eval,
      head, tail, addr, vertex, enqueueMemory]

/-- One fixed RAM program, independent of graph size, source, and input contents. -/
def bfsCode : Code := .seq (.block [.mov head (.lit 0)])
  (.seq clearCode (.seq seed.compile bfsLoop))

/-- Textbook source. The three loops are verified modularly by `clear_vc`,
`scan_correct`, and `bfs_vc`; ghost sets, lists, and credits stay in those proofs. -/
def bfsSource : Stmt := imperative {
  head := 0;
  while head < size {
    call clearBody;
  }
  call seed;
  while head < tail {
    call popBody;
    while ptr > 0 {
      call scanBody;
    }
  }
}

theorem bfsSource_compiles : bfsSource.compile = bfsCode := rfl

/-- The complete uniform algorithm: actual RAM execution, exact reachability,
and a linear bound including flag initialization. `n` is the number of vertices
and `m` is the number of labelled edges, including parallel edges. -/
theorem bfs_correct {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) (source : Nat) (hs : source < a.n) (s : State)
    (hn : s.regs size = a.n) (hsource : s.regs vertex = source) (heap : Heap a s.memory) :
    ∃ k t, Exec bfsCode s k t ∧
      ReturnsReachable G source (fun v => v < a.n ∧ t.memory (5 * v + 1) = 1) ∧
      k ≤ 13 * a.n + 32 * rep.edges.card + 9 := by
  let z := s.set head 0
  have hz : z.regs head = 0 := by simp [z, State.set]
  have hzn : z.regs size = a.n := by simpa [z, State.set, size, head] using hn
  have hzs : z.regs vertex = source := by simpa [z, State.set, vertex, head] using hsource
  obtain ⟨i, u, hu, ⟨hun, hus, hf, hzero⟩, hi⟩ := (clear_vc a.n source s.memory).sound
    (g := 0) (s := z) ⟨hz, by omega, hzn, hzs, .refl _, by simp⟩
  obtain ⟨he, hh, ht, hm⟩ := seed_correct u
  have hview : View a.n (seeded u).memory (discovered ∅ [source]) [source]
      ((seeded u).regs head) := by
    have emptyView : View a.n u.memory ∅ [] 0 := ⟨by simpa using hzero, by simp⟩
    simpa [hm, hh, hus, discovered] using emptyView.enqueue (v := source)
  have hinv : Invariant a G source ∅ [source] := by
    refine ⟨by simp, by simp, by simp, ?_, by simp, ?_, by simp⟩
    · intro v hv; simpa using (List.mem_singleton.mp hv ▸ hs)
    · intro v hv
      have : v = source := by simpa using hv
      subst v
      exact .refl ((rep.vertices source).mpr hs)
  have hrep : LoopRep a G source (∅, [source]) (seeded u) := by
    refine ⟨hinv, ?_, hview, by simp [hh, ht]⟩
    rw [hm, hus]
    exact (heap.frame hf).frame (enqueue_frame _ _ _)
  obtain ⟨j, t, hj, hQ, hjcost⟩ := bfs_loop_correct rep hrep
  refine ⟨1 + (i + (6 + j)), t, .seq (.block _ s) (.seq hu (.seq he hj)), hQ, ?_⟩
  simp only [Nat.sub_zero] at hi
  omega

/-- A valid input to the machine. Proof fields are erased by Lean's evaluator. -/
structure Input {β : Type*} (a : Adjacency) (G : Graph Nat β) where
  representation : Represents a G
  source : Nat
  source_valid : source < a.n
  memory : Memory
  heap : Heap a memory

def Input.initial {β : Type*} {a : Adjacency} {G : Graph Nat β} (input : Input a G) : State where
  regs r := if r = size then a.n else if r = vertex then input.source else 0
  memory := input.memory

/-- No fuel, and no extra termination argument at a call site. -/
def Input.run {β : Type*} {a : Adjacency} {G : Graph Nat β} (input : Input a G) : Nat × State :=
  Checked.run bfsCode input.initial (by
    obtain ⟨k, t, hx, _⟩ := bfs_correct input.representation input.source input.source_valid
      input.initial (by simp [Input.initial])
      (by simp [Input.initial, vertex, size]) input.heap
    exact ⟨k, t, hx⟩)

theorem Input.correct {β : Type*} {a : Adjacency} {G : Graph Nat β} (input : Input a G) :
    Exec bfsCode input.initial input.run.1 input.run.2 ∧
    ReturnsReachable G input.source (fun v => v < a.n ∧ input.run.2.memory (5 * v + 1) = 1) ∧
    input.run.1 ≤ 13 * a.n + 32 * input.representation.edges.card + 9 := by
  obtain ⟨k, t, hx, hQ, hk⟩ := bfs_correct input.representation input.source input.source_valid
    input.initial (by simp [Input.initial])
    (by simp [Input.initial, vertex, size]) input.heap
  have he : input.run = (k, t) := Checked.run_eq hx _
  rw [he]
  exact ⟨hx, hQ, hk⟩

/-- The same result and exact cost satisfy the independent source semantics. -/
theorem Input.source_correct {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (input : Input a G) : Eval bfsSource input.initial input.run.1 input.run.2 :=
  Eval.of_compile (by rw [bfsSource_compiles]; exact input.correct.1)

/-- A uniform linear upper bound, since a valid source guarantees `n ≥ 1`. -/
theorem Input.linear {β : Type*} {a : Adjacency} {G : Graph Nat β} (input : Input a G) :
    input.run.1 ≤ 32 * (a.n + input.representation.edges.card) := by
  have := input.correct.2.2
  have := input.source_valid
  omega

/-- The public connectivity theorem: reaching all vertices characterizes
connectedness. BFS correctness itself does not require connectedness. -/
theorem Input.connected_iff {β : Type*} {a : Adjacency} {G : Graph Nat β} (input : Input a G) :
    (∀ v < a.n, input.run.2.memory (5 * v + 1) = 1) ↔ Connected G := by
  have hc := visits_all_iff_connected
    ((input.representation.vertices input.source).mpr input.source_valid) input.correct.2.1
  constructor
  · intro h
    exact hc.mp (fun v hv => ⟨(input.representation.vertices v).mp hv,
      h v ((input.representation.vertices v).mp hv)⟩)
  · intro h v hv
    exact (hc.mpr h v ((input.representation.vertices v).mpr hv)).2

end AlgoLib.Experimental.RAM.BFS
