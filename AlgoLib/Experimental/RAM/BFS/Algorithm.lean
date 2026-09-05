/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.BFS.Scan
import Mathlib.Tactic

/-!
# BFS, in the order of the textbook proof

1. Scanning a row discovers exactly its previously unseen neighbors.
2. Mark-before-enqueue preserves uniqueness and the reachability invariant.
3. Each vertex is dequeued once; its row is scanned once.
4. The potential pays for all actual RAM operations.
5. An empty FIFO turns edge closure into completeness by induction on a walk.
-/
namespace AlgoLib.Experimental.RAM.BFS
open Checked Checked.Source

@[simp] theorem scan_seen (xs : List Nat) (seen : Finset Nat) (queue : List Nat) (v : Nat) :
    v ∈ (scan xs seen queue).1 ↔ v ∈ seen ∨ v ∈ xs := by
  induction xs generalizing seen queue with
  | nil => simp [scan]
  | cons u us ih =>
    simp only [scan]
    rw [ih]
    by_cases hu : u ∈ seen <;> simp [discover, hu] <;> aesop

@[simp] theorem scan_queue (xs : List Nat) (seen : Finset Nat) (queue : List Nat) (v : Nat) :
    v ∈ (scan xs seen queue).2 ↔ v ∈ queue ∨ (v ∈ xs ∧ v ∉ seen) := by
  induction xs generalizing seen queue with
  | nil => simp [scan]
  | cons u us ih =>
    simp only [scan]
    rw [ih]
    by_cases hu : u ∈ seen
    · simp only [discover, if_pos hu, List.mem_cons]
      constructor
      · tauto
      · rintro (h | ⟨h | h, hn⟩)
        · exact Or.inl h
        · subst v; contradiction
        · exact Or.inr ⟨h, hn⟩
    · simp only [discover, if_neg hu, List.mem_append,
        Finset.mem_insert, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h | h) | ⟨h, hn⟩)
        · exact Or.inl h
        · subst v; exact Or.inr ⟨Or.inl rfl, hu⟩
        · exact Or.inr ⟨Or.inr h, fun hv => hn (Or.inr hv)⟩
      · tauto

theorem scan_distinct (xs : List Nat) (seen : Finset Nat) (queue : List Nat)
    (hq : queue.Nodup) (hqseen : ∀ v ∈ queue, v ∈ seen) : (scan xs seen queue).2.Nodup := by
  induction xs generalizing seen queue with
  | nil => exact hq
  | cons v vs ih =>
    simp only [scan]
    by_cases hv : v ∈ seen
    · simpa [discover, hv] using ih seen queue hq hqseen
    · simp only [discover, if_neg hv]
      apply ih
      · have hvq : v ∉ queue := fun h => hv (hqseen v h)
        simpa using hq.append (List.nodup_singleton v) (List.disjoint_singleton.mpr hvq)
      · intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact Finset.mem_insert_of_mem (hqseen w hw)
        · exact Finset.mem_insert_self _ _

/-- Discovered vertices are the processed vertices together with the FIFO. -/
def discovered (done : Finset Nat) (queue : List Nat) : Finset Nat := done ∪ queue.toFinset

@[simp] theorem mem_discovered {done : Finset Nat} {queue : List Nat} {v : Nat} :
    v ∈ discovered done queue ↔ v ∈ done ∨ v ∈ queue := by simp [discovered]

/-- Maintenance of the mathematical invariant, independently of memory layout. -/
theorem Invariant.process {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) {source u : Nat} {done : Finset Nat} {queue : List Nat}
    (h : Invariant a G source done (u :: queue)) :
    let result := scan (a.neighbors u) (discovered done (u :: queue)) queue
    result.1 = discovered (insert u done) result.2 ∧
      Invariant a G source (insert u done) result.2 := by
  dsimp only
  have hu : u < a.n := h.valid_queue u (by simp)
  have hud : u ∉ done := h.disjoint u (by simp)
  have hqu : u ∉ queue := (List.nodup_cons.mp h.distinct).1
  have hq := h.distinct.of_cons
  have heq : (scan (a.neighbors u) (discovered done (u :: queue)) queue).1 =
      discovered (insert u done) (scan (a.neighbors u) (discovered done (u :: queue)) queue).2 := by
    ext v
    simp only [scan_seen, mem_discovered, scan_queue, Finset.mem_insert, List.mem_cons]
    tauto
  refine ⟨heq, ?_⟩
  constructor
  · exact scan_distinct _ _ _ hq (fun v hv => by simp [hv])
  · intro v hv hd
    rw [scan_queue] at hv
    rcases hv with hv | ⟨_, hn⟩
    · rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hqu hv
      · exact h.disjoint v (by simp [hv]) hd
    · apply hn
      simp only [mem_discovered, List.mem_cons]
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hd
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hu
    · exact h.valid_done v hv
  · intro v hv
    rcases (scan_queue _ _ _ _).mp hv with hv | ⟨hv, _⟩
    · exact h.valid_queue v (by simp [hv])
    · exact a.valid u hu v hv
  · have hs : source ∈ (scan (a.neighbors u) (discovered done (u :: queue)) queue).1 :=
      (scan_seen _ _ _ _).mpr (Or.inl (mem_discovered.mpr h.source_seen))
    simpa [heq] using hs
  · intro v hv
    have hs : v ∈ (scan (a.neighbors u) (discovered done (u :: queue)) queue).1 := by
      rw [heq]; exact mem_discovered.mpr hv
    rcases (scan_seen _ _ _ _).mp hs with hs | hs
    · exact h.sound v (mem_discovered.mp hs)
    · exact .step (h.sound u (by simp)) ((rep.adjacency u hu v).mp hs)
  · intro v hv w hw
    have hs : w ∈ (scan (a.neighbors u) (discovered done (u :: queue)) queue).1 := by
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (scan_seen _ _ _ _).mpr (Or.inr hw)
      · exact (scan_seen _ _ _ _).mpr (Or.inl (mem_discovered.mpr (h.closed v hv w hw)))
    simpa [heq] using hs

/-- Charge each unprocessed vertex for its dequeue, guards, and adjacency scan. -/
def potential (a : Adjacency) (done : Finset Nat) : Nat :=
  ∑ v ∈ Finset.range a.n \ done, (8 + 16 * (a.neighbors v).length)

theorem potential_process (a : Adjacency) (done : Finset Nat) {u : Nat}
    (hu : u < a.n) (hud : u ∉ done) :
    potential a (insert u done) + (8 + 16 * (a.neighbors u).length) = potential a done := by
  have he : Finset.range a.n \ insert u done = (Finset.range a.n \ done).erase u := by
    ext v; simp; tauto
  unfold potential
  rw [he]
  exact Finset.sum_erase_add _ _ (by simp [hu, hud])

theorem potential_initial (a : Adjacency) : potential a ∅ = 8 * a.n + 16 * a.entries := by
  simp [potential, Adjacency.entries, Finset.sum_add_distrib, Finset.mul_sum,
    Nat.mul_comm]

/-- Ghost data at the outer loop header. -/
abbrev Frontier := Finset Nat × List Nat

def LoopRep {β : Type*} (a : Adjacency) (G : Graph Nat β) (source : Nat)
    (g : Frontier) (s : State) : Prop :=
  Invariant a G source g.1 g.2 ∧ Heap a s.memory ∧
  View a.n s.memory (discovered g.1 g.2) g.2 (s.regs head) ∧
  s.regs tail = s.regs head + g.2.length

private def popped (s : State) : State :=
  block [
    .assign addr (.bin .mul (.lit 5) (.reg head)),
    .assign addr (.bin .add (.reg addr) (.lit 2)),
    .assign vertex (.load (.reg addr)),
    .assign head (.bin .add (.reg head) (.lit 1)),
    .assign addr (.bin .mul (.lit 5) (.reg vertex)),
    .assign ptr (.load (.reg addr))] s

private theorem pop_correct (s : State) :
    Exec popBody.compile s 6 (popped s) ∧
    (popped s).memory = s.memory ∧
    (popped s).regs head = s.regs head + 1 ∧
    (popped s).regs tail = s.regs tail ∧
    (popped s).regs ptr = s.memory (5 * s.memory (5 * s.regs head + 2)) := by
  refine ⟨(Eval.block _ s).compile, rfl, ?_, ?_, ?_⟩ <;>
    simp [popped, block, Simple.eval, Expr.eval, State.set, Operand.eval, BinOp.eval,
      head, tail, addr, vertex, ptr]

/-- Generated loop VCs for both reachability and running time. The proof only
uses the row-scan contract, the graph invariant, and one potential identity. -/
theorem bfs_vc {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) (source : Nat) :
    LoopVC bfsTest bfsBody (LoopRep a G source) (fun g => potential a g.1)
      (fun s => ReturnsReachable G source (fun v => v < a.n ∧ s.memory (5 * v + 1) = 1)) := by
  vcgen
  · intro g s h hstop
    obtain ⟨hi, _, hv, ht⟩ := h
    have hnil : g.2 = [] := by
      have : ¬ s.regs head < s.regs tail := by simpa [bfsTest, Test.eval, Operand.eval] using hstop
      have : g.2.length = 0 := by omega
      exact List.eq_nil_of_length_eq_zero this
    have hc := (hnil ▸ hi).exit rep
    intro v
    constructor
    · rintro ⟨hvn, hmark⟩
      apply (hc v).mp
      have := hv.marks v hvn
      simp [hnil] at this
      split_ifs at this with hm
      · exact hm
      · omega
    · intro hr
      have hd := (hc v).mpr hr
      have hvn := hi.valid_done v hd
      exact ⟨hvn, by simpa [hnil, hd] using hv.marks v hvn⟩
  · rintro ⟨done, queue⟩ s ⟨hi, heap, view, ht⟩ hgo
    cases queue with
    | nil => simp [bfsTest, Test.eval, Operand.eval, ht] at hgo
    | cons u queue =>
      have hu := hi.valid_queue u (by simp)
      have hud := hi.disjoint u (by simp)
      have hslot : s.memory (5 * s.regs head + 2) = u := by simpa using view.slots 0 u rfl
      obtain ⟨hx, hm, hh, htail, hp⟩ := pop_correct s
      have hchain : Chain (popped s).memory ((popped s).regs ptr) (a.neighbors u) := by
        rw [hp, hm, hslot]; exact heap u hu
      have hview : View a.n (popped s).memory (discovered done (u :: queue)) queue
          ((popped s).regs head) := by rw [hm, hh]; exact view.pop
      have htt : (popped s).regs tail = (popped s).regs head + queue.length := by
        rw [htail, hh]; simp only [List.length_cons] at ht; omega
      obtain ⟨k, t, hs, hk, hh', ht', hf, hv⟩ := scan_correct (a.valid u hu) hchain hview htt
      obtain ⟨heq, hi'⟩ := hi.process rep
      refine ⟨(insert u done, (scan (a.neighbors u) (discovered done (u :: queue)) queue).2),
        6 + k, t, .seq hx hs, ?_, ?_⟩
      · exact ⟨hi', heap.frame (by simpa [hm] using hf), by simpa [heq] using hv, ht'⟩
      · have hp := potential_process a done hu hud
        dsimp only
        omega

/-- The machine loop returns exactly the reachable set in linear time in the
number of vertices plus stored adjacency entries. -/
theorem bfs_loop_correct {β : Type*} {a : Adjacency} {G : Graph Nat β}
    (rep : Represents a G) {source : Nat} {s : State}
    (h : LoopRep a G source (∅, [source]) s) :
    ∃ k t, Exec bfsLoop s k t ∧
      ReturnsReachable G source (fun v => v < a.n ∧ t.memory (5 * v + 1) = 1) ∧
      k ≤ 8 * a.n + 32 * rep.edges.card + 1 := by
  obtain ⟨k, t, hx, hQ, hk⟩ := (bfs_vc rep source).sound h
  refine ⟨k, t, hx, hQ, ?_⟩
  simp only [potential_initial] at hk
  have := rep.incidenceBound
  omega

end AlgoLib.Experimental.RAM.BFS
