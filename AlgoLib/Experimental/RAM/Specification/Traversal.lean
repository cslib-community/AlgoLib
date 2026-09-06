/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Specification.Graph
import Mathlib.Tactic

/-!
# Mathematical BFS discovery and frontier preservation

These are the existing scan and reachability lemmas, moved out of the backend so
owned frontend proofs can reuse them without importing instructions or memory.
The scan is a mathematical specification. Executable programs still traverse each
adjacency entry and invoke separately certified queue and visited operations.
-/
namespace AlgoLib.Experimental.RAM.BFS

/-- Ghost effect of mark-before-enqueue. -/
def discover (seen : Finset Nat) (queue : List Nat) (v : Nat) : Finset Nat × List Nat :=
  if v ∈ seen then (seen, queue) else (insert v seen, queue ++ [v])


/-- Pure ghost scan, used only in specifications and proofs. -/
def scan (xs : List Nat) (seen : Finset Nat) (queue : List Nat) : Finset Nat × List Nat :=
  match xs with
  | [] => (seen, queue)
  | v :: vs => let d := discover seen queue v; scan vs d.1 d.2


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

end AlgoLib.Experimental.RAM.BFS
