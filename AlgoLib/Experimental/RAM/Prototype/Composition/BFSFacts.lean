/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Specification.Traversal
import AlgoLib.Experimental.RAM.Authoring.ArrayFacts

/-!
# The paper argument for owned BFS

Visited arrays denote finite vertex sets. A frontier consists of the processed
vertices and a duplicate-free queue. Remaining work counts each unprocessed vertex
once and each of its adjacency entries once. These definitions and lemmas contain
no compiler, address, queue representation, or implementation potential.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Composition.BFSFacts
open Experimental.RAM.BFS

def marked (a : Array Nat) : Finset Nat := (Finset.range a.size).filter (fun v => a[v]! ≠ 0)

@[simp] theorem mem_marked (a : Array Nat) (v : Nat) :
    v ∈ marked a ↔ v < a.size ∧ a[v]! ≠ 0 := by simp [marked]

theorem mark_insert (a : Array Nat) (v : Nat) (valid : v < a.size) :
    marked (a.setIfInBounds v 1) = insert v (marked a) := by
  ext w
  by_cases eq : w = v
  · subst w
    simp [mem_marked, valid, getElem!_pos]
  · by_cases hw : w < a.size
    · simp [mem_marked, hw, getElem!_pos, eq, Ne.symm eq]
    · simp [mem_marked, hw, eq]

def QueueOK (a : Array Nat) (q : List Nat) : Prop := q.Nodup ∧ ∀ v ∈ q, v ∈ marked a

theorem room_for_fresh (a : Array Nat) (q : List Nat) (v : Nat)
    (ok : QueueOK a q) (valid : v < a.size) (fresh : a[v]! = 0) : q.length < a.size := by
  have hv : v ∉ q := by
    intro hv
    have := (mem_marked a v).mp (ok.2 v hv)
    exact this.2 fresh
  have sub : q.toFinset ⊆ Finset.range a.size := by
    intro w hw
    exact Finset.mem_range.mpr ((mem_marked a w).mp (ok.2 w (by simpa using hw))).1
  have proper : q.toFinset ⊂ Finset.range a.size :=
    ⟨sub, fun h => hv (by simpa using h (Finset.mem_range.mpr valid))⟩
  simpa [List.toFinset_card_of_nodup ok.1] using Finset.card_lt_card proper

theorem queue_tail (a : Array Nat) (q : List Nat) (ok : QueueOK a q) : QueueOK a q.tail :=
  ⟨ok.1.sublist (List.tail_sublist q), fun v hv => ok.2 v (List.mem_of_mem_tail hv)⟩

theorem queue_enqueue (a : Array Nat) (q : List Nat) (v : Nat)
    (ok : QueueOK a q) (valid : v < a.size) (fresh : a[v]! = 0) :
    QueueOK (a.setIfInBounds v 1) (q ++ [v]) := by
  have hv : v ∉ q := fun h => ((mem_marked a v).mp (ok.2 v h)).2 fresh
  refine ⟨ok.1.append (List.nodup_singleton v) (List.disjoint_singleton.mpr hv), ?_⟩
  intro w hw
  rw [mark_insert a v valid]
  simp only [List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact Finset.mem_insert_of_mem (ok.2 w hw)
  · exact Finset.mem_insert_self _ _

def Frontier {β : Type} (a : Adjacency) (G : AlgoLib.Graph Nat β) (source : Nat)
    (seen : Finset Nat) (q : List Nat) : Prop :=
  ∃ done, seen = discovered done q ∧ Invariant a G source done q

theorem frontier_queue {β : Type} (a : Adjacency) (G : AlgoLib.Graph Nat β) (source : Nat)
    (visited : Array Nat) (q : List Nat) (h : Frontier a G source (marked visited) q) :
    QueueOK visited q := by
  obtain ⟨done, seen, inv⟩ := h
  exact ⟨inv.distinct, fun v hv => seen ▸ (mem_discovered.mpr (Or.inr hv))⟩

theorem processed_eq {done seen : Finset Nat} {q : List Nat}
    (h : seen = discovered done q) (disjoint : ∀ v ∈ q, v ∉ done) :
    seen \ q.toFinset = done := by
  ext v
  simp only [h, Finset.mem_sdiff, mem_discovered, List.mem_toFinset]
  have := disjoint v
  tauto

def work (a : Adjacency) (seen : Finset Nat) (q : List Nat) : Nat :=
  ∑ v ∈ Finset.range a.n \ (seen \ q.toFinset), (1 + (a.neighbors v).length)

theorem scan_processed (row : List Nat) (seen : Finset Nat) (q : List Nat) :
    (scan row seen q).1 \ (scan row seen q).2.toFinset = seen \ q.toFinset := by
  ext v
  simp only [Finset.mem_sdiff, scan_seen, List.mem_toFinset, scan_queue]
  tauto

theorem scan_work (a : Adjacency) (row : List Nat) (seen : Finset Nat) (q : List Nat) :
    work a (scan row seen q).1 (scan row seen q).2 = work a seen q := by
  simp only [work, scan_processed]

theorem process {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β} {source u : Nat}
    {seen : Finset Nat} {q : List Nat} (rep : Represents a G)
    (h : Frontier a G source seen (u :: q)) :
    u < a.n ∧ Frontier a G source (scan (a.neighbors u) seen q).1
      (scan (a.neighbors u) seen q).2 ∧
      work a seen q + (1 + (a.neighbors u).length) = work a seen (u :: q) := by
  obtain ⟨done, rfl, inv⟩ := h
  have hu := inv.valid_queue u (by simp)
  have fresh := inv.disjoint u (by simp)
  have complete := inv.process rep
  refine ⟨hu, ⟨insert u done, complete⟩, ?_⟩
  have old := processed_eq rfl inv.disjoint
  have new := processed_eq complete.1 complete.2.disjoint
  have erased : Finset.range a.n \ insert u done = (Finset.range a.n \ done).erase u := by
    ext v; simp; tauto
  rw [← scan_work a (a.neighbors u)]
  simp only [work, old, new, erased]
  exact Finset.sum_erase_add _ _ (by simp [hu, fresh])

theorem exit {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β} {source : Nat}
    {seen : Finset Nat} (rep : Represents a G) (h : Frontier a G source seen []) :
    ∀ v, v ∈ seen ↔ Reachable G source v := by
  obtain ⟨done, rfl, inv⟩ := h
  simpa [discovered] using inv.exit rep

theorem process_head {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β} {source : Nat}
    {seen : Finset Nat} {q : List Nat} (rep : Represents a G) (running : q ≠ [])
    (h : Frontier a G source seen q) :
    q.head?.getD 0 < a.n ∧ Frontier a G source (scan (a.neighbors (q.head?.getD 0)) seen q.tail).1
      (scan (a.neighbors (q.head?.getD 0)) seen q.tail).2 ∧
      work a seen q.tail + (1 + (a.neighbors (q.head?.getD 0)).length) = work a seen q := by
  cases q with
  | nil => contradiction
  | cons u q => exact process rep h

theorem initial {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β} {source : Nat}
    (rep : Represents a G) (valid : source < a.n) : Frontier a G source {source} [source] := by
  refine ⟨∅, by simp [discovered], ⟨by simp, by simp, by simp, ?_, by simp, ?_, by simp⟩⟩
  · intro v hv; simpa using (show v = source by simpa using hv) ▸ valid
  · intro v hv
    have eq : v = source := by simpa using hv
    subst v
    exact .refl ((rep.vertices source).mpr valid)

theorem initial_work (a : Adjacency) (source : Nat) :
    work a {source} [source] = a.n + a.entries := by
  simp [work, Adjacency.entries, Finset.sum_add_distrib]

theorem work_le_total (a : Adjacency) (seen : Finset Nat) (q : List Nat) :
    work a seen q ≤ a.n + a.entries := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun v => 1 + (a.neighbors v).length)
    (Finset.sdiff_subset (s := Finset.range a.n) (t := seen \ q.toFinset))
    (fun _ _ _ => Nat.zero_le _)
  simpa [work, Adjacency.entries, Finset.sum_add_distrib] using h

theorem scan_mark (row : List Nat) (visited : Array Nat) (q : List Nat)
    (running : row ≠ []) (valid : row.head?.getD 0 < visited.size)
    (fresh : visited[row.head?.getD 0]! = 0) :
    scan row.tail (marked (visited.setIfInBounds (row.head?.getD 0) 1)) (q ++ [row.head?.getD 0]) =
      scan row (marked visited) q := by
  rw [mark_insert visited (row.head?.getD 0) valid]
  cases row with
  | nil => contradiction
  | cons v vs => simp_all [scan, discover, mem_marked]

theorem scan_skip (row : List Nat) (visited : Array Nat) (q : List Nat)
    (running : row ≠ []) (valid : row.head?.getD 0 < visited.size)
    (old : visited[row.head?.getD 0]! ≠ 0) :
    scan row.tail (marked visited) q = scan row (marked visited) q := by
  cases row with
  | nil => contradiction
  | cons v vs => simp_all [scan, discover, mem_marked]

theorem marked_empty (visited : Array Nat) (zero : ∀ v < visited.size, visited[v]! = 0) :
    marked visited = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have h := (mem_marked visited v).mp hv
  exact h.2 (zero v h.1)

theorem zero_prefix (visited : Array Nat) (i : Nat) (hi : i < visited.size)
    (zero : ∀ v < i, visited[v]! = 0) :
    ∀ v < i + 1, (visited.setIfInBounds i 0)[v]! = 0 := by
  intro v hv
  have hb : v < visited.size := by omega
  rw [Authoring.ArrayFacts.get_set _ _ _ _ hb]
  split_ifs with eq
  · rfl
  · exact zero v (by omega)

/-- Initialization connects the cleared bitmap to the graph invariant. -/
theorem seed {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β}
    (rep : Represents a G) (visited : Array Nat) (source : Nat)
    (size : visited.size = a.n) (valid : source < a.n)
    (zero : ∀ v < visited.size, visited[v]! = 0) :
    Frontier a G source (marked (visited.setIfInBounds source 1)) [source] := by
  rw [mark_insert _ _ (by omega), marked_empty _ zero]
  simpa using initial rep valid

theorem frontier_head {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β}
    {source : Nat} {seen : Finset Nat} {q : List Nat}
    (h : Frontier a G source seen q) (running : q ≠ []) : q.head?.getD 0 < a.n := by
  obtain ⟨done, eq, inv⟩ := h
  cases q with
  | nil => contradiction
  | cons u q => exact inv.valid_queue u (by simp)

theorem finish_bitmap {β : Type} {a : Adjacency} {G : AlgoLib.Graph Nat β}
    (rep : Represents a G) (source : Nat) (visited : Array Nat)
    (h : Frontier a G source (marked visited) []) :
    ∀ v, (v < visited.size ∧ visited[v]! ≠ 0) ↔ Reachable G source v := by
  simpa only [mem_marked] using exit rep h

theorem head_mem (row : List Nat) (running : row ≠ []) : row.head?.getD 0 ∈ row := by
  cases row with
  | nil => contradiction
  | cons u q => simp

grind_pattern head_mem => row.head?.getD 0

end AlgoLib.Experimental.RAM.Prototype.Composition.BFSFacts
