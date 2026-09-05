/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Internal.Search
import AlgoLib.Experimental.RAM.Paper.Interface
import AlgoLib.Experimental.RAM.Library.GraphInput
import AlgoLib.Experimental.RAM.Core.Output

namespace AlgoLib.Experimental.RAM.Paper.Search
open Checked Checked.Language Experimental.RAM.BFS

def initial (source : Nat) : State := ⟨{source}, [source], [], source, ∅⟩

private def encode {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) : Store where
  vars ty name := if ty = .word ∧ name = Refinement.name size then a.n else
    if ty = .word ∧ name = Refinement.name vertex then i.source else 0
  heap := i.memory

private def prepareCode : Code := .seq (.block [.mov head (.lit 0)])
  (.seq clearCode (.seq seed (.block [.mov ptr (.lit 0)])))

private theorem prepare_correct {β : Type} {a : Adjacency} {G : Graph Nat β} (i : Input a G) :
    ∃ k t, Eval (Refinement.lift prepareCode) (encode i) k t ∧
      (model a).Represents (initial i.source) t ∧ k ≤ 25 * a.n + 45 := by
  let s := Refinement.view (encode i)
  have ready : Refinement.Ready (encode i) := by simp [encode, Refinement.Ready]
  have hn : s.regs size = a.n := by simp [s, encode, Refinement.view, Refinement.name, size]
  have hsource : s.regs vertex = i.source := by
    simp [s, encode, Refinement.view, Refinement.name, vertex]
  let z := s.set head 0
  have hz : z.regs head = 0 := by simp [z, Checked.State.set]
  have hzn : z.regs size = a.n := by simpa [z, Checked.State.set, size, head] using hn
  have hzs : z.regs vertex = i.source := by simpa [z, Checked.State.set, vertex, head] using hsource
  obtain ⟨k, u, hu, ⟨hun, hus, hf, hzero⟩, hk⟩ := (clear_vc a.n i.source s.memory).sound
    (g := 0) (s := z) ⟨hz, by omega, hzn, hzs, .refl _, by simp⟩
  obtain ⟨he, hh, ht, hm⟩ := seed_correct u
  have hv : View a.n (seeded u).memory {i.source} [i.source] ((seeded u).regs head) := by
    have emptyView : View a.n u.memory ∅ [] 0 := ⟨by simpa using hzero, by simp⟩
    simpa [hm, hh, hus] using emptyView.enqueue (v := i.source)
  let t := (seeded u).set ptr 0
  have hheap : Heap a t.memory := by
    change Heap a (seeded u).memory
    rw [hm, hus]
    exact (i.heap.frame hf).frame (enqueue_frame _ _ _)
  have hx : Exec prepareCode s (1 + (k + (6 + 1))) t :=
    .seq (.block _ s) (.seq hu (.seq he (.block _ _)))
  obtain ⟨j, w, hw, hready, heq, hj⟩ := Refinement.lift_correct hx (by decide) (encode i) ready rfl
  have hmem : w.heap = t.memory := congrArg Checked.State.memory heq
  refine ⟨j, w, hw, ⟨hready, hmem ▸ hheap, ?_, ?_, ?_⟩, by omega⟩
  · change View a.n w.heap {i.source} [i.source] ((Refinement.view w).regs head)
    simpa [hmem, heq, t, Checked.State.set, head, ptr] using hv
  · change (Refinement.view w).regs tail = (Refinement.view w).regs head + [i.source].length
    simp [heq, t, Checked.State.set, head, ptr, tail, hh, ht]
  · change (Refinement.view w).regs ptr = 0
    simp [heq, t, Checked.State.set]

/-- Ordinary graph/source input, and a visited-set output. Preparation clears
arbitrary scratch memory and is included in the compiled time bound. -/
def interface {β : Type} (a : Adjacency) (G : Graph Nat β) :
    Interface (model a) (Input a G) Bitmap where
  initial i := initial i.source
  encode := encode
  prepare := Refinement.lift prepareCode
  preparationCost _ := 25 * a.n + 45
  preparation := prepare_correct
  decode _ s := ⟨a.n, s.heap, 5, 1⟩
  Observes g out := ∀ v, out.contains v = true ↔ v < a.n ∧ v ∈ g.seen
  output i g s hs := by
    intro v
    simp only [Bitmap.contains, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    constructor
    · rintro ⟨hv, hm⟩
      have h := hs.2.2.1.marks v hv
      refine ⟨hv, ?_⟩
      split_ifs at h with seen
      · exact seen
      · omega
    · rintro ⟨hv, seen⟩
      exact ⟨hv, by simpa [seen] using hs.2.2.1.marks v hv⟩

end AlgoLib.Experimental.RAM.Paper.Search
