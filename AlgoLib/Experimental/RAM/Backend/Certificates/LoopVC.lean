/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Machine.Machine

/-!
# Machine-level loop certificate rule

Establishes total execution from an instruction-level invariant and decreasing credit potential.

This is used by implementation certificates, not by the canonical algorithm proof. Public
LoopProof is in Authoring/Semantics.

## Further details

# Modular verification conditions with time credits

A loop invariant may relate the RAM state to arbitrary *ghost* mathematical
data. The potential is the remaining time credit. Paying for a true guard
forces strict decrease, so the time VC also proves termination. No ghost data
or credits occur in the compiled program. Body contracts can be reused rather
than expanding nested loops into enormous weakest preconditions.
-/
namespace AlgoLib.Experimental.RAM.Checked

/-- The two verification conditions generated for a loop: its exit establishes
`post`; each true iteration preserves the invariant and pays its actual RAM
cost from the potential. Initialization is an instance of `rep` at the call. -/
structure LoopVC {Ghost : Type*} (q : Test) (body : Code)
    (rep : Ghost → State → Prop) (potential : Ghost → Nat) (post : State → Prop) : Prop where
  exit : ∀ g s, rep g s → q.eval s = false → post s
  step : ∀ g s, rep g s → q.eval s = true →
    ∃ g' k t, Exec body s k t ∧ rep g' t ∧ 1 + k + potential g' ≤ potential g

/-- All loop iterations, their guards, and the final false guard are accounted
for. In particular, a false claimed potential cannot manufacture an execution. -/
theorem LoopVC.sound {Ghost : Type*} {q : Test} {body : Code}
    {rep : Ghost → State → Prop} {potential : Ghost → Nat} {post : State → Prop}
    (vc : LoopVC q body rep potential post) {g s} (h : rep g s) :
    ∃ k t, Exec (.while q body) s k t ∧ post t ∧ k ≤ potential g + 1 := by
  suffices ∀ n g s, potential g = n → rep g s →
      ∃ k t, Exec (.while q body) s k t ∧ post t ∧ k ≤ potential g + 1 from
    this (potential g) g s rfl h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro g s hn hs
    cases hq : q.eval s with
    | false => exact ⟨1, s, .whileFalse hq, vc.exit g s hs hq, by omega⟩
    | true =>
      obtain ⟨g', i, u, hx, hu, hp⟩ := vc.step g s hs hq
      obtain ⟨j, t, ht, hQ, hj⟩ := ih (potential g') (by omega) g' u rfl hu
      exact ⟨1 + i + j, t, .whileTrue hq hx ht, hQ, by omega⟩

/-- Straight-line verification conditions are calculated from instruction syntax,
including the actual cost. This is the base case for modular loop proofs. -/
def BlockVC (is : List Instr) (Q : State → Prop) (credit : Nat) (s : State) : Prop :=
  Q (blockEval is s) ∧ is.length ≤ credit

theorem BlockVC.sound {is Q credit s} (h : BlockVC is Q credit s) :
    ∃ k t, Exec (.block is) s k t ∧ Q t ∧ k ≤ credit :=
  ⟨is.length, blockEval is s, .block is s, h⟩

end AlgoLib.Experimental.RAM.Checked
