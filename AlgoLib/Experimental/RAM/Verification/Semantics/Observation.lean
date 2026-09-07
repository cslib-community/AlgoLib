/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Mathlib.Tactic

/-!
# A costed observation for the Loom algebra

This independent finite-execution semantics instantiates the actual upstream Loom
hierarchy in `LoomObservation.lean`. Credit: the Loom authors,
https://github.com/verse-lab/loom and https://verse-lab.org/papers/loom-popl26.pdf.
Velvet motivates the separation of executable methods from their proof annotations.

`Computation` describes finite stateful executions with a cost. `wp` observes an
execution through its postcondition and remaining credits. The pure/bind laws are
proved below: symbolic execution can compose observations without inspecting RAM.
This is an existential total-correctness observation, intended for the deterministic
supported language. It is NOT a demonic WP for arbitrary nondeterministic programs.
There are no executable arbitrary Lean callbacks in the supported program syntax.
-/
namespace AlgoLib.Experimental.RAM.Prototype

/-- A finite costed execution, independent of the RAM machine. -/
def Computation (State α : Type) := State → Nat → State → α → Prop

namespace Computation
variable {State α β γ : Type}

def pure (a : α) : Computation State α := fun s k t b => k = 0 ∧ t = s ∧ b = a

def bind (m : Computation State α) (f : α → Computation State β) : Computation State β :=
  fun s k t b => ∃ i u a j, m s i u a ∧ f a u j t b ∧ k = i + j

/-- Observe a terminating execution; no user-supplied fuel occurs here. -/
def wp (m : Computation State α) (Q : α → State → Nat → Prop) (s : State) (c : Nat) : Prop :=
  ∃ k t a, m s k t a ∧ k ≤ c ∧ Q a t (c - k)

theorem pure_bind (a : α) (f : α → Computation State β) : bind (pure a) f = f a := by
  funext s k t b
  simp [bind, pure]

theorem bind_pure (m : Computation State α) : bind m pure = m := by
  funext s k t b
  simp [bind, pure]

theorem bind_assoc (m : Computation State α) (f : α → Computation State β)
    (g : β → Computation State γ) : bind (bind m f) g = bind m (fun a => bind (f a) g) := by
  funext s k t b
  apply propext
  constructor
  · rintro ⟨ij, v, a, l, ⟨i, u, x, j, hm, hf, rfl⟩, hg, rfl⟩
    exact ⟨i, u, x, j + l, hm, ⟨j, v, a, l, hf, hg, rfl⟩, Nat.add_assoc ..⟩
  · rintro ⟨i, u, x, jl, hm, ⟨j, v, a, l, hf, hg, rfl⟩, rfl⟩
    exact ⟨i + j, v, a, l, ⟨i, u, x, j, hm, hf, rfl⟩, hg, (Nat.add_assoc ..).symm⟩

@[simp] theorem wp_pure (a : α) (Q : α → State → Nat → Prop) (s : State) (c : Nat) :
    (pure a).wp Q s c ↔ Q a s c := by simp [wp, pure]

/-- The observation preserves sequencing: the central Loom-style connection. -/
theorem wp_bind (m : Computation State α) (f : α → Computation State β)
    (Q : β → State → Nat → Prop) (s : State) (c : Nat) :
    (bind m f).wp Q s c ↔ m.wp (fun a => (f a).wp Q) s c := by
  constructor
  · rintro ⟨k, t, b, ⟨i, u, a, j, hm, hf, rfl⟩, hk, hQ⟩
    exact ⟨i, u, a, hm, by omega, j, t, b, hf, by omega,
      by simpa [Nat.sub_sub] using hQ⟩
  · rintro ⟨i, u, a, hm, hi, j, t, b, hf, hj, hQ⟩
    exact ⟨i + j, t, b, ⟨i, u, a, j, hm, hf, rfl⟩, by omega,
      by simpa [Nat.sub_sub] using hQ⟩

theorem wp_mono {m : Computation State α} {P Q : α → State → Nat → Prop}
    (h : ∀ a s c, P a s c → Q a s c) {s : State} {c : Nat} (hp : m.wp P s c) :
    m.wp Q s c := by
  obtain ⟨k, t, a, hm, hk, ht⟩ := hp
  exact ⟨k, t, a, hm, hk, h a t (c - k) ht⟩

/-- Each loop test consumes a credit, including the final false test. -/
inductive Loop (test : State → Bool) (body : Computation State Unit) :
    State → Nat → State → Unit → Prop where
  | done {s} : test s = false → Loop test body s 1 s ()
  | step {s u t i j} : test s = true → body s i u () →
      Loop test body u j t () → Loop test body s (1 + i + j) t ()

/-- A supplied invariant and credit decrease prove termination, including zero-cost bodies. -/
theorem wp_loop (test : State → Bool) (body : Computation State Unit)
    (I : State → Nat → Prop) (Q : Unit → State → Nat → Prop)
    (step : ∀ s c, I s c → 1 ≤ c ∧
      if test s then body.wp (fun _ => I) s (c - 1) else Q () s (c - 1))
    (s : State) (c : Nat) (initial : I s c) : wp (Loop test body) Q s c := by
  induction c using Nat.strongRecOn generalizing s with
  | ind c ih =>
    obtain ⟨hc, hs⟩ := step s c initial
    cases ht : test s with
    | false => exact ⟨1, s, (), .done ht, hc, by simpa [ht] using hs⟩
    | true =>
      obtain ⟨i, u, a, hb, hi, hu⟩ := (by simpa [ht] using hs :
        body.wp (fun _ => I) s (c - 1))
      cases a
      obtain ⟨j, t, a, hl, hj, hQ⟩ := ih (c - 1 - i) (by omega) u hu
      cases a
      exact ⟨1 + i + j, t, (), .step ht hb hl, by omega,
        by simpa [Nat.sub_sub, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hQ⟩

end Computation
end AlgoLib.Experimental.RAM.Prototype
