/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Mathlib.Tactic

/-!
# Typed clients of abstract, owned interfaces

An input/output type describes the mathematical value of the resources transferred
through a call. It is not a global machine store. `frame` carries a separately owned
component through a computation. Operations describe functional behavior and logical
charges only. Neither their Lean effects nor tests are executable RAM callbacks:
linking requires a registered implementation for every leaf, including both branches.

This is a first-order, structured client language. Calls inline finite procedure
bodies; runtime recursion and dynamic allocation are not claimed. Loop termination
is established by VCs. Library authors provide operations; clients supply invariants.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace AlgoLib.Experimental.RAM.Prototype.Composition

structure Operation (A B : Type) where
  requires : A → Prop
  effect : A → B
  charge : A → Nat

inductive Program : Type → Type → Type 1 where
  | identity : Program A A
  | swap : Program (A × B) (B × A)
  | invoke (op : Operation A B) : Program A B
  | seq (p : Program A B) (q : Program B C) : Program A C
  | frame (p : Program A B) (R : Type) : Program (A × R) (B × R)
  | branch (test : A → Bool) (yes no : Program A B) : Program A B
  | loop (test : A → Bool) (body : Program A A) : Program A A
  | call (body : Program A B) : Program A B

/-- Finite loop execution over a typed body relation. -/
inductive Iter (test : A → Bool) (body : A → Nat → A → Prop) : A → Nat → A → Prop where
  | done : test a = false → Iter test body a 1 a
  | step : test a = true → body a i b → Iter test body b j c → Iter test body a (1 + i + j) c

/-- Compositional execution; type indices never require casting machine values. -/
def Run : Program A B → A → Nat → B → Prop
  | .identity, a, k, b => k = 0 ∧ b = a
  | .swap, a, k, b => k = 0 ∧ b = (a.2, a.1)
  | .invoke op, a, k, b => op.requires a ∧ k = op.charge a ∧ b = op.effect a
  | .seq p q, a, k, c => ∃ i b j, Run p a i b ∧ Run q b j c ∧ k = i + j
  | .frame p _, a, k, b => Run p a.1 k b.1 ∧ b.2 = a.2
  | .branch test p q, a, k, b => ∃ i, k = 1 + i ∧ if test a then Run p a i b else Run q a i b
  | .loop test body, a, k, b => Iter test (Run body) a k b
  | .call p, a, k, b => Run p a k b

namespace Run
theorem identity (a : A) : Run (.identity : Program A A) a 0 a := ⟨rfl, rfl⟩
theorem invoke (op : Operation A B) (a : A) (h : op.requires a) :
    Run (.invoke op) a (op.charge a) (op.effect a) := ⟨h, rfl, rfl⟩
theorem seq (hp : Run p a i b) (hq : Run q b j c) : Run (.seq p q) a (i + j) c :=
  ⟨i, b, j, hp, hq, rfl⟩
theorem frame (hp : Run p a i b) (r : R) : Run (.frame p R) (a, r) i (b, r) := ⟨hp, rfl⟩
theorem yes (ht : test a = true) (hp : Run p a i b) : Run (.branch test p q) a (1 + i) b :=
  ⟨i, rfl, by simpa [ht] using hp⟩
theorem no (ht : test a = false) (hq : Run q a i b) : Run (.branch test p q) a (1 + i) b :=
  ⟨i, rfl, by simpa [ht] using hq⟩
theorem done (ht : test a = false) : Run (.loop test body) a 1 a := Iter.done ht
theorem step (ht : test a = true) (hb : Run body a i b) (hl : Run (.loop test body) b j c) :
    Run (.loop test body) a (1 + i + j) c := Iter.step ht hb hl
theorem call (hp : Run p a i b) : Run (.call p) a i b := hp
end Run

/-- Only mathematical values and logical credits occur in the generated goals. -/
def VC : Program A B → (B → Nat → Prop) → A → Nat → Prop
  | .identity, Q, a, c => Q a c
  | .swap, Q, a, c => Q (a.2, a.1) c
  | .invoke op, Q, a, c => op.requires a ∧ op.charge a ≤ c ∧ Q (op.effect a) (c - op.charge a)
  | .seq p q, Q, a, c => VC p (VC q Q) a c
  | .frame p _, Q, a, c => VC p (fun b d => Q (b, a.2) d) a.1 c
  | .branch test p q, Q, a, c => 1 ≤ c ∧ if test a then VC p Q a (c - 1) else VC q Q a (c - 1)
  | .loop test body, Q, a, c => ∃ I : A → Nat → Prop, I a c ∧
      ∀ b d, I b d → 1 ≤ d ∧ if test b then VC body I b (d - 1) else Q b (d - 1)
  | .call p, Q, a, c => VC p Q a c

theorem VC.sound (p : Program A B) (Q : B → Nat → Prop) (a : A) (c : Nat)
    (h : VC p Q a c) : ∃ k b, Run p a k b ∧ k ≤ c ∧ Q b (c - k) := by
  induction p generalizing c with
  | identity => exact ⟨0, a, Run.identity a, by omega, by simpa [VC] using h⟩
  | swap => exact ⟨0, (a.2, a.1), ⟨rfl, rfl⟩, by omega, by simpa [VC] using h⟩
  | invoke op => exact ⟨_, _, Run.invoke op a h.1, h.2⟩
  | seq p q ihp ihq =>
    obtain ⟨i, b, hp, hi, hb⟩ := ihp _ _ _ h
    obtain ⟨j, d, hq, hj, hd⟩ := ihq _ _ _ hb
    exact ⟨i + j, d, Run.seq hp hq, by omega, by simpa [Nat.sub_sub] using hd⟩
  | frame p R ih =>
    obtain ⟨i, b, hp, hi, hb⟩ := ih _ _ _ h
    exact ⟨i, (b, a.2), by simpa using Run.frame hp (r := a.2), hi, hb⟩
  | branch test p q ihp ihq =>
    obtain ⟨hc, hn⟩ := h
    cases ht : test a with
    | true =>
      obtain ⟨i, b, hp, hi, hb⟩ := ihp Q a (c - 1) (by simpa [ht] using hn)
      exact ⟨1 + i, b, Run.yes ht hp, by omega, by simpa [Nat.sub_sub, Nat.add_comm] using hb⟩
    | false =>
      obtain ⟨i, b, hp, hi, hb⟩ := ihq Q a (c - 1) (by simpa [ht] using hn)
      exact ⟨1 + i, b, Run.no ht hp, by omega, by simpa [Nat.sub_sub, Nat.add_comm] using hb⟩
  | loop test body ih =>
    obtain ⟨I, ha, hs⟩ := h
    have go : ∀ c a, I a c → ∃ k b, Run (.loop test body) a k b ∧ k ≤ c ∧ Q b (c - k) := by
      intro c
      induction c using Nat.strongRecOn with
      | ind c rec =>
        intro a ha
        obtain ⟨hc, hn⟩ := hs a c ha
        cases ht : test a with
        | false => exact ⟨1, a, Run.done ht, hc, by simpa [ht] using hn⟩
        | true =>
          obtain ⟨i, b, hb, hi, hI⟩ := ih I a (c - 1) (by simpa [ht] using hn)
          obtain ⟨j, d, hd, hj, hQ⟩ := rec (c - 1 - i) (by omega) b hI
          exact ⟨1 + i + j, d, Run.step ht hb hd, by omega,
            by simpa [Nat.sub_sub, Nat.add_assoc] using hQ⟩
    exact go c a ha
  | call p ih =>
    obtain ⟨i, b, hp, hi, hQ⟩ := ih Q a c h
    exact ⟨i, b, Run.call hp, hi, hQ⟩

/-- Run two procedures on separately owned components, without copying either. -/
abbrev Program.both (p : Program A B) (q : Program C D) : Program (A × C) (B × D) :=
  .seq (.frame p C) (.seq .swap (.seq (.frame q B) .swap))

/-- A reusable procedure specification; implementations and payment strategy are absent. -/
structure Procedure (A B : Type) where
  body : Program A B
  requires : A → Prop
  ensures : A → B → Prop
  credits : A → Nat
  correct : ∀ a, requires a → ∃ k b, Run body a k b ∧ ensures a b ∧ k ≤ credits a

/-- Package only mathematical VCs; the source execution proof is reconstructed. -/
def Procedure.verify (body : Program A B) (pre : A → Prop) (post : A → B → Prop)
    (credits : A → Nat)
    (proof : ∀ a, pre a → VC body (fun b _ => post a b) a (credits a)) : Procedure A B where
  body := body
  requires := pre
  ensures := post
  credits := credits
  correct a ha := by
    obtain ⟨k,b,run,hk,hb⟩ := VC.sound body _ a _ (proof a ha)
    exact ⟨k,b,run,hb,hk⟩

/-- Typed procedure composition uses only the two public contracts. -/
def Procedure.then (p : Procedure A B) (q : Procedure B C)
    (accepts : ∀ a b, p.requires a → p.ensures a b → q.requires b)
    (allowance : A → Nat) (pays : ∀ a b, p.requires a → p.ensures a b → q.credits b ≤ allowance a) :
    Procedure A C where
  body := .seq (.call p.body) (.call q.body)
  requires := p.requires
  ensures a c := ∃ b, p.ensures a b ∧ q.ensures b c
  credits a := p.credits a + allowance a
  correct a ha := by
    obtain ⟨i, b, hp, hb, hi⟩ := p.correct a ha
    obtain ⟨j, c, hq, hc, hj⟩ := q.correct b (accepts a b ha hb)
    exact ⟨i + j, c, .seq (Run.call hp) (Run.call hq), ⟨b, hb, hc⟩,
      by have := pays a b ha hb; omega⟩

end AlgoLib.Experimental.RAM.Prototype.Composition
