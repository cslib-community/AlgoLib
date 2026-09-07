/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Language.Contracts
import AlgoLib.Experimental.RAM.Verification.SourceMetadata

/-!
# Indexed verification plans and their soundness

A Plan annotates the exact executable Program. Calls read public summaries; framing,
branches and loops compose their VCs. Plan.sound reconstructs abstract execution
with affine credit accounting. The annotations never define a second executable.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

/-- Proof annotations indexed by the one supported executable language. -/
inductive Plan : {A B : Type} → Program A B → Type 1 where
  | identity : Plan (.identity : Program A A)
  | swap : Plan (.swap : Program (A × B) (B × A))
  | invoke (op : Operation A B) : Plan (.invoke op)
  | call (proc : Procedure A B) : Plan (.call proc.body)
  | seq : Plan p → Plan q → Plan (.seq p q)
  | frame (proof : Plan p) (R : Type) : Plan (.frame p R)
  | branch (test : A → Bool) : Plan p → Plan q → Plan (.branch test p q)
  | loop (test : A → Bool) (invariant : A → Nat → Prop) :
      Plan body → Plan (.loop test body)
  | atEntry {p : Program A B} (annotations : A → Plan p) : Plan p
  | assert (fact : A → Prop) : Plan (.identity : Program A A)
  | countedLoop (site : String) (test : A → Bool) (invariant : A → Prop)
      (measure : A → Nat) (bodyAllowance : Nat) : Plan body → Plan (.loop test body)
  | invokeAt (site : String) (op : Operation A B) : Plan (.invoke op)
  | callAt (site : String) (proc : Procedure A B) : Plan (.call proc.body)
  | workLoop (site : String) (test : A → Bool) (invariant : A → Prop)
      (measure : A → Nat) (unit : Nat) : Plan body → Plan (.loop test body)

/-- The call case reads only requires/ensures/credits, never the procedure body. -/
def Plan.vc {A B : Type} {p : Program A B} : Plan p → (B → Nat → Prop) → A → Nat → Prop
  | .identity, Q, a, c => Q a c
  | .swap, Q, a, c => Q (a.2, a.1) c
  | .invoke op, Q, a, c => op.requires a ∧ op.charge a ≤ c ∧ Q (op.effect a) (c - op.charge a)
  | .call proc, Q, a, c => proc.requires a ∧ proc.credits a ≤ c ∧
      SourceForall "result" (fun b => proc.ensures a b → Q b (c - proc.credits a))
  | .seq p q, Q, a, c => p.vc (q.vc Q) a c
  | .frame p _, Q, a, c => p.vc (fun b d => Q (b, a.2) d) a.1 c
  | .branch test p q, Q, a, c => 1 ≤ c ∧ if test a then p.vc Q a (c - 1) else q.vc Q a (c - 1)
  | .loop test I body, Q, a, c => I a c ∧ SourceForall "current" (fun b => ∀ d, I b d → 1 ≤ d ∧
      if test b then body.vc I b (d - 1) else Q b (d - 1))
  | .atEntry f, Q, a, c => (f a).vc Q a c
  | .assert fact, Q, a, c => fact a ∧ Q a c
  | .countedLoop site test I measure unit body, Q, a, c =>
      ObligationAt "loop allowance sufficient" site (measure a * (unit + 1) + 1 ≤ c) ∧
      ObligationAt "loop invariant initialized" site (I a) ∧
      SourceForall "current" (fun b => I b → if test b then
        ObligationAt "iteration bound positive" site (0 < measure b) ∧
        body.vc (fun next _ =>
          ObligationAt "loop invariant preserved" site (I next) ∧
          ObligationAt "iteration bound decreases" site (measure next < measure b)) b unit
      else ObligationAt "loop exit" site (Q b (c - (measure a * (unit + 1) + 1))))
  | .invokeAt site op, Q, a, c =>
      ObligationAt "array index within bounds / operation precondition" site
        (op.requires a) ∧
      ObligationAt "statement allowance sufficient" site (op.charge a ≤ c) ∧
      Q (op.effect a) (c - op.charge a)
  | .callAt site proc, Q, a, c =>
      ObligationAt "procedure precondition" site (proc.requires a) ∧
      ObligationAt "procedure allowance sufficient" site (proc.credits a ≤ c) ∧
      SourceForall "result" (fun b => proc.ensures a b → Q b (c - proc.credits a))
  | .workLoop site test I measure unit body, Q, a, c =>
      ObligationAt "loop allowance sufficient" site (unit * measure a + 1 ≤ c) ∧
      ObligationAt "loop invariant initialized" site (I a) ∧
      SourceForall "current" (fun b => I b → if test b then
        body.vc (fun next left =>
          ObligationAt "loop invariant preserved" site (I next) ∧
          ObligationAt "remaining work decreases" site (measure next < measure b) ∧
          ObligationAt "iteration allowance sufficient" site (unit * measure next + 1 ≤ left))
          b (unit * measure b)
      else ObligationAt "loop exit" site (Q b (c - (unit * measure a + 1))))
termination_by structural plan _ _ _ => plan

/-- Replacing a procedure body preserves every caller continuation obligation. -/
theorem Plan.call_implementation_independent (contract : Contract A B)
    (p q : Program A B) (hp hq) (post : B → Nat → Prop) :
    (Plan.call (contract.implement p hp)).vc post =
      (Plan.call (contract.implement q hq)).vc post := rfl

/-- Public summaries suffice, even when a callee spends less than its allowance. -/
theorem Plan.sound {A B : Type} {p : Program A B} (plan : Plan p)
    (Q : B → Nat → Prop) (a : A) (c : Nat)
    (h : plan.vc Q a c) : ∃ k b left, Run p a k b ∧ k + left ≤ c ∧ Q b left := by
  induction plan generalizing c with
  | workLoop site test I measure unit body ih =>
    rename_i state bodyProgram
    obtain ⟨paid, initial, step⟩ := h
    change unit * measure a + 1 ≤ c at paid
    let surplus := c - (unit * measure a + 1)
    have go : ∀ n b, measure b = n → I b →
        ∃ k result, Run (.loop test bodyProgram) b k result ∧
          k ≤ unit * n + 1 ∧ Q result surplus := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n rec =>
        intro b equal inv
        have next := step b inv
        cases ht : test b with
        | false =>
          exact ⟨1, b, Run.done ht, by omega, by simpa [ht, surplus] using next⟩
        | true =>
          simp only [ht, ↓reduceIte] at next
          obtain ⟨j, mid, left, run, cost, invariant, smaller, allowance⟩ := ih _ b _ next
          obtain ⟨k, result, rest, bound, post⟩ := rec (measure mid) (equal ▸ smaller)
            mid rfl invariant
          change unit * measure mid + 1 ≤ left at allowance
          exact ⟨1 + j + k, result, Run.step ht run rest, by rw [← equal]; omega, post⟩
    obtain ⟨k, b, run, bound, post⟩ := go (measure a) a rfl initial
    exact ⟨k, b, surplus, run, by dsimp [surplus]; omega, post⟩
  | identity => exact ⟨0, a, c, Run.identity a, by omega, h⟩
  | swap => exact ⟨0, (a.2, a.1), c, ⟨rfl, rfl⟩, by omega, h⟩
  | invoke op => exact ⟨_, _, c - op.charge a, Run.invoke op a h.1, by have := h.2.1; omega, h.2.2⟩
  | call proc =>
    obtain ⟨pre, paid, next⟩ := h
    obtain ⟨k, b, run, post, bound⟩ := proc.correct a pre
    exact ⟨k, b, c - proc.credits a, Run.call run, by omega, next b post⟩
  | seq p q ihp ihq =>
    obtain ⟨i, b, middle, hp, hi, hb⟩ := ihp _ _ _ h
    obtain ⟨j, d, left, hq, hj, hd⟩ := ihq _ _ _ hb
    exact ⟨i + j, d, left, Run.seq hp hq, by omega, hd⟩
  | frame p R ih =>
    obtain ⟨i, b, left, hp, hi, hb⟩ := ih _ _ _ h
    exact ⟨i, (b, a.2), left, by simpa using Run.frame hp (r := a.2), hi, hb⟩
  | branch test p q ihp ihq =>
    obtain ⟨hc, hn⟩ := h
    cases ht : test a with
    | true =>
      obtain ⟨i, b, left, hp, hi, hb⟩ := ihp Q a (c - 1) (by simpa [ht] using hn)
      exact ⟨1 + i, b, left, Run.yes ht hp, by omega, hb⟩
    | false =>
      obtain ⟨i, b, left, hp, hi, hb⟩ := ihq Q a (c - 1) (by simpa [ht] using hn)
      exact ⟨1 + i, b, left, Run.no ht hp, by omega, hb⟩
  | loop test I body ih =>
    rename_i state bodyProgram
    obtain ⟨initial, step⟩ := h
    have go : ∀ c a, I a c → ∃ k b left,
        Run (.loop test bodyProgram) a k b ∧ k + left ≤ c ∧ Q b left := by
      intro c
      induction c using Nat.strongRecOn with
      | ind c rec =>
        intro a ha
        obtain ⟨hc, hn⟩ := step a c ha
        cases ht : test a with
        | false => exact ⟨1, a, c - 1, Run.done ht, by omega, by simpa [ht] using hn⟩
        | true =>
          obtain ⟨i, b, middle, hb, hi, hI⟩ := ih I a (c - 1) (by simpa [ht] using hn)
          obtain ⟨j, d, left, hd, hj, hQ⟩ := rec middle (by omega) b hI
          exact ⟨1 + i + j, d, left, Run.step ht hb hd, by omega, hQ⟩
    exact go c a initial
  | atEntry f ih => exact ih a Q a c h
  | assert fact => exact ⟨0, a, c, Run.identity a, by omega, h.2⟩
  | countedLoop site test I measure unit body ih =>
    rename_i state bodyProgram
    obtain ⟨paid, initial, step⟩ := h
    let surplus := c - (measure a * (unit + 1) + 1)
    have go : ∀ n b, measure b = n → I b →
        ∃ k result, Run (.loop test bodyProgram) b k result ∧
          k ≤ n * (unit + 1) + 1 ∧ Q result surplus := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n rec =>
        intro b eq inv
        have next := step b inv
        cases ht : test b with
        | false =>
          exact ⟨1, b, Run.done ht, by omega, by simpa [ht, surplus] using next⟩
        | true =>
          simp only [ht, ↓reduceIte] at next
          obtain ⟨j, mid, left, run, cost, invariant, decrease⟩ := ih _ b unit next.2
          have smaller : measure mid < n := eq ▸ decrease
          obtain ⟨k, result, rest, bound, post⟩ := rec (measure mid) smaller mid rfl invariant
          have ranks : (measure mid + 1) * (unit + 1) ≤ n * (unit + 1) :=
            Nat.mul_le_mul_right _ smaller
          refine ⟨1 + j + k, result, Run.step ht run rest, ?_, post⟩
          simp only [Nat.add_mul, Nat.one_mul] at ranks
          omega
    obtain ⟨k, result, run, bound, post⟩ := go (measure a) a rfl initial
    refine ⟨k, result, surplus, run, ?_, post⟩
    dsimp [surplus]
    change measure a * (unit + 1) + 1 ≤ c at paid
    omega
  | invokeAt site op =>
    exact ⟨_, _, c - op.charge a, Run.invoke op a h.1, by
      have := h.2.1; change _ ≤ _ at this; omega, h.2.2⟩
  | callAt site proc =>
    obtain ⟨k, b, run, post, bound⟩ := proc.correct a h.1
    exact ⟨k, b, c - proc.credits a, Run.call run, by
      have := h.2.1; change _ ≤ _ at this; omega, h.2.2 b post⟩


end AlgoLib.Experimental.RAM.Prototype.Composition
