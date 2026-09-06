/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Observation
import AlgoLib.Experimental.RAM.Authoring.Semantics

/-!
# Backend-independent logical interpretation

`denote` interprets Authoring.Program in the costed computations of Observation.
`denote_iff_run` connects this independently defined monadic interpretation to
logical Run semantics, and `run_unique` establishes determinism.

This file imports no RAM model or compiler. Interpretation.lean supplies the
execution adapter; SupportedCompilation.lean connects the actual Loom WP to the
supported-language compiler theorem. Proof annotations do not affect `denote`.
-/
namespace AlgoLib.Experimental.RAM.Prototype
open Authoring

variable {State : Type}

/-- Mathematical interpretation of a certified library call. -/
def action (a : Action State) : Computation State Unit := fun s k t _ =>
  a.requires s ∧ k = a.work s ∧ t = a.effect s

/-- Independently specified source interpretation; loops mean finite iterations. -/
def denote : Program State → Computation State Unit
  | .skip => Computation.pure ()
  | .action a => action a
  | .seq a b => Computation.bind (denote a) (fun _ => denote b)
  | .branch q a b => fun s k t _ => ∃ j, k = 1 + j ∧
      if q.test s then denote a s j t () else denote b s j t ()
  | .loop q b => Computation.Loop q.test (denote b)

theorem denote_run (p : Program State) {s t : State} {k : Nat}
    (h : denote p s k t ()) : Run p s k t := by
  induction p generalizing s t k with
  | skip => obtain ⟨rfl, rfl, _⟩ := h; exact .skip _
  | action a => obtain ⟨ha, rfl, rfl⟩ := h; exact .action a s ha
  | seq a b iha ihb =>
    obtain ⟨i, u, x, j, ha, hb, rfl⟩ := h
    cases x
    exact .seq (iha ha) (ihb hb)
  | branch q a b iha ihb =>
    obtain ⟨j, rfl, hj⟩ := h
    cases hq : q.test s with
    | true => exact .ifTrue hq (iha (by simpa [hq] using hj))
    | false => exact .ifFalse hq (ihb (by simpa [hq] using hj))
  | loop q b ihb =>
    change Computation.Loop q.test (denote b) s k t () at h
    generalize () = x at h
    induction h with
    | done hq => exact .whileFalse hq
    | step hq hb _ ih => exact .whileTrue hq (ihb hb) ih

theorem run_denote {p : Program State} {s t : State} {k : Nat}
    (h : Run p s k t) : denote p s k t () := by
  induction h with
  | skip => exact ⟨rfl, rfl, rfl⟩
  | action a s ha => exact ⟨ha, rfl, rfl⟩
  | seq _ _ iha ihb => exact ⟨_, _, (), _, iha, ihb, rfl⟩
  | ifTrue hq _ ih => exact ⟨_, rfl, by simpa [hq] using ih⟩
  | ifFalse hq _ ih => exact ⟨_, rfl, by simpa [hq] using ih⟩
  | whileFalse hq => exact .done hq
  | whileTrue hq _ _ ihb ihl => exact .step hq ihb ihl

theorem denote_iff_run (p : Program State) (s t : State) (k : Nat) :
    denote p s k t () ↔ Run p s k t := ⟨denote_run p, run_denote⟩

/-- Supported source programs have a unique terminating result and logical cost. -/
theorem run_unique {p : Program State} {s t t' : State} {k k' : Nat}
    (h : Run p s k t) (h' : Run p s k' t') : k = k' ∧ t = t' := by
  induction h generalizing k' t' with
  | skip => cases h'; exact ⟨rfl, rfl⟩
  | action => cases h'; exact ⟨rfl, rfl⟩
  | seq _ _ iha ihb =>
    cases h' with
    | seq ha hb =>
      obtain ⟨rfl, rfl⟩ := iha ha
      obtain ⟨rfl, rfl⟩ := ihb hb
      exact ⟨rfl, rfl⟩
  | ifTrue hq _ ih =>
    cases h' with
    | ifTrue _ hb => obtain ⟨rfl, rfl⟩ := ih hb; exact ⟨rfl, rfl⟩
    | ifFalse hn _ => simp_all
  | ifFalse hq _ ih =>
    cases h' with
    | ifTrue hn _ => simp_all
    | ifFalse _ hb => obtain ⟨rfl, rfl⟩ := ih hb; exact ⟨rfl, rfl⟩
  | whileFalse hq =>
    cases h' with
    | whileFalse => exact ⟨rfl, rfl⟩
    | whileTrue hn => simp_all
  | whileTrue hq _ _ ihb ihl =>
    cases h' with
    | whileFalse hn => simp_all
    | whileTrue _ hb hl =>
      obtain ⟨rfl, rfl⟩ := ihb hb
      obtain ⟨rfl, rfl⟩ := ihl hl
      exact ⟨rfl, rfl⟩

/-- Existential observation cannot pick a favorable execution of this language. -/
theorem denote_deterministic {p : Program State} {s t t' : State} {k k' : Nat}
    (h : denote p s k t ()) (h' : denote p s k' t' ()) : k = k' ∧ t = t' :=
  run_unique (denote_run p h) (denote_run p h')

end AlgoLib.Experimental.RAM.Prototype
