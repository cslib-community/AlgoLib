/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Backend.Language.Verification

/-!
# Internal command normalization

Normalizes command structure and proves evaluation transport between equivalent normalized
programs.

Used to reuse earlier implementation certificates. Normalization equalities are never obligations
for canonical Programs authors.

## Further details

# Cost-preserving normalization for compositional program refinement
-/
namespace AlgoLib.Experimental.RAM.Checked.Language

def Cmd.append : Cmd → Cmd → Cmd
  | .skip, b => b
  | .seq a b, c => .seq a (b.append c)
  | a, b => .seq a b

theorem Eval.append_iff (a b : Cmd) (s t : Store) (k : Nat) :
    Eval (a.append b) s k t ↔ Eval (.seq a b) s k t := by
  induction a generalizing s t k with
  | skip =>
    constructor
    · intro h; simpa using Eval.seq (.skip s) h
    · intro h; cases h with | seq ha hb => cases ha; simpa using hb
  | seq a c iha ihc =>
    constructor
    · intro h
      cases h with
      | seq ha hcb =>
        obtain ⟨⟩ := (ihc _ _ _).mp hcb
        rename_i hc hb
        simpa [Nat.add_assoc] using Eval.seq (Eval.seq ha hc) hb
    · intro h
      cases h with
      | seq hac hb =>
        cases hac with
        | seq ha hc =>
          simpa [Nat.add_assoc] using Eval.seq ha ((ihc _ _ _).mpr (Eval.seq hc hb))
  | assign | write | branch | loop | localVar => rfl

def Cmd.normalize : Cmd → Cmd
  | .skip => .skip
  | .seq a b => a.normalize.append b.normalize
  | .branch q a b => .seq (.branch q a.normalize b.normalize) .skip
  | .loop q b => .seq (.loop q b.normalize) .skip
  | .localVar v e b => .seq (.localVar v e b.normalize) .skip
  | a => .seq a .skip

theorem Eval.seq_skip {a : Cmd} {s t : Store} {k : Nat} :
    Eval (.seq a .skip) s k t ↔ Eval a s k t := by
  constructor
  · intro h; cases h with | seq ha hb => cases hb; simpa using ha
  · intro h; simpa using Eval.seq h (.skip t)

theorem Eval.normalize {c : Cmd} {s t : Store} {k : Nat} (h : Eval c s k t) :
    Eval c.normalize s k t := by
  induction h with
  | skip => exact .skip _
  | assign => exact Eval.seq_skip.mpr (.assign _ _ _)
  | write => exact Eval.seq_skip.mpr (.write _ _ _)
  | seq ha hb iha ihb => exact (Eval.append_iff _ _ _ _ _).mpr (.seq iha ihb)
  | ifTrue hq hb ih => exact Eval.seq_skip.mpr (.ifTrue hq ih)
  | ifFalse hq hb ih => exact Eval.seq_skip.mpr (.ifFalse hq ih)
  | whileFalse hq => exact Eval.seq_skip.mpr (.whileFalse hq)
  | whileTrue hq hb hl ihb ihl =>
    exact Eval.seq_skip.mpr (.whileTrue hq ihb (Eval.seq_skip.mp ihl))
  | localVar hb ih => exact Eval.seq_skip.mpr (.localVar ih)

theorem Eval.of_normalize {c : Cmd} {s t : Store} {k : Nat}
    (h : Eval c.normalize s k t) : Eval c s k t := by
  induction c generalizing s t k with
  | skip => exact h
  | assign | write => exact Eval.seq_skip.mp h
  | seq a b iha ihb =>
    cases (Eval.append_iff _ _ _ _ _).mp h with
    | seq ha hb => exact .seq (iha ha) (ihb hb)
  | branch q a b iha ihb =>
    cases Eval.seq_skip.mp h with
    | ifTrue hq ha => exact .ifTrue hq (iha ha)
    | ifFalse hq hb => exact .ifFalse hq (ihb hb)
  | localVar v e b ih =>
    cases Eval.seq_skip.mp h with
    | localVar hb => exact .localVar (ih hb)
  | loop q b ihb =>
    have loop : ∀ k s t, Eval (.loop q b.normalize) s k t → Eval (.loop q b) s k t := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
        intro s t hx
        cases hx with
        | whileFalse hq => exact .whileFalse hq
        | @whileTrue _ _ _ u _ i j hq hb hl =>
          have hpos := q.cost_pos
          exact .whileTrue hq (ihb hb) (ih j (by omega) u t hl)
    exact loop _ _ _ (Eval.seq_skip.mp h)

/-- Layout and grouping of source blocks cannot change their semantics or cost. -/
theorem Eval.transfer {a b : Cmd} (same : a.normalize = b.normalize)
    {s t : Store} {k : Nat} (h : Eval a s k t) : Eval b s k t :=
  Eval.of_normalize (same ▸ h.normalize)

end AlgoLib.Experimental.RAM.Checked.Language
