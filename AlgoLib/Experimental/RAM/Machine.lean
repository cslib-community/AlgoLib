/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

/-!
# A RAM language with enforced operation counts

`Code` is first-order syntax. Operands are literals or registers, never Lean
functions. A block executes one unit-cost instruction per list entry; a test
and conditional transfer cost one unit. `Exec` derives the time from these
rules. Machine state has no clock to overwrite, and the language has no way
to insert a caller-supplied state transformer or cost annotation.

This is a structured unit-cost natural-number RAM with eight named registers,
unbounded addressed memory, saturating subtraction, and unbounded arithmetic.
Names are conveniences; all registers have the same machine semantics. The
choice of word arithmetic is part of the model, not a bit-complexity claim.
Sequence bookkeeping is free. Each while guard, including its final false
test, is charged. `Prefix` and its composition lemmas support ordinary loop
proofs without exposing program counters.

A complexity theorem must quantify over one fixed `Code` before quantifying
over runtime inputs. Input-dependent code generation or a nonstandard input
encoding is not an implementation of that uniform algorithm.
-/

namespace AlgoLib.Experimental.RAM.Checked

/-- A fixed finite register bank; names make the sorting program readable. -/
inductive Reg where
  | base | count | limit | cursor | key | next | temp | live
  deriving DecidableEq, Repr

/-- There is no time field in the machine state. -/
structure State where
  regs : Reg → Nat
  memory : Nat → Nat

/-- Atomic operands prohibit hiding computation inside expression evaluation. -/
inductive Operand where
  | reg (r : Reg)
  | lit (n : Nat)
  deriving DecidableEq, Repr

def Operand.eval (s : State) : Operand → Nat
  | .reg r => s.regs r
  | .lit n => n

inductive BinOp where
  | add | sub | mul
  deriving DecidableEq, Repr

def BinOp.eval : BinOp → Nat → Nat → Nat
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- Each instruction has a constant number of atomic operands. -/
inductive Instr where
  | mov (dst : Reg) (src : Operand)
  | load (dst : Reg) (addr : Operand)
  | store (addr value : Operand)
  | bin (op : BinOp) (dst : Reg) (x y : Operand)
  deriving DecidableEq, Repr

def State.set (s : State) (r : Reg) (v : Nat) : State :=
  { s with regs := Function.update s.regs r v }

def Instr.eval (i : Instr) (s : State) : State :=
  match i with
  | .mov r x => s.set r (x.eval s)
  | .load r a => s.set r (s.memory (a.eval s))
  | .store a x => { s with memory := Function.update s.memory (a.eval s) (x.eval s) }
  | .bin op r x y => s.set r (op.eval (x.eval s) (y.eval s))

/-- Evaluation performs exactly the listed instructions. -/
def blockEval (is : List Instr) (s : State) : State := is.foldl (fun t i => i.eval t) s

inductive Test where
  | lt (x y : Operand)
  | le (x y : Operand)
  | eq (x y : Operand)
  deriving DecidableEq, Repr

def Test.eval (s : State) : Test → Bool
  | .lt x y => decide (x.eval s < y.eval s)
  | .le x y => decide (x.eval s ≤ y.eval s)
  | .eq x y => decide (x.eval s = y.eval s)

/-- Finite structured code, including potentially nonterminating loops. -/
inductive Code where
  | block (is : List Instr)
  | seq (first second : Code)
  | ite (test : Test) (yes no : Code)
  | while (test : Test) (body : Code)
  deriving DecidableEq, Repr

/-- Terminating execution in exactly the indicated number of machine operations.
There is no rule allowing arbitrary computation or an arbitrary time charge. -/
inductive Exec : Code → State → Nat → State → Prop where
  | block (is : List Instr) (s : State) : Exec (.block is) s is.length (blockEval is s)
  | seq {a b : Code} {s u t : State} {i j : Nat} :
      Exec a s i u → Exec b u j t → Exec (.seq a b) s (i + j) t
  | ifTrue {q : Test} {a b : Code} {s t : State} {i : Nat} :
      q.eval s = true → Exec a s i t → Exec (.ite q a b) s (1 + i) t
  | ifFalse {q : Test} {a b : Code} {s t : State} {i : Nat} :
      q.eval s = false → Exec b s i t → Exec (.ite q a b) s (1 + i) t
  | whileFalse {q : Test} {b : Code} {s : State} :
      q.eval s = false → Exec (.while q b) s 1 s
  | whileTrue {q : Test} {b : Code} {s u t : State} {i j : Nat} :
      q.eval s = true → Exec b s i u → Exec (.while q b) u j t →
      Exec (.while q b) s (1 + i + j) t

/-- A proved execution fixes both the result and the cost. -/
theorem Exec.deterministic {c : Code} {s t : State} {i : Nat} (h : Exec c s i t) :
    ∀ {j u}, Exec c s j u → i = j ∧ t = u := by
  induction h with
  | block is s => intro j u h; cases h; exact ⟨rfl, rfl⟩
  | seq ha hb iha ihb =>
    intro j u h
    cases h with
    | seq ha' hb' =>
      obtain ⟨rfl, rfl⟩ := iha ha'
      obtain ⟨rfl, rfl⟩ := ihb hb'
      exact ⟨rfl, rfl⟩
  | ifTrue hq ha ih =>
    intro j u h
    cases h with
    | ifTrue _ ha' => obtain ⟨rfl, rfl⟩ := ih ha'; exact ⟨rfl, rfl⟩
    | ifFalse hq' _ => simp_all
  | ifFalse hq ha ih =>
    intro j u h
    cases h with
    | ifTrue hq' _ => simp_all
    | ifFalse _ ha' => obtain ⟨rfl, rfl⟩ := ih ha'; exact ⟨rfl, rfl⟩
  | whileFalse hq =>
    intro j u h
    cases h with
    | whileFalse _ => exact ⟨rfl, rfl⟩
    | whileTrue hq' _ _ => simp_all
  | whileTrue hq ha hb iha ihb =>
    intro j u h
    cases h with
    | whileFalse hq' => simp_all
    | whileTrue _ ha' hb' =>
      obtain ⟨rfl, rfl⟩ := iha ha'
      obtain ⟨rfl, rfl⟩ := ihb hb'
      exact ⟨rfl, rfl⟩

/-- No zero-step execution can change even one register or memory cell. -/
theorem Exec.zero {c : Code} {s t : State} (h : Exec c s 0 t) : t = s := by
  generalize hz : 0 = n at h
  induction h with
  | block is s => cases is <;> simp_all [blockEval]
  | seq ha hb iha ihb =>
    have hi : _ = 0 := Nat.eq_zero_of_add_eq_zero_left hz.symm
    have hj : _ = 0 := Nat.eq_zero_of_add_eq_zero_right hz.symm
    exact (ihb hi.symm).trans (iha hj.symm)
  | ifTrue | ifFalse | whileFalse | whileTrue => omega

/-- A sequence of true loop iterations, with the exit test left to the caller. -/
inductive Prefix (q : Test) (body : Code) : State → Nat → State → Prop where
  | refl (s : State) : Prefix q body s 0 s
  | snoc {s u t : State} {i j : Nat} :
      Prefix q body s i u → q.eval u = true → Exec body u j t →
      Prefix q body s (i + 1 + j) t

/-- Append a complete loop execution to a prefix. -/
theorem Prefix.then_loop {q : Test} {body : Code} {s u : State} {i : Nat}
    (h : Prefix q body s i u) {t : State} {j : Nat}
    (ht : Exec (.while q body) u j t) : Exec (.while q body) s (i + j) t := by
  induction h generalizing t j with
  | refl => simpa using ht
  | snoc hp hq hb ih =>
    simpa [Nat.add_assoc] using ih (Exec.whileTrue hq hb ht)

/-- A false guard completes a prefix, charging its final test. -/
theorem Prefix.finish {q : Test} {body : Code} {s t : State} {i : Nat}
    (h : Prefix q body s i t) (hq : q.eval t = false) :
    Exec (.while q body) s (i + 1) t := h.then_loop (.whileFalse hq)

/-- Prepend one iteration even when a command follows the loop. -/
theorem Exec.while_seq_step {q : Test} {body after : Code} {s u t : State} {i j : Nat}
    (hq : q.eval s = true) (hb : Exec body s i u)
    (ht : Exec (.seq (.while q body) after) u j t) :
    Exec (.seq (.while q body) after) s (1 + i + j) t := by
  cases ht with
  | seq hloop hafter =>
    simpa [Nat.add_assoc] using Exec.seq (Exec.whileTrue hq hb hloop) hafter

/-- A client contract combines a genuine execution, a postcondition, and its time bound. -/
def Ensures (P : State → Prop) (c : Code) (Q : State → Prop) (budget : Nat) : Prop :=
  ∀ s, P s → ∃ k t, Exec c s k t ∧ Q t ∧ k ≤ budget

theorem Ensures.seq {P Q R : State → Prop} {a b : Code} {i j : Nat}
    (ha : Ensures P a Q i) (hb : Ensures Q b R j) :
    Ensures P (.seq a b) R (i + j) := by
  intro s hs
  obtain ⟨x, u, hx, hu, hi⟩ := ha s hs
  obtain ⟨y, t, hy, ht, hj⟩ := hb u hu
  exact ⟨x + y, t, .seq hx hy, ht, Nat.add_le_add hi hj⟩


/-- An executable interpreter. Fuel limits evaluator recursion depth, not RAM
operations. `none` means insufficient fuel; successful results report the
instruction count fixed by `Exec`. Fuel and host evaluation time are not part
of machine state or available to a RAM program. -/
def run : Nat → Code → State → Option (Nat × State)
  | 0, _, _ => none
  | _ + 1, .block is, s => some (is.length, blockEval is s)
  | fuel + 1, .seq a b, s => do
    let (i, u) ← run fuel a s
    let (j, t) ← run fuel b u
    return (i + j, t)
  | fuel + 1, .ite q a b, s => do
    let (i, t) ← run fuel (if q.eval s then a else b) s
    return (1 + i, t)
  | fuel + 1, .while q b, s =>
    if q.eval s then do
      let (i, u) ← run fuel b s
      let (j, t) ← run fuel (.while q b) u
      return (1 + i + j, t)
    else some (1, s)

/-- Every successful interpreter result is a genuine execution with that cost. -/
theorem run_sound {fuel : Nat} {c : Code} {s t : State} {k : Nat}
    (h : run fuel c s = some (k, t)) : Exec c s k t := by
  induction fuel generalizing c s t k with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases c with
    | block is =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .block _ _
    | seq a b =>
      cases ha : run fuel a s with
      | none => simp [run, ha] at h
      | some r =>
        obtain ⟨i, u⟩ := r
        cases hb : run fuel b u with
        | none => simp [run, ha, hb] at h
        | some r =>
          obtain ⟨j, v⟩ := r
          have heq : i + j = k ∧ v = t := by simpa [run, ha, hb] using h
          obtain ⟨rfl, rfl⟩ := heq
          exact .seq (ih ha) (ih hb)
    | ite q a b =>
      cases hq : q.eval s <;>
        cases hr : run fuel (if q.eval s then a else b) s with
        | none => simp [run, hr] at h
        | some r =>
          obtain ⟨i, u⟩ := r
          have heq : 1 + i = k ∧ u = t := by simpa [run, hr] using h
          obtain ⟨rfl, rfl⟩ := heq
          first
          | exact .ifTrue hq (ih (by simpa [hq] using hr))
          | exact .ifFalse hq (ih (by simpa [hq] using hr))
    | «while» q b =>
      cases hq : q.eval s with
      | false =>
        simp only [run, hq, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .whileFalse hq
      | true =>
        cases hb : run fuel b s with
        | none => simp [run, hq, hb] at h
        | some r =>
          obtain ⟨i, u⟩ := r
          cases hw : run fuel (.while q b) u with
          | none => simp [run, hq, hb, hw] at h
          | some r =>
            obtain ⟨j, v⟩ := r
            have heq : 1 + i + j = k ∧ v = t := by simpa [run, hq, hb, hw] using h
            obtain ⟨rfl, rfl⟩ := heq
            exact .whileTrue hq (ih hb) (ih hw)


/-- Conversely, every terminating execution is reproduced by the interpreter
with sufficiently large fuel. Extra fuel never changes the derived result. -/
theorem Exec.run_complete {c : Code} {s t : State} {k : Nat} (h : Exec c s k t) :
    ∃ fuel, ∀ extra, run (fuel + extra) c s = some (k, t) := by
  induction h with
  | block is s =>
    refine ⟨1, fun extra => ?_⟩
    rw [Nat.add_comm]
    rfl
  | @seq a b s u t i j ha hb iha ihb =>
    obtain ⟨f, hf⟩ := iha
    obtain ⟨g, hg⟩ := ihb
    refine ⟨f + g + 1, fun extra => ?_⟩
    have hfa : run (f + g + extra) a s = some (i, u) := by
      simpa [Nat.add_assoc] using hf (g + extra)
    have hgb : run (f + g + extra) b u = some (j, t) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg (f + extra)
    rw [show f + g + 1 + extra = (f + g + extra) + 1 by omega]
    simp [run, hfa, hgb]
  | ifTrue hq ha ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, fun extra => ?_⟩
    rw [show f + 1 + extra = (f + extra) + 1 by omega]
    simp [run, hq, hf]
  | ifFalse hq ha ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, fun extra => ?_⟩
    rw [show f + 1 + extra = (f + extra) + 1 by omega]
    simp [run, hq, hf]
  | whileFalse hq =>
    refine ⟨1, fun extra => ?_⟩
    rw [Nat.add_comm]
    simp [run, hq]
  | @whileTrue q b s u t i j hq ha hb iha ihb =>
    obtain ⟨f, hf⟩ := iha
    obtain ⟨g, hg⟩ := ihb
    refine ⟨f + g + 1, fun extra => ?_⟩
    have hfa : run (f + g + extra) b s = some (i, u) := by
      simpa [Nat.add_assoc] using hf (g + extra)
    have hgb : run (f + g + extra) (.while q b) u = some (j, t) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg (f + extra)
    rw [show f + g + 1 + extra = (f + g + extra) + 1 by omega]
    simp [run, hq, hfa, hgb]

end AlgoLib.Experimental.RAM.Checked
