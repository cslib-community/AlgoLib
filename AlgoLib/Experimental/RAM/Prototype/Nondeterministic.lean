/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.VelvetSemantics

/-!
# Nondeterministic RAM and all-outcome translation contracts

`Code` extends the existing instruction semantics with choice of a natural word.
A choice is an actual charged instruction. A finite procedure table supports
recursive and mutually recursive control transfers: call and return cost one each.
All registers are shared; `call` saves no local variables or arrays. A compiler must
emit explicit loads and stores for activation data, and pay for them. In particular,
this semantics does not copy an unbounded register file as a constant-time step.

A choice is a primitive nondeterministic instruction; no Lean predicate or state transformer
is accepted as a machine operation. Unsupported predicates must be implemented by
ordinary code, whose execution cost is counted. The old deterministic RAM is
embedded without modifying its semantics or invalidating its determinism theorem.

`Translation` relates an actual ordinary Velvet method to one fixed target program.
Its two directions prohibit both lost and invented terminating outcomes. The
correctness transport theorem quantifies over every target execution; a successful
example run is never used as evidence of a worst-case cost or universal property.
-/
namespace AlgoLib.Experimental.RAM.Prototype.Nondeterministic
open Checked

inductive Code where
  | deterministic (code : Checked.Code)
  | choose (destination : Reg)
  | seq (first second : Code)
  | branch (test : Test) (yes no : Code)
  | loop (test : Test) (body : Code)
  | call (procedure : Nat)
  deriving Repr

/-- All finite executions, including every possible value of a choice instruction. -/
inductive ExecIn (procedures : List Code) : Code → State → Nat → State → Prop where
  | deterministic {code s k t} :
      Checked.Exec code s k t → ExecIn procedures (.deterministic code) s k t
  | choose (s : State) (r : Reg) (n : Nat) : ExecIn procedures (.choose r) s 1 (s.set r n)
  | seq {a b s u t i j} : ExecIn procedures a s i u → ExecIn procedures b u j t →
      ExecIn procedures (.seq a b) s (i+j) t
  | ifTrue {q a b s t k} : q.eval s = true → ExecIn procedures a s k t →
      ExecIn procedures (.branch q a b) s (1+k) t
  | ifFalse {q a b s t k} : q.eval s = false → ExecIn procedures b s k t →
      ExecIn procedures (.branch q a b) s (1+k) t
  | whileFalse {q b s} : q.eval s = false → ExecIn procedures (.loop q b) s 1 s
  | whileTrue {q b s u t i j} : q.eval s = true → ExecIn procedures b s i u →
      ExecIn procedures (.loop q b) u j t → ExecIn procedures (.loop q b) s (1+i+j) t
  | call {index body s t k} : procedures[index]? = some body →
      ExecIn procedures body s k t → ExecIn procedures (.call index) s (1 + k + 1) t

/-- Compatibility execution for programs with no procedure declarations. -/
abbrev Exec := ExecIn []

@[simp] theorem deterministic_iff {procedures : List Code} {code : Checked.Code}
    {s t : State} {k : Nat} :
    ExecIn procedures (.deterministic code) s k t ↔ Checked.Exec code s k t := by
  constructor
  · intro h; cases h with | deterministic h => exact h
  · exact .deterministic

/-- A certificate for the actual upstream method, not another program's WP. -/
structure Translation {Input Output : Type} (source : Input → VelvetM Output) where
  code : Code
  procedures : List Code := []
  encode : Input → State
  decode : State → Output
  valid : Input → Prop
  equivalent : ∀ input, valid input → ∀ output,
    VelvetSemantics.Returns (source input) output ↔
      ∃ steps final, ExecIn procedures code (encode input) steps final ∧ decode final = output

/-- Every actual target execution inherits every source outcome property. -/
theorem Translation.correct {Input Output : Type} {source : Input → VelvetM Output}
    (translation : Translation source) (input : Input) (valid : translation.valid input)
    (post : Output → Prop)
    (sourceCorrect : ∀ output, VelvetSemantics.Returns (source input) output → post output)
    {steps : Nat} {final : State}
    (run : ExecIn translation.procedures translation.code
      (translation.encode input) steps final) :
    post (translation.decode final) :=
  sourceCorrect _ ((translation.equivalent input valid _).mpr ⟨steps, final, run, rfl⟩)

/-- A separate *universal* execution bound is required for worst-case complexity. -/
def Translation.Within {Input Output : Type} {source : Input → VelvetM Output}
    (translation : Translation source) (budget : Input → Nat) : Prop :=
  ∀ input, translation.valid input → ∀ steps final,
    ExecIn translation.procedures translation.code (translation.encode input) steps final →
      steps ≤ budget input

/-- Correctness and cost concern the same execution, for every nondeterministic choice. -/
theorem Translation.correct_and_cost {Input Output : Type}
    {source : Input → VelvetM Output} (translation : Translation source)
    (budget : Input → Nat) (cost : translation.Within budget)
    (input : Input) (valid : translation.valid input) (post : Output → Prop)
    (sourceCorrect : ∀ output, VelvetSemantics.Returns (source input) output → post output)
    {steps : Nat} {final : State}
    (run : ExecIn translation.procedures translation.code
      (translation.encode input) steps final) :
    post (translation.decode final) ∧ steps ≤ budget input :=
  ⟨translation.correct input valid post sourceCorrect run, cost input valid steps final run⟩

/-- A source outcome gives a target execution; this alone is not demonic termination. -/
theorem Translation.realizes {Input Output : Type} {source : Input → VelvetM Output}
    (translation : Translation source) (input : Input) (valid : translation.valid input)
    {output : Output} (run : VelvetSemantics.Returns (source input) output) :
    ∃ steps final, ExecIn translation.procedures translation.code
      (translation.encode input) steps final ∧
      translation.decode final = output :=
  (translation.equivalent input valid output).mp run

end AlgoLib.Experimental.RAM.Prototype.Nondeterministic
