/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Semantics

/-!
# Authoring syntax and credit automation

Parses each call, branch, and loop compositionally into Program. The paper_steps tactic
substitutes public logical contracts, while Credits packages reusable finite charging arguments.

Register operation equations with paper_simps in a public Library module. No tactic here discovers
an algorithm invariant or trusts an external solver.
-/
namespace AlgoLib.Experimental.RAM.Authoring

declare_syntax_cat mathStmt
syntax "call " term ";" : mathStmt
syntax "while " "(" term ")" " {" mathStmt* "}" : mathStmt
syntax "if " "(" term ")" " {" mathStmt* "}" "else" "{" mathStmt* "}" : mathStmt
syntax "paper" "{" mathStmt* "}" : term
syntax "paper_statement% " mathStmt : term
macro_rules
  | `(paper_statement% call $a;) => `(Program.action $a)
  | `(paper_statement% while ($q) { $body:mathStmt* }) =>
      `(Program.loop $q (paper { $body* }))
  | `(paper_statement% if ($q) { $yes:mathStmt* } else { $no:mathStmt* }) =>
      `(Program.branch $q (paper { $yes* }) (paper { $no* }))
  | `(paper {}) => `(Program.skip)
  | `(paper { $a:mathStmt }) => `(paper_statement% $a)
  | `(paper { $a:mathStmt $b:mathStmt $rest:mathStmt* }) =>
      `(Program.seq (paper_statement% $a) (paper { $b $rest* }))

/-- Expand control flow, substitute certified effects, and collect all payments.
The explicit list contains logical API definitions, never compiler lemmas. -/
register_simp_attr paper_simps

macro "paper_steps" " [" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [VC, Procedure.call, paper_simps, $ds,*] at *)

/-- Solve routine natural-number credit inequalities after the algorithmic
charging identity has been supplied. Failure leaves the mathematical goal. -/
macro "paper_credits" : tactic =>
  `(tactic| (simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul,
    Nat.mul_zero, Nat.zero_mul] at *; omega))

namespace Credits
/-- Allocate a reusable budget to every item not yet processed. -/
def remaining (items done : Finset Nat) (charge : Nat → Nat) : Nat :=
  ∑ x ∈ items \ done, charge x

theorem remove (items done : Finset Nat) (charge : Nat → Nat) {x : Nat}
    (hx : x ∈ items) (fresh : x ∉ done) :
    remaining items (insert x done) charge + charge x = remaining items done charge := by
  have he : items \ insert x done = (items \ done).erase x := by ext; simp; tauto
  unfold remaining
  rw [he]
  exact Finset.sum_erase_add _ _ (by simp [hx, fresh])

@[simp] theorem empty (items : Finset Nat) (charge : Nat → Nat) :
    remaining items ∅ charge = ∑ x ∈ items, charge x := by simp [remaining]
end Credits
end AlgoLib.Experimental.RAM.Authoring
