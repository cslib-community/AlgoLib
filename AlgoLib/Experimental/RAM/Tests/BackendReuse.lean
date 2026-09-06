/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Authoring.Methods
import AlgoLib.Experimental.RAM.Tests.CreditLogic

/-!
# One logical proof, two executable RAM backends

`CreditLogic.four_correct` proves a four-credit contract without importing RAM.
Here a backend author realizes its one primitive in two ways: a direct increment,
and an increment with a scratch assignment. Both implement the exact same action.
The compiler reconstructs sequence and procedure certificates. The selected backend
infers bounds of 16 and 24 instructions; the logical method specifies only 4 credits.

This is an implementation-author example. Algorithm authors need only CreditLogic.lean.
Both executions use the verified RAM runner, with no supplied fuel or host evaluation
of the logical effect. Output decoding is a host-side observation of the final store.
-/
namespace AlgoLib.Experimental.RAM.Tests.BackendReuse
open Authoring Checked.Language CreditLogic

/-- A second backend uses extra scratch work but the same logical state. -/
def model (scratch : Bool) : Model Nat where
  Represents n s := s.vars .word "value" = n
  overhead := if scratch then 6 else 4

def value : Var .word := ⟨"value"⟩
def temp : Var .word := ⟨"scratch"⟩
def expression : Expr .word := .bin .add (.var value) (.lit 1)

/-- The primitive backend proof pays for every emitted instruction. -/
instance implementation (scratch : Bool) : ActionImplementation (model scratch) increment where
  implementation := if scratch then
    .seq (.assign temp (.lit 0)) (.assign value expression)
    else .assign value expression
  correct n s hs _ := by
    dsimp only [increment] at *
    cases scratch with
    | false =>
      refine ⟨4, _, Eval.assign value expression s, ?_, by decide⟩
      simpa [model, Store.set, expression, Expr.eval, Op.eval, Op.machine,
        Checked.BinOp.eval, value] using hs
    | true =>
      refine ⟨6, _, Eval.seq (Eval.assign temp (.lit 0) s)
        (Eval.assign value expression _), ?_, by decide⟩
      simpa [model, Store.set, expression, Expr.eval, Op.eval, Op.machine,
        Checked.BinOp.eval, value, temp] using hs

/-- Choose an implementation while keeping the same logical input/output view. -/
def interface (scratch : Bool) : Interface (model scratch) Nat Nat where
  initial n := n
  encode n := ⟨fun _ _ => n, fun _ => 0⟩
  prepare := .skip
  preparationCost _ := 0
  preparation _ := ⟨0, _, .skip _, rfl, Nat.le_refl _⟩
  decode _ s := s.vars .word "value"
  Observes n out := out = n
  output _ _ _ h := h

/-- A method declares logical credits only, regardless of its backend. -/
def method (scratch : Bool) : Authoring.Method (interface scratch) where
  body := four
  requires _ := True
  «ensures» n out := out = n + 4
  credits _ := 4

/-- Reuse the exact same algorithm proof for both backend choices. -/
theorem verification (scratch : Bool) : (method scratch).VCs := by
  intro n _
  exact four_correct.output_vc n (fun out => out = n + 4) 4 trivial (by rfl)
    (fun _ h _ view => view.trans h)

/-- All intermediate certificates are reconstructed, including nested procedure calls. -/
def certified (scratch : Bool) : VerifiedMethod (interface scratch) :=
  (method scratch).certify (verification scratch)

def run (scratch : Bool) (n : Nat) : Result Nat := (certified scratch).run n trivial

/-- One public theorem supplies both correctness and the inferred backend bound. -/
theorem correct (scratch : Bool) (n : Nat) :
    (run scratch n).value = n + 4 ∧ (run scratch n).steps ≤ (method scratch).time n :=
  (certified scratch).correct n trivial

example (n : Nat) : (method false).time n = 16 := rfl
example (n : Nat) : (method true).time n = 24 := rfl

/-- An abstract effect is not an executable implementation certificate. -/
def unimplemented : Action Nat where
  requires _ := True
  effect n := n + 100
  work _ := 0

example : True := by
  let logical : Program Nat := .action unimplemented
  fail_if_success
    have : Compilation (model false) logical := by ram_compile
  trivial

/- The emitted code really differs, not just the advertised conversion factor. -/
set_option linter.hashCommand false in
#eval show IO Unit from do
  let direct := run false 7
  let scratch := run true 7
  unless direct.value == 11 && direct.steps == 16 do
    throw <| IO.userError "direct backend failed"
  unless scratch.value == 11 && scratch.steps == 24 do
    throw <| IO.userError "scratch backend failed"

end AlgoLib.Experimental.RAM.Tests.BackendReuse
