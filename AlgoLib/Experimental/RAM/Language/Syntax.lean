/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Library.Array
import AlgoLib.Experimental.RAM.Language.VC
import Lean

/-!
# Paper-style syntax for arbitrary programs

Every production is compositional; there are no BFS-specific patterns. Lean
checks the types after expansion. Arrays, procedure calls, nested arithmetic,
conditionals, scoped variables, and loops can be freely combined. Identifiers resolve through
Lean's normal lexical scopes. `call` statically inlines a finite source command.
-/
namespace AlgoLib.Experimental.RAM.Checked.Language

class ToExpr (α : Type) (ty : outParam Ty) where
  toExpr : α → Expr ty

instance {ty : Ty} : ToExpr (Var ty) ty := ⟨Expr.var⟩
instance {ty : Ty} : ToExpr (Expr ty) ty := ⟨id⟩

def expression {α : Type} {ty : Ty} [ToExpr α ty] (a : α) : Expr ty := ToExpr.toExpr a

declare_syntax_cat paperExpr
syntax ident : paperExpr
syntax num : paperExpr
syntax "(" paperExpr ")" : paperExpr
syntax ident "[" paperExpr "]" : paperExpr
syntax:65 paperExpr:65 " + " paperExpr:66 : paperExpr
syntax:65 paperExpr:65 " - " paperExpr:66 : paperExpr
syntax:70 paperExpr:70 " * " paperExpr:71 : paperExpr
syntax "source_expr% " paperExpr : term

macro_rules
  | `(source_expr% $x:ident) => `(expression $x)
  | `(source_expr% $n:num) => `(Expr.lit (ty := .word) $n)
  | `(source_expr% ($x:paperExpr)) => `(source_expr% $x)
  | `(source_expr% $a:ident[$i:paperExpr]) => `(ArrayRef.cell $a (source_expr% $i))
  | `(source_expr% $x:paperExpr + $y:paperExpr) =>
    `(Expr.bin .add (source_expr% $x) (source_expr% $y))
  | `(source_expr% $x:paperExpr - $y:paperExpr) =>
    `(Expr.bin .sub (source_expr% $x) (source_expr% $y))
  | `(source_expr% $x:paperExpr * $y:paperExpr) =>
    `(Expr.bin .mul (source_expr% $x) (source_expr% $y))

declare_syntax_cat paperCond
syntax paperExpr " < " paperExpr : paperCond
syntax paperExpr " <= " paperExpr : paperCond
syntax paperExpr " == " paperExpr : paperCond
syntax "source_condition% " paperCond : term

macro_rules
  | `(source_condition% $x:paperExpr < $y:paperExpr) =>
    `(Condition.mk _ .lt (source_expr% $x) (source_expr% $y))
  | `(source_condition% $x:paperExpr <= $y:paperExpr) =>
    `(Condition.mk _ .le (source_expr% $x) (source_expr% $y))
  | `(source_condition% $x:paperExpr == $y:paperExpr) =>
    `(Condition.mk _ .eq (source_expr% $x) (source_expr% $y))

declare_syntax_cat paperStmt
syntax ident " := " paperExpr ";" : paperStmt
syntax ident " := " ident "(" paperExpr ")" ";" : paperStmt
syntax ident "[" paperExpr "]" " := " paperExpr ";" : paperStmt
syntax "if " paperCond " {" paperStmt* "}" "else" "{" paperStmt* "}" : paperStmt
syntax "while " paperCond " {" paperStmt* "}" : paperStmt
syntax "call " term ";" : paperStmt
syntax "local " ident " := " paperExpr " {" paperStmt* "}" : paperStmt
syntax "program" "{" paperStmt* "}" : term
syntax "source_statement% " paperStmt : term

macro_rules
  | `(source_statement% $out:ident := $p:ident($arg:paperExpr);) =>
    `(Procedure.call $p (source_expr% $arg) $out)
  | `(source_statement% $x:ident := $e:paperExpr;) => `(Cmd.assign $x (source_expr% $e))
  | `(source_statement% $a:ident[$i:paperExpr] := $e:paperExpr;) =>
    `(ArrayRef.put $a (source_expr% $i) (source_expr% $e))
  | `(source_statement% if $q:paperCond { $a:paperStmt* } else { $b:paperStmt* }) =>
    `(Cmd.branch (source_condition% $q) (program { $a* }) (program { $b* }))
  | `(source_statement% while $q:paperCond { $b:paperStmt* }) =>
    `(Cmd.loop (source_condition% $q) (program { $b* }))
  | `(source_statement% call $p:term;) => `($p)
  | `(source_statement% local $v:ident := $e:paperExpr { $b:paperStmt* }) =>
    `(Cmd.localVar $v (source_expr% $e) (program { $b* }))
  | `(program {}) => `(Cmd.skip)
  | `(program { $a:paperStmt $rest:paperStmt* }) =>
    `(Cmd.seq (source_statement% $a) (program { $rest* }))

macro "procedure" "(" input:ident ")" "returns" output:ident "{" body:paperStmt* "}" : term => do
  let fresh ← Lean.Macro.addMacroScope input.getId
  let name := Lean.quote fresh.toString
  `(let $input : Var _ := ⟨$name⟩
    { parameter := $input, body := fun $output => program { $body* } })

/-- Open the standard loop VCs or compose sequential time-credit triples. -/
macro "source_vc" : tactic =>
  `(tactic| first | apply LoopVC.mk | apply Triple.seq | apply Triple.assign | apply Triple.write)

end AlgoLib.Experimental.RAM.Checked.Language
