/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.LoopVC
import Lean

/-!
# Textbook imperative notation

`imperative { ... }` elaborates to `Source.Stmt`, never directly to an
unrestricted Lean computation. Identifiers denote named `Reg` constants;
`A[address]` denotes RAM memory. Expressions are deliberately flat: a literal,
a variable, a memory read, or one arithmetic operation on atomic operands.
Use another assignment for a compound expression. `call helper;` inlines a
source statement whose compilation is subject to the same verified compiler.

Loop annotations are ordinary Lean terms, checked by `Source.VC`.
Loops without inline annotations are intended for external, modular `LoopVC`
proofs with ghost views and time potentials. Their placeholder annotations do
not certify termination: a true iteration cannot pass `Source.VC` with rank zero. The macros
are untrusted conveniences: the generated `Stmt` and all subsequent proofs
are checked by Lean's kernel.
-/

namespace AlgoLib.Experimental.RAM.Checked.Source

open Lean

declare_syntax_cat ramAtom
syntax ident : ramAtom
syntax num : ramAtom

declare_syntax_cat ramExpr
syntax ramAtom : ramExpr
syntax "A[" ramAtom "]" : ramExpr
syntax ramAtom " + " ramAtom : ramExpr
syntax ramAtom " - " ramAtom : ramExpr
syntax ramAtom " * " ramAtom : ramExpr

declare_syntax_cat ramTest
syntax ramAtom " < " ramAtom : ramTest
syntax ramAtom " <= " ramAtom : ramTest
syntax ramAtom " == " ramAtom : ramTest
syntax ramAtom " > " ramAtom : ramTest

declare_syntax_cat ramStmt
syntax ident " := " ramExpr ";" : ramStmt
syntax "A[" ramAtom "]" " := " ramAtom ";" : ramStmt
syntax "if " ramTest " {" ramStmt* "}" " else " "{" ramStmt* "}" : ramStmt
syntax "while " ramTest " {" ramStmt* "}" : ramStmt
syntax "while " ramTest " invariant " term:max " decreases " term:max " {" ramStmt* "}" : ramStmt
syntax "call " ident ";" : ramStmt

syntax "ram_atom% " ramAtom : term
syntax "ram_expr% " ramExpr : term
syntax "ram_test% " ramTest : term

macro_rules
  | `(ram_atom% $x:ident) => `(Operand.reg $x)
  | `(ram_atom% $n:num) => `(Operand.lit $n)
  | `(ram_expr% $a:ramAtom) => `(Expr.atom (ram_atom% $a))
  | `(ram_expr% A[$a:ramAtom]) => `(Expr.load (ram_atom% $a))
  | `(ram_expr% $a:ramAtom + $b:ramAtom) => `(Expr.bin .add (ram_atom% $a) (ram_atom% $b))
  | `(ram_expr% $a:ramAtom - $b:ramAtom) => `(Expr.bin .sub (ram_atom% $a) (ram_atom% $b))
  | `(ram_expr% $a:ramAtom * $b:ramAtom) => `(Expr.bin .mul (ram_atom% $a) (ram_atom% $b))
  | `(ram_test% $a:ramAtom < $b:ramAtom) => `(Test.lt (ram_atom% $a) (ram_atom% $b))
  | `(ram_test% $a:ramAtom <= $b:ramAtom) => `(Test.le (ram_atom% $a) (ram_atom% $b))
  | `(ram_test% $a:ramAtom == $b:ramAtom) => `(Test.eq (ram_atom% $a) (ram_atom% $b))
  | `(ram_test% $a:ramAtom > $b:ramAtom) => `(Test.lt (ram_atom% $b) (ram_atom% $a))

private def expandSimple (s : TSyntax `ramStmt) : MacroM (Option (TSyntax `term)) := do
  match s with
  | `(ramStmt| $r:ident := $e:ramExpr;) => return some (← `(Simple.assign $r (ram_expr% $e)))
  | `(ramStmt| A[$a:ramAtom] := $v:ramAtom;) =>
    return some (← `(Simple.store (ram_atom% $a) (ram_atom% $v)))
  | _ => return none

/-- Group adjacent assignments into blocks, keeping the source program compact. -/
private partial def expandBlock (ss : Array (TSyntax `ramStmt)) : MacroM (TSyntax `term) := do
  let mut leading : Array (TSyntax `term) := #[]
  let mut i := 0
  while i < ss.size do
    match ← expandSimple ss[i]! with
    | some a => leading := leading.push a; i := i + 1
    | none => break
  if i = ss.size then
    return ← `(Stmt.block [$leading,*])
  let main ← match ss[i]! with
    | `(ramStmt| if $q:ramTest { $yes:ramStmt* } else { $no:ramStmt* }) =>
      `(Stmt.ite (ram_test% $q) $(← expandBlock yes) $(← expandBlock no))
    | `(ramStmt| while $q:ramTest invariant $inv:term decreases $rank:term { $body:ramStmt* }) =>
      `(Stmt.loop (ram_test% $q) $inv $rank $(← expandBlock body))
    | `(ramStmt| while $q:ramTest { $body:ramStmt* }) =>
      `(Stmt.loop (ram_test% $q) (fun _ _ => True) (fun _ => 0) $(← expandBlock body))
    | `(ramStmt| call $name:ident;) => pure (⟨name.raw⟩ : TSyntax `term)
    | other => Macro.throwErrorAt other "expected an assignment, conditional, loop, or call"
  let result ← if i + 1 = ss.size then pure main
    else `(Stmt.seq $main $(← expandBlock (ss.extract (i + 1) ss.size)))
  if leading.isEmpty then return result
  else return ← `(Stmt.seq (Stmt.block [$leading,*]) $result)

macro "imperative" " {" ss:ramStmt* "}" : term => expandBlock ss

/-- Generate exit and maintenance/time goals for a modular `LoopVC`, or expand
inline source obligations and fixed assignments. Users supply mathematical
invariants and finish the resulting goals with ordinary Lean proofs. -/
macro "vcgen" : tactic =>
  `(tactic| first
    | apply LoopVC.mk
    | simp [VC, block, Simple.eval, Expr.eval, State.set,
        Operand.eval, BinOp.eval, Test.eval])


macro "method" " requires " P:term:max " ensures " Q:term:max
    " {" ss:ramStmt* "}" " verified_by " h:term:max : term => do
  `(Method.mk $(← expandBlock ss) $P $Q $h)

end AlgoLib.Experimental.RAM.Checked.Source
