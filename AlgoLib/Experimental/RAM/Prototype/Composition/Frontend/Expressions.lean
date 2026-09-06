/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Frontend.Resources

/-!
# Expression and condition elaboration

Checks scalar expressions, array access, receiver queries, source locations, and their inferred
charges. Emitted fragments still require verified implementation certificates.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
open Lean Elab Command Term Meta Parser

partial def mentions (rs : Array Resource) (s : Syntax) : Bool :=
  (s.isIdent && rs.any (fun r => r.name.getId.isPrefixOf s.getId)) ||
    s.getArgs.any (mentions rs)

partial def liftQuery (rs : Array Resource) (i : Nat) (q : Term) : TermElabM Term := do
  if rs.size == 1 then return q
  let n := splitAt rs
  if i < n then `(testLeft $(← liftQuery (rs.extract 0 n) i q))
  else `(testRight $(← liftQuery (rs.extract n rs.size) (i - n) q))

partial def checkStatic (rs : Array Resource) (term : Syntax) : TermElabM Unit := do
  if term.isIdent then
    for r in rs do
      let n := term.getId
      if r.name.getId.isPrefixOf n || (r.name.getId.appendAfter "Old").isPrefixOf n then
        throwErrorAt term
          "Procedure arguments describe fixed code. Runtime input '{r.name}' must pass through a \
        certified typed operation"
  for child in term.getArgs do checkStatic rs child

def items (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Parser.Term.doSeqBracketed then stx[1].getArgs.map (·[0])
  else if stx.getKind == ``Parser.Term.doSeqIndent then stx[0].getArgs.map (·[0])
  else #[]

def receiverApplication (e : Term) : TermElabM (Ident × Array Term) := do
  let (head, args) ← match e with
    | `($f:ident $args:term*) => pure (f, args)
    | `($f:ident) => pure (f, #[])
    | _ => throwErrorAt e "Use a receiver call or assign a verified procedure"
  let mut actual : Array Term := #[]
  for arg in args do
    match arg with
    | `(()) => pure ()
    | `(($a:term, $b:term)) => actual := actual ++ #[a, b]
    | `(($a:term)) => actual := actual.push a
    | _ => actual := actual.push arg
  return (head, actual)

partial def path (rs : Array Resource) (i : Nat) : TermElabM Term := do
  if rs.size == 1 then return ← `(Path.here)
  let n := splitAt rs
  if i < n then `(Path.left $(← path (rs.extract 0 n) i))
  else `(Path.right $(← path (rs.extract n rs.size) (i - n)))

def resource (rs : Array Resource) (active : Array Name) (x : Ident) : TermElabM Nat := do
  let some i := rs.findIdx? (fun r => r.name.getId == x.getId)
    | throwErrorAt x "Unknown mutable variable '{x}'"
  unless active.contains x.getId do throwErrorAt x "Local '{x}' is not in scope"
  return i

def isNat (r : Resource) : Bool :=
  r.type.raw.isIdent && r.type.raw.getId.eraseMacroScopes == `Nat

partial def expression (rs : Array Resource) (active : Array Name) (e : Term) :
    TermElabM Term := withRef e do
  match e with
  | `(($e:term)) => expression rs active e
  | `($n:num) => `(Value.literal $n)
  | `($a:term + $b:term) =>
    `(Value.binary .add $(← expression rs active a) $(← expression rs active b))
  | `($a:term - $b:term) =>
    `(Value.binary .sub $(← expression rs active a) $(← expression rs active b))
  | `($a:term * $b:term) =>
    `(Value.binary .mul $(← expression rs active a) $(← expression rs active b))
  | `($a:ident[$i:term]!) | `($a:ident[$i:term]) =>
    `(Value.index $(← path rs (← resource rs active a)) $(← expression rs active i))
  | `($x:ident) =>
    if let .str name "size" := x.getId then
      return ← `(Value.size $(← path rs (← resource rs active (mkIdent name))))
    if let some i := rs.findIdx? (fun r => r.name.getId == x.getId) then
      discard <| resource rs active x
      unless isNat rs[i]! do throwErrorAt x "A scalar expression requires Nat"
      return ← `(Value.scalar $(← path rs i))
    -- Immutable configuration is elaborated as a natural-number literal in fixed code.
    return ← `(Value.literal $x)
  | _ => throwErrorAt e "Supported expressions are Nat variables, constants, array indexing, \
      array size, and +, -, *. Use a verified procedure for other computations"

/-- Symbolic substitution proposes cost bounds; generated VCs check every proposal. -/
def substitute (x : Name) (value : Term) (term : Term) : TermElabM Term := do
  return ⟨← term.raw.replaceM fun node => do
    if node.isIdent && node.getId == x then return some value.raw
    else if node.isIdent && node.getId == x.str "size" then
      return some (← `(($value).size)).raw
    else return none⟩

def sourceSite (stx : Syntax) : TermElabM Term := do
  let map ← getFileMap
  let pos := map.toPosition (stx.getPos?.getD 0)
  return quote s!"{← getFileName}:{pos.line}:{pos.column + 1}"

def operation (op : Term) (writes : Array Nat) (cost : Term) : TermElabM Fragment :=
  return ⟨← `(Program.invoke $op), ← `(Plan.invoke $op), some cost, writes, pure, some cost⟩

def assignment (rs : Array Resource) (active : Array Name) (i : Nat) (e : Term) :
    TermElabM Fragment := do
  let value ← expression rs active e
  let part ← operation (← `(Composition.assign $(← path rs i) $value)) #[i]
    (← `(Value.credits (S := $(← stateType rs)) $value + 1))
  let plan ← `(Plan.invokeAt $(← sourceSite e)
    (Composition.assign $(← path rs i) $value))
  return { part with plan, transfer := fun t => substitute rs[i]!.name.getId e t }

def guardSlots (rs : Array Resource) (q : Term) : TermElabM (Nat × Nat) := do
  let key := "_guard" ++ toString (q.raw.getPos?.getD 0)
  let some i := rs.findIdx? (fun r => r.name.getId == Name.mkSimple (key ++ "a"))
    | throwErrorAt q "Missing compiler guard slots"
  return (i, i + 1)

def condition (rs : Array Resource) (active : Array Name) (q : Term) :
    TermElabM (Fragment × Term × Term) := do
  let comparison ← match q with
    | `($a:term < $b:term) => pure (some (a, b, ← `(Relation.lt), false))
    | `($a:term ≤ $b:term) =>
      pure (some (a, b, ← `(Relation.le), false))
    | `($a:term > $b:term) => pure (some (b, a, ← `(Relation.lt), false))
    | `($a:term ≥ $b:term) => pure (some (b, a, ← `(Relation.le), false))
    | `($a:term == $b:term) | `($a:term = $b:term) =>
      pure (some (a, b, ← `(Relation.eq), false))
    | `($a:term ≠ $b:term) | `($a:term != $b:term) =>
      pure (some (a, b, ← `(Relation.eq), true))
    | _ => pure none
  if let some (a, b, op, negated) := comparison then
    let (i, j) ← guardSlots rs q
    let mut before ← seq (← assignment rs active i a) (← assignment rs active j b)
    let test ← `(Composition.compare $op $(← path rs i) $(← path rs j))
    let ea ← expression rs active a
    let eb ← expression rs active b
    let s := mkIdent (← mkFreshUserName `s)
    let fact ← `(fun $s =>
      $(← project rs i (← `($s))) = ($ea).eval $s ∧
      $(← project rs j (← `($s))) = ($eb).eval $s)
    if negated then
      let yes ← assignment rs active i (← `(0))
      let no ← assignment rs active i (← `(1))
      let flag : Fragment := ⟨← `(Program.branch $test $(yes.program) $(no.program)),
        ← `(Plan.branch $test $(yes.plan) $(no.plan)), some (← `(3)), #[i], pure, some (← `(3))⟩
      before ← seq before (← seq flag (← assignment rs active j (← `(1))))
      let fact ← `(fun ($s : $(← stateType rs)) =>
        $(← project rs i (← `($s))) =
          (if ($op).eval (($ea).eval $s) (($eb).eval $s) then 0 else 1) ∧
        $(← project rs j (← `($s))) = 1)
      return (before, ← `(Composition.compare .eq $(← path rs i) $(← path rs j)), fact)
    return (before, test, fact)
  let .str receiver field := q.raw.getId
    | throwErrorAt q "Use a scalar comparison or a certified receiver query"
  let i ← resource rs active (mkIdent receiver)
  return (← skip, ← liftQuery rs i (mkIdent (Name.mkSimple field)), ← `(fun _ => True))


end AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
