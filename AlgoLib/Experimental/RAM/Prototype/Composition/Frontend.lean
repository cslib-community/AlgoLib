/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Velvet.Syntax
import AlgoLib.Experimental.RAM.Prototype.Composition.Expressions

/-!
# One mutable frontend for owned procedures, scalars, and arrays

Every statement elaborates to Composition.Program and its indexed Plan. Ordinary
arithmetic and indexing use typed paths; receiver calls use inputs contracts.
The same method can mix these forms inside branches and annotated nested loops.
Local names are lexically checked and assigned distinct owned scalar slots.
RAM representations and expression certificates are supplied by the linker.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
open Lean Elab Command Term Meta Parser

syntax (name := receiverCall) ident noWs "(" term,* ")" : doElem
declare_syntax_cat loopCost
syntax "iterations_at_most" Term.termBeforeDo : loopCost
syntax "amortized_potential" Term.termBeforeDo : loopCost
syntax (name := paperWhile) "while " term
  ("invariant " (str)? term)* loopCost
  ("done_with " term)? ("decreasing " term)? " do " doSeq : doElem

syntax (name := pairCall) "(" ident "," ident ")" " := " term : doElem

/-- Use a library's uniform allowance when available; dependent contracts need no adapter. -/
syntax "contract% " term:max : term
elab_rules : term
  | `(contract% $proc:term) => do
    let p ← elabTerm proc none
    let type ← mkAppM ``UniformCredits #[p]
    if let some _ ← synthInstance? type then
      elabTerm (← `(Procedure.uniform $proc)) none
    else pure p

private structure Resource where
  name : Ident
  type : Term
  localSlot : Bool := false
  mutable : Bool := true
  deriving Inhabited

private structure Fragment where
  program : Term
  plan : Term
  estimate : Option Term
  writes : Array Nat := #[]
  transfer : Term → TermElabM Term := pure

private def splitAt (rs : Array Resource) : Nat :=
  let inputs := (rs.filter (! ·.localSlot)).size
  if 0 < inputs && inputs < rs.size then inputs else 1

private partial def stateType (rs : Array Resource) : TermElabM Term := do
  if rs.size == 1 then return rs[0]!.type
  let n := splitAt rs
  `($(← stateType (rs.extract 0 n)) × $(← stateType (rs.extract n rs.size)))

private partial def project (rs : Array Resource) (i : Nat) (s : Term) : TermElabM Term := do
  if rs.size == 1 then return s
  let n := splitAt rs
  if i < n then project (rs.extract 0 n) i (← `(($s).1))
  else project (rs.extract n rs.size) (i - n) (← `(($s).2))

private def bindViews (rs : Array Resource) (s : Term) (t : Term) : TermElabM Term := do
  let mut result := t
  for i in (List.range rs.size).reverse do
    result ← `(let $(rs[i]!.name) : $(rs[i]!.type) := $(← project rs i s); $result)
  return result

private def bindOld (rs : Array Resource) (s : Term) (t : Term) : TermElabM Term := do
  let mut result := t
  for i in (List.range rs.size).reverse do
    let old := mkIdent (rs[i]!.name.getId.appendAfter "Old")
    result ← `(let $old : $(rs[i]!.type) := $(← project rs i s); $result)
  return result

private def skip : TermElabM Fragment :=
  return ⟨← `(Program.identity), ← `(Plan.identity), some (← `(0)), #[], pure⟩

private def seq (p q : Fragment) : TermElabM Fragment := do
  let estimate ← match p.estimate, q.estimate with
    | some x, some y => pure (some (← `($x + $(← p.transfer y))))
    | _, _ => pure none
  return ⟨← `(Program.seq $(p.program) $(q.program)), ← `(Plan.seq $(p.plan) $(q.plan)),
    estimate, p.writes ++ q.writes, fun t => do p.transfer (← q.transfer t)⟩

/-- Focus a call on one typed component; the remaining components become automatic frames. -/
private partial def focus (rs : Array Resource) (i : Nat) (p : Fragment) : TermElabM Fragment := do
  if rs.size == 1 then return p
  let n := splitAt rs
  if i < n then
    let inner ← focus (rs.extract 0 n) i p
    let rest ← stateType (rs.extract n rs.size)
    return { inner with
      program := ← `(Program.frame $(inner.program) $rest)
      plan := ← `(Plan.frame $(inner.plan) $rest) }
  let inner ← focus (rs.extract n rs.size) (i - n) p
  let left ← stateType (rs.extract 0 n)
  let framed : Fragment := { inner with
    program := ← `(Program.frame $(inner.program) $left)
    plan := ← `(Plan.frame $(inner.plan) $left) }
  let swap : Fragment := ⟨← `(Program.swap), ← `(Plan.swap), some (← `(0)), #[], pure⟩
  seq swap (← seq framed swap)

/-- Static ownership routing; emitted regroupings compile to skip. -/
private inductive Tree where
  | leaf (index : Nat) (type : Term)
  | pair (left right : Tree)
  deriving Inhabited

private partial def tree (rs : Array Resource) (offset := 0) : Tree :=
  if rs.size == 1 then .leaf offset rs[0]!.type
  else let n := splitAt rs
       .pair (tree (rs.extract 0 n) offset) (tree (rs.extract n rs.size) (offset + n))

private partial def Tree.type : Tree → TermElabM Term
  | .leaf _ t => pure t
  | .pair a b => do `($(← a.type) × $(← b.type))

private partial def Tree.contains : Tree → Nat → Bool
  | .leaf i _, j => i == j
  | .pair a b, j => a.contains j || b.contains j

private def framed (p : Fragment) (t : Term) : TermElabM Fragment :=
  return { p with
    program := ← `(Program.frame $(p.program) $t)
    plan := ← `(Plan.frame $(p.plan) $t) }

private def swapped : TermElabM Fragment :=
  return ⟨← `(Program.swap), ← `(Plan.swap), some (← `(0)), #[], pure⟩

private def regroup (a b c : Term) (reverse := false) : TermElabM Fragment := do
  let op ← if reverse then `(unassociate $a $b $c) else `(associate $a $b $c)
  return ⟨← `(Program.invoke $op), ← `(Plan.invoke $op), some (← `(0)), #[], pure⟩

/-- Move one leaf to the front and produce its inverse route and remaining tree. -/
private partial def extract (t : Tree) (i : Nat) : TermElabM (Fragment × Fragment × Tree) := do
  match t with
  | .leaf .. => throwError "A runtime argument must use a distinct reserved slot"
  | .pair left right =>
    match left with
    | .leaf j _ => if i == j then return (← skip, ← skip, right)
    | _ => pure ()
    match right with
    | .leaf j _ => if i == j then return (← swapped, ← swapped, left)
    | _ => pure ()
    let reversed := !left.contains i
    let (selected, other) := if reversed then (right, left) else (left, right)
    let (forward, backward, rest) ← extract selected i
    let selectedType ← match selected with
      | .leaf _ t => pure t
      | _ => do
        let rec leafType : Tree → TermElabM Term
          | .leaf j t => if i == j then pure t else throwError "Invalid argument route"
          | .pair a b => if a.contains i then leafType a else leafType b
        leafType selected
    let forward ← seq (← framed forward (← other.type))
      (← regroup selectedType (← rest.type) (← other.type))
    let backward ← seq (← regroup selectedType (← rest.type) (← other.type) true)
      (← framed backward (← other.type))
    let forward ← if reversed then seq (← swapped) forward else pure forward
    let backward ← if reversed then seq backward (← swapped) else pure backward
    return (forward, backward, .pair rest other)

private def frameRight (p : Fragment) (t : Term) : TermElabM Fragment := do
  seq (← swapped) (← seq (← framed p t) (← swapped))

private def focusPair (rs : Array Resource) (i j : Nat) (p : Fragment) : TermElabM Fragment := do
  let (take, restore, rest) ← extract (tree rs) i
  match rest with
  | .leaf k _ =>
    unless k == j do throwError "Invalid runtime argument slot"
    seq take (← seq p restore)
  | _ =>
    let (takeArg, restoreArg, frame) ← extract rest j
    let a := rs[i]!.type
    let b := rs[j]!.type
    let before ← seq take (← seq (← frameRight takeArg a)
      (← regroup a b (← frame.type) true))
    let after ← seq (← regroup a b (← frame.type)) (← seq (← frameRight restoreArg a) restore)
    seq before (← seq (← framed p (← frame.type)) after)

private partial def mentions (rs : Array Resource) (s : Syntax) : Bool :=
  (s.isIdent && rs.any (fun r => r.name.getId.isPrefixOf s.getId)) ||
    s.getArgs.any (mentions rs)

private partial def liftQuery (rs : Array Resource) (i : Nat) (q : Term) : TermElabM Term := do
  if rs.size == 1 then return q
  let n := splitAt rs
  if i < n then `(testLeft $(← liftQuery (rs.extract 0 n) i q))
  else `(testRight $(← liftQuery (rs.extract n rs.size) (i - n) q))

private partial def checkStatic (rs : Array Resource) (term : Syntax) : TermElabM Unit := do
  if term.isIdent then
    for r in rs do
      let n := term.getId
      if r.name.getId.isPrefixOf n || (r.name.getId.appendAfter "Old").isPrefixOf n then
        throwErrorAt term
          "Procedure arguments describe fixed code. Runtime input '{r.name}' must pass through a \
        certified typed operation"
  for child in term.getArgs do checkStatic rs child

private def items (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Parser.Term.doSeqBracketed then stx[1].getArgs.map (·[0])
  else if stx.getKind == ``Parser.Term.doSeqIndent then stx[0].getArgs.map (·[0])
  else #[]

private def receiverApplication (e : Term) : TermElabM (Ident × Array Term) := do
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

private partial def path (rs : Array Resource) (i : Nat) : TermElabM Term := do
  if rs.size == 1 then return ← `(Path.here)
  let n := splitAt rs
  if i < n then `(Path.left $(← path (rs.extract 0 n) i))
  else `(Path.right $(← path (rs.extract n rs.size) (i - n)))

private def resource (rs : Array Resource) (active : Array Name) (x : Ident) : TermElabM Nat := do
  let some i := rs.findIdx? (fun r => r.name.getId == x.getId)
    | throwErrorAt x "Unknown mutable variable '{x}'"
  unless active.contains x.getId do throwErrorAt x "Local '{x}' is not in scope"
  return i

private def isNat (r : Resource) : Bool :=
  r.type.raw.isIdent && r.type.raw.getId.eraseMacroScopes == `Nat

private partial def expression (rs : Array Resource) (active : Array Name) (e : Term) :
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
private def substitute (x : Name) (value : Term) (term : Term) : TermElabM Term := do
  return ⟨← term.raw.replaceM fun node => do
    if node.isIdent && node.getId == x then return some value.raw
    else if node.isIdent && node.getId == x.str "size" then
      return some (← `(($value).size)).raw
    else return none⟩

private def sourceSite (stx : Syntax) : TermElabM Term := do
  let map ← getFileMap
  let pos := map.toPosition (stx.getPos?.getD 0)
  return quote s!"{← getFileName}:{pos.line}:{pos.column + 1}"

private def operation (op : Term) (writes : Array Nat) (cost : Term) : TermElabM Fragment :=
  return ⟨← `(Program.invoke $op), ← `(Plan.invoke $op), some cost, writes, pure⟩

private def assignment (rs : Array Resource) (active : Array Name) (i : Nat) (e : Term) :
    TermElabM Fragment := do
  let value ← expression rs active e
  let part ← operation (← `(Composition.assign $(← path rs i) $value)) #[i]
    (← `(Value.credits (S := $(← stateType rs)) $value + 1))
  let plan ← `(Plan.invokeAt $(← sourceSite e)
    (Composition.assign $(← path rs i) $value))
  return { part with plan, transfer := fun t => substitute rs[i]!.name.getId e t }

private def guardSlots (rs : Array Resource) (q : Term) : TermElabM (Nat × Nat) := do
  let key := "_guard" ++ toString (q.raw.getPos?.getD 0)
  let some i := rs.findIdx? (fun r => r.name.getId == Name.mkSimple (key ++ "a"))
    | throwErrorAt q "Missing compiler guard slots"
  return (i, i + 1)

private def condition (rs : Array Resource) (active : Array Name) (q : Term) :
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
        ← `(Plan.branch $test $(yes.plan) $(no.plan)), some (← `(3)), #[i], pure⟩
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

private partial def statements (rs : Array Resource) (body : TSyntax ``Parser.Term.doSeq)
    (inferBudget : Bool) (active : Array Name) (nested := false) : TermElabM Fragment := do
  let mut active := active
  let mut result ← skip
  let all := items body.raw
  for i in [:all.size] do
    let stx : TSyntax `doElem := ⟨all[i]!⟩
    if stx.raw.getKind == ``Parser.Term.doReturn && (nested || i + 1 < all.size) then
      throwErrorAt stx "Return is supported only at method exit"
    let (part, next) ← statement active stx
    let part ← do
      let site ← sourceSite stx
      -- Only the current primitive is labelled; its continuation keeps its own source.
      let plan ← match part.plan with
        | `(Plan.invoke $op) => `(Plan.invokeAt $site $op)
        | _ => pure part.plan
      pure { part with plan }
    result ← seq result part
    active := next
  return result
where
  call (active : Array Name) (target : Ident) (proc : Term) : TermElabM Fragment := do
    let i ← resource rs active target
    checkStatic rs proc.raw
    let proc ← if inferBudget then `(contract% ($proc)) else pure proc
    let amount ← `(($proc).credits $(rs[i]!.name))
    focus rs i ⟨← `(Program.call ($proc).body),
      ← `(Plan.callAt $(← sourceSite target) $proc), some amount, #[i], pure⟩
  receiver (active : Array Name) (f : Ident) (args : Array Term) : TermElabM Fragment := do
    let .str target field := f.getId
      | throwErrorAt f "Use a receiver such as buffer.append(...)"
    unless args.any (fun a => mentions rs a.raw) do
      return ← call active (mkIdent target) (← `($(mkIdent (Name.mkSimple field)) $args*))
    if args.isEmpty then throwErrorAt f "Missing runtime argument"
    for arg in args.pop do checkStatic rs arg
    let i ← resource rs active (mkIdent target)
    let key := Name.mkSimple ("_argument" ++ toString (f.raw.getPos?.getD 0))
    let some j := rs.findIdx? (fun r => r.name.getId == key)
      | throwErrorAt f "Missing runtime argument slot"
    let prepare ← assignment rs active j args.back!
    let config := args.pop
    let proc ← `($(mkIdent (Name.mkSimple (field ++ "From"))) $config*)
    let proc ← if inferBudget then `(contract% ($proc)) else pure proc
    let amount ← `(($proc).credits ($(rs[i]!.name), $(rs[j]!.name)))
    let part : Fragment := ⟨← `(Program.call ($proc).body),
      ← `(Plan.callAt $(← sourceSite f) $proc),
      some amount, #[i,j], pure⟩
    seq prepare (← focusPair rs i j part)
  declare (active : Array Name) (x : Ident) (e : Term) :
      TermElabM (Fragment × Array Name) := do
    let some i := rs.findIdx? (fun r => r.name.getId == x.getId)
      | throwErrorAt x "Missing local slot"
    return (← assignment rs active i e, active.push x.getId)
  loop (active : Array Name) (q : Term) (label : Array (Option (TSyntax `str)))
      (inv : Array Term) (cost done measure : Option Term)
      (body : TSyntax ``Parser.Term.doSeq) : TermElabM Fragment := do
    let (before, test, guardFact) ← condition rs active q
    let mut body ← statements rs body inferBudget active true
    let s := mkIdent (← mkFreshUserName `state)
    let entry := mkIdent (← mkFreshUserName `entry)
    let remaining := mkIdent `remaining
    if let some measure := measure then
      let predicate ← `(fun ($s : $(← stateType rs)) => $(← bindViews rs (← `($s)) measure))
      let program ← `(Program.seq $(body.program) Program.identity)
      let plan ← `(Plan.atEntry (fun $entry => Plan.seq $(body.plan)
        (Plan.assert (fun $s => $predicate $s < $predicate $entry))))
      body := {body with program, plan}
    body ← seq body before
    let site ← sourceSite q
    let mut estimated : Option Term := none
    let mut unit : Option Term := none
    if let some bound := cost then
      let some bodyCost := body.estimate
        | throwErrorAt bound "Annotate every nested loop with iterations_at_most \
          or amortized_potential"
      -- For an increasing index, use the upper endpoint in the dependent body cost.
      -- This is a candidate envelope, not an axiom: preservation VCs must prove it pays.
      let envelope ← match bound with
        | `($upper:term - $index:ident) => substitute index.getId upper bodyCost
        | _ => pure bodyCost
      unit := some envelope
      estimated := some (← `($bound * ($envelope + 1) + 1))
    let mut invTerm ← `(True)
    for k in (List.range inv.size).reverse do
      let fact := inv[k]!
      if cost.isSome then
        let title := label[k]!.map (·.getString) |>.getD "loop invariant"
        let name ← `( $(quote (title ++ " initialized / preserved at ")) ++ $site )
        invTerm ← `(Obligation $name $fact ∧ $invTerm)
      else invTerm ← `($fact ∧ $invTerm)
    invTerm ← bindViews rs (← `($s)) invTerm
    invTerm ← `($guardFact $s ∧ $invTerm)
    for i in [:rs.size] do
      if active.contains rs[i]!.name.getId && !body.writes.contains i then
        invTerm ← `($(← project rs i (← `($s))) = $(← project rs i (← `($entry))) ∧ $invTerm)
    let loopInv ← `(fun ($s : $(← stateType rs)) ($remaining : Nat) => $invTerm)
    let loop : Fragment := ⟨← `(Program.loop $test $(body.program)),
      ← `(Plan.atEntry (fun ($entry : $(← stateType rs)) =>
        Plan.loop $test $loopInv $(body.plan))), none, body.writes, pure⟩
    let loop ← if let some bound := cost then do
      let frozen ← bindViews rs (← `($entry)) unit.get!
      let measure ← `(fun ($s : $(← stateType rs)) => $(← bindViews rs (← `($s)) bound))
      let invariantFn ← `(fun ($s : $(← stateType rs)) => $invTerm)
      pure { loop with
        plan := ← `(Plan.atEntry (fun ($entry : $(← stateType rs)) =>
          Plan.countedLoop $site $test $invariantFn $measure $frozen $(body.plan)))
        estimate := estimated }
      else pure loop
    let mut part ← seq before loop
    if let some done := done then
      let fact ← `(fun ($s : $(← stateType rs)) => $(← bindViews rs (← `($s)) done))
      part ← seq part ⟨← `(Program.identity), ← `(Plan.assert $fact), some (← `(0)), #[], pure⟩
    return part
  statement (active : Array Name) (stx : TSyntax `doElem) :
      TermElabM (Fragment × Array Name) := withRef stx do
    match stx with
    | `(doElem| let mut $x:ident := $e:term)
    | `(doElem| let mut $x:ident : Nat := $e:term)
    | `(doElem| let $x:ident := $e:term)
    | `(doElem| let $x:ident : Nat := $e:term) => declare active x e
    | `(doElem| ($left:ident, $right:ident) := $proc:term) =>
      let i ← resource rs active left
      let j ← resource rs active right
      if i == j then throwErrorAt stx "A procedure cannot receive the same owned resource twice"
      unless rs[i]!.mutable && rs[j]!.mutable do
        throwErrorAt stx "Procedure outputs require mutable resources"
      checkStatic rs proc
      let proc ← if inferBudget then `(contract% ($proc)) else pure proc
      let amount ← `(($proc).credits ($(rs[i]!.name), $(rs[j]!.name)))
      let part : Fragment := ⟨← `(Program.call ($proc).body),
        ← `(Plan.callAt $(← sourceSite stx) $proc),
        some amount, #[i,j], pure⟩
      return (← focusPair rs i j part, active)
    | `(doElem| $target:ident := $value:term) =>
      let i ← resource rs active target
      unless rs[i]!.mutable do throwErrorAt target "Immutable local; use 'let mut'"
      let part ← if isNat rs[i]! then assignment rs active i value else call active target value
      return (part, active)
    | `(doElem| $a:ident[$i:term] := $e:term) =>
      let slot ← resource rs active a
      let index ← expression rs active i
      let value ← expression rs active e
      let part ← operation (← `(Composition.write $(← path rs slot) $index $value)) #[slot]
        (← `(Value.credits (S := $(← stateType rs)) $index +
          Value.credits (S := $(← stateType rs)) $value + 3))
      let updated ← `(($a).set! $i $e)
      return ({ part with transfer := fun t => substitute a.getId updated t }, active)
    | `(doElem| $f:ident($args:term,*)) =>
      return (← receiver active f args, active)
    | `(doElem| if $q:term then $yes:doSeq else $no:doSeq) =>
      let (before, test, _) ← condition rs active q
      let yes ← statements rs yes inferBudget active true
      let no ← statements rs no inferBudget active true
      let estimate ← match yes.estimate, no.estimate with
        | some x, some y => pure (some (← `(1 + max $x $y)))
        | _, _ => pure none
      let part : Fragment := ⟨← `(Program.branch $test $(yes.program) $(no.program)),
        ← `(Plan.branch $test $(yes.plan) $(no.plan)), estimate, yes.writes ++ no.writes,
        fun t => do `(max $(← yes.transfer t) $(← no.transfer t))⟩
      return (← seq before part, active)
    | `(doElem| if $q:term then $yes:doSeq) =>
      statement active (← `(doElem| if $q then $yes else pure ()))
    | `(doElem| while $q:term
        $[invariant $[$label:str]? $inv:term]*
        $cost:loopCost $[done_with $done]? $[decreasing $measure]? do $body:doSeq) =>
      return (← loop active q label inv (some ⟨cost.raw[1]⟩) done measure body, active)
    | `(doElem| while $q:term
        $[invariant $[$label:str]? $inv:term
        ]* $[done_with $done]? $[decreasing $measure]? do $body:doSeq) =>
      return (← loop active q label inv none done measure body, active)
    | `(doElem| assert $fact:term) =>
      let s := mkIdent (← mkFreshUserName `state)
      let predicate ← `(fun ($s : $(← stateType rs)) => $(← bindViews rs (← `($s)) fact))
      return (⟨← `(Program.identity), ← `(Plan.assert $predicate),
        some (← `(0)), #[], pure⟩, active)
    | `(doElem| return) | `(doElem| return ()) | `(doElem| pure ()) => return (← skip, active)
    | `(doElem| $e:term) =>
      let (head, args) ← receiverApplication e
      return (← receiver active head args, active)
    | _ => throwErrorAt stx "Use scalar assignment, indexed array update, a verified call, \
        conditional, annotated loop, or assertion"

/-- Reserve local and guard registers before elaborating paths. Names are lexical;
slots are private method scratch and never specialize executable code. -/
private partial def collect (rs : Array Resource) (body : Syntax) : TermElabM (Array Resource) := do
  let mut rs := rs
  for raw in items body do
    let stx : TSyntax `doElem := ⟨raw⟩
    match stx with
    | `(doElem| let mut $x:ident := $_:term)
    | `(doElem| let mut $x:ident : Nat := $_:term) =>
      rs := rs.push ⟨x, ← `(Nat), true, true⟩
    | `(doElem| let $x:ident := $_:term)
    | `(doElem| let $x:ident : Nat := $_:term) =>
      rs := rs.push ⟨x, ← `(Nat), true, false⟩
    | `(doElem| if $q:term then $yes:doSeq else $no:doSeq) =>
      rs ← guards rs q
      rs ← collect (← collect rs yes) no
    | `(doElem| if $q:term then $yes:doSeq) =>
      rs ← collect (← guards rs q) yes
    | `(doElem| while $q:term
        $[invariant $[$_:str]? $_:term]* $_:loopCost
        $[done_with $_]? $[decreasing $_]? do $body:doSeq)
    | `(doElem| while $q:term
        $[invariant $[$_:str]? $_:term
        ]* $[done_with $_]? $[decreasing $_]? do $body:doSeq) =>
      rs ← collect (← guards rs q) body
    | _ => pure ()
  return rs
where
  guards (rs : Array Resource) (q : Term) : TermElabM (Array Resource) := do
    if q.raw.isIdent then return rs
    let key := "_guard" ++ toString (q.raw.getPos?.getD 0)
    return rs ++ #[⟨mkIdent (Name.mkSimple (key ++ "a")), ← `(Nat), true, true⟩,
      ⟨mkIdent (Name.mkSimple (key ++ "b")), ← `(Nat), true, true⟩]

private partial def collectArguments (known rs : Array Resource) (body : Syntax) :
    TermElabM (Array Resource) := do
  let mut rs := rs
  for raw in items body do
    let stx : TSyntax `doElem := ⟨raw⟩
    match stx with
    | `(doElem| $f:ident($args:term,*)) =>
      if args.getElems.any (fun a => mentions known a.raw) then
        let key := "_argument" ++ toString (f.raw.getPos?.getD 0)
        rs := rs.push ⟨mkIdent (Name.mkSimple key), ← `(Nat), true, true⟩
    | `(doElem| if $_:term then $yes:doSeq else $no:doSeq) =>
      rs ← collectArguments known (← collectArguments known rs yes) no
    | `(doElem| if $_:term then $yes:doSeq) => rs ← collectArguments known rs yes
    | `(doElem| while $_:term
        $[invariant $[$_:str]? $_:term]* $_:loopCost
        $[done_with $_]? $[decreasing $_]? do $body:doSeq)
    | `(doElem| while $_:term
        $[invariant $[$_:str]? $_:term
        ]* $[done_with $_]? $[decreasing $_]? do $body:doSeq) =>
      rs ← collectArguments known rs body
    | `(doElem| $e:term) =>
      let (f, args) ← receiverApplication e
      if args.any (fun a => mentions known a.raw) then
        let key := "_argument" ++ toString (f.raw.getPos?.getD 0)
        rs := rs.push ⟨mkIdent (Name.mkSimple key), ← `(Nat), true, true⟩
    | _ => pure ()
  return rs

/-- Existing `ram method` dispatches resource parameters here. Immutable parameters
specialize the method before execution and must not be confused with RAM inputs. -/
def declareMethod (name : Ident) (binders : Array (TSyntax `leafny_binder))
    (ret : Ident) (retTy : Term) (pre post : Array Term) (credits : Option Term)
    (body : TSyntax ``Parser.Term.doSeq) : CommandElabM Unit := do
  let mut rs : Array Resource := #[]
  let mut params : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
  let mut args : Array Term := #[]
  for b in binders do
    match b with
    | `(leafny_binder| (mut $x:ident : $ty:term)) => rs := rs.push ⟨x, ty, false, true⟩
    | `(leafny_binder| ($x:ident : $ty:term)) =>
      params := params.push (← `(bracketedBinder| ($x : $ty)))
      args := args.push (← `($x))
    | _ => throwErrorAt b "Use typed mutable resources and explicit immutable configuration \
        parameters"
  if rs.isEmpty then throwErrorAt name "Declare at least one mutable resource"
  let inputs := rs
  rs ← Command.runTermElabM fun _ => do
    let rs ← collect rs body
    collectArguments rs rs body
  let names := rs.map (·.name.getId)
  unless names.toList.Nodup do throwErrorAt name "Mutable resource names must be distinct"
  for r in rs do
    if r.name.getId == ret.getId || ret.getId == `remaining ||
        ret.getId == r.name.getId.appendAfter "Old" || r.name.getId == `remaining ||
        names.contains (r.name.getId.appendAfter "Old") then
      throwErrorAt r.name "Reserve distinct output, Old, and remaining-credit names"
  let input := mkIdent (← liftCoreM <| mkFreshUserName `input)
  let output := mkIdent (← liftCoreM <| mkFreshUserName `output)
  let (fragment, state, pre, post, budget, uniformBudget) ← Command.runTermElabM fun _ => do
    let mut fragment ← statements rs body credits.isNone (inputs.map (·.name.getId))
    let mut p ← `(True)
    for fact in pre.reverse do p ← `($fact ∧ $p)
    let mut q ← `(True)
    for fact in post.reverse do q ← `($fact ∧ $q)
    let state ← stateType inputs
    let result ← if retTy.raw.isIdent && retTy.raw.getId == `Unit then `(()) else do
      let mut values : Array Term := #[]
      for i in [:inputs.size] do values := values.push (← project inputs i (← `($output)))
      let mut value := values.back!
      for v in values.toList.dropLast.reverse do value ← `(($v, $value))
      pure value
    q ← `(let $ret : $retTy := $result; $q)
    p ← bindOld inputs (← `($input)) (← bindViews inputs (← `($input)) p)
    q ← bindOld inputs (← `($input)) (← bindViews inputs (← `($output)) q)
    if rs.size > inputs.size then
      let scratch ← stateType (rs.extract inputs.size rs.size)
      let enter ← operation (← `(enterLocals $state $scratch)) #[]
        (← `(Locals.credits (L := $scratch)))
      let initializeCost := fun t => do
        let mut result := t
        for r in rs.extract inputs.size rs.size do
          result ← substitute r.name.getId (⟨Syntax.mkNumLit "0"⟩) result
        return result
      let enter : Fragment := { enter with transfer := initializeCost }
      let leave ← operation (← `(leaveLocals $state $scratch)) #[] (← `(0))
      fragment ← seq enter (← seq fragment leave)
    let budget ← match credits, fragment.estimate with
      | some c, _ => bindViews inputs (← `($input)) c
      | none, some c => bindViews inputs (← `($input)) c
      | none, none => throwErrorAt body "Loops need a logical credits clause and a resource \
        invariant; RAM time is inferred"
    let plan ← bindOld inputs (← `($input)) fragment.plan
    return ({ fragment with plan }, state, p, q, budget, fragment.estimate.getD budget)
  if rs.size > inputs.size then
    let scratchType ← Command.runTermElabM fun _ => stateType (rs.extract inputs.size rs.size)
    let scratchName := mkIdent (name.getId.appendAfter "Locals")
    elabCommand (← `(command| abbrev $scratchName : Type := $scratchType))
  let obligations := mkIdent (name.getId.appendAfter "Obligations")
  let certificate := mkIdent (name.getId.appendAfter "Certificate")
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    @[reducible] def $name $params* : Algorithm $state $state where
      body := $(fragment.program)
      annotations := fun $input => $(fragment.plan)
      «requires» := fun $input => $pre
      «ensures» := fun $input $output => $post
      «credits» := fun $input => $budget))
  let obligationType ← if params.isEmpty then `(($name).Obligations)
    else `(∀ $params*, ($name $args*).Obligations)
  elabCommand (← `(command| def $obligations : Prop := $obligationType))
  elabCommand (← `(command|
    @[reducible] def $certificate (proof : $obligations) $params* : Procedure $state $state :=
      ($name $args*).certify (proof $args*)))
  if credits.isNone && !(← Command.runTermElabM fun _ => do
      let fragment ← statements rs body true (inputs.map (·.name.getId))
      return fragment.estimate.any (fun c => mentions inputs c)) then
    let uniform := mkIdent (name.getId.appendAfter "UniformCredits")
    elabCommand (← `(command|
      instance $uniform:ident (proof : $obligations) $params* :
          UniformCredits ($certificate proof $args*) where
        amount := $uniformBudget
        bound _ := Nat.le_refl _))

end AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
