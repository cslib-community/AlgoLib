/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import AlgoLib.Experimental.RAM.Prototype.Composition.Frontend.Syntax

/-!
# Elaboration state and ownership routing

Internal resource trees, mathematical state projections, fragment composition, and reversible
ownership routes. These helpers are implementation APIs, not algorithm-author interfaces.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
open Lean Elab Command Term Meta Parser

structure Resource where
  name : Ident
  type : Term
  localSlot : Bool := false
  mutable : Bool := true
  deriving Inhabited

structure Fragment where
  program : Term
  plan : Term
  estimate : Option Term
  writes : Array Nat := #[]
  transfer : Term → TermElabM Term := pure
  work : Option Term

def splitAt (rs : Array Resource) : Nat :=
  let inputs := (rs.filter (! ·.localSlot)).size
  if 0 < inputs && inputs < rs.size then inputs else 1

partial def stateType (rs : Array Resource) : TermElabM Term := do
  if rs.size == 1 then return rs[0]!.type
  let n := splitAt rs
  `($(← stateType (rs.extract 0 n)) × $(← stateType (rs.extract n rs.size)))

partial def project (rs : Array Resource) (i : Nat) (s : Term) : TermElabM Term := do
  if rs.size == 1 then return s
  let n := splitAt rs
  if i < n then project (rs.extract 0 n) i (← `(($s).1))
  else project (rs.extract n rs.size) (i - n) (← `(($s).2))

def bindViews (rs : Array Resource) (s : Term) (t : Term) : TermElabM Term := do
  let mut result := t
  for i in (List.range rs.size).reverse do
    result ← `(let $(rs[i]!.name) : $(rs[i]!.type) := $(← project rs i s); $result)
  return result

def bindOld (rs : Array Resource) (s : Term) (t : Term) : TermElabM Term := do
  let mut result := t
  for i in (List.range rs.size).reverse do
    let old := mkIdent (rs[i]!.name.getId.appendAfter "Old")
    result ← `(let $old : $(rs[i]!.type) := $(← project rs i s); $result)
  return result

def skip : TermElabM Fragment :=
  return ⟨← `(Program.identity), ← `(Plan.identity), some (← `(0)), #[], pure, some (← `(0))⟩

def seq (p q : Fragment) : TermElabM Fragment := do
  let estimate ← match p.estimate, q.estimate with
    | some x, some y => pure (some (← `($x + $(← p.transfer y))))
    | _, _ => pure none
  let work ← match p.work, q.work with
    | some x, some y => pure (some (← `($x + $(← p.transfer y))))
    | _, _ => pure none
  return ⟨← `(Program.seq $(p.program) $(q.program)), ← `(Plan.seq $(p.plan) $(q.plan)),
    estimate, p.writes ++ q.writes, (fun t => do p.transfer (← q.transfer t)), work⟩

/-- Focus a call on one typed component; the remaining components become automatic frames. -/
partial def focus (rs : Array Resource) (i : Nat) (p : Fragment) : TermElabM Fragment := do
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
  let swap : Fragment :=
    ⟨← `(Program.swap), ← `(Plan.swap), some (← `(0)), #[], pure, some (← `(0))⟩
  seq swap (← seq framed swap)

/-- Static ownership routing; emitted regroupings compile to skip. -/
inductive Tree where
  | leaf (index : Nat) (type : Term)
  | pair (left right : Tree)
  deriving Inhabited

partial def tree (rs : Array Resource) (offset := 0) : Tree :=
  if rs.size == 1 then .leaf offset rs[0]!.type
  else let n := splitAt rs
       .pair (tree (rs.extract 0 n) offset) (tree (rs.extract n rs.size) (offset + n))

partial def Tree.type : Tree → TermElabM Term
  | .leaf _ t => pure t
  | .pair a b => do `($(← a.type) × $(← b.type))

partial def Tree.contains : Tree → Nat → Bool
  | .leaf i _, j => i == j
  | .pair a b, j => a.contains j || b.contains j

def framed (p : Fragment) (t : Term) : TermElabM Fragment :=
  return { p with
    program := ← `(Program.frame $(p.program) $t)
    plan := ← `(Plan.frame $(p.plan) $t) }

def swapped : TermElabM Fragment :=
  return ⟨← `(Program.swap), ← `(Plan.swap), some (← `(0)), #[], pure, some (← `(0))⟩

def regroup (a b c : Term) (reverse := false) : TermElabM Fragment := do
  let op ← if reverse then `(unassociate $a $b $c) else `(associate $a $b $c)
  return ⟨← `(Program.invoke $op), ← `(Plan.invoke $op), some (← `(0)), #[], pure, some (← `(0))⟩

/-- Move one leaf to the front and produce its inverse route and remaining tree. -/
partial def extract (t : Tree) (i : Nat) : TermElabM (Fragment × Fragment × Tree) := do
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

def frameRight (p : Fragment) (t : Term) : TermElabM Fragment := do
  seq (← swapped) (← seq (← framed p t) (← swapped))

def focusPair (rs : Array Resource) (i j : Nat) (p : Fragment) : TermElabM Fragment := do
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


end AlgoLib.Experimental.RAM.Prototype.Composition.Frontend
