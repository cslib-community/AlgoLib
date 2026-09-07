/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/
import Init


/-!
# Source identities and mathematical context metadata

Named propositions and typed source shapes describe obligations before simplification.
These wrappers carry no executable meaning or RAM representation. The kernel checks
the wrapped propositions; metadata supports navigation, not trusted evidence.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace AlgoLib.Experimental.RAM.Prototype.Composition

/-- A transparent proposition carrying the source-level name of an obligation.
The kernel checks `fact`; diagnostics retain `label` until the user opens the goal. -/
def Obligation (_label : String) (fact : Prop) : Prop := fact

/-- Keep location metadata separate: constructing proof obligations does not compute strings. -/
def ObligationAt (_label _site : String) (fact : Prop) : Prop := fact

/-- A stable invariant name, independent of its initialization/preservation phase. -/
def InvariantFact (_name : String) (fact : Prop) : Prop := fact

/-- A quantified source role. Value types remain ordinary Lean types. -/
def SourceForall (_role : String) (body : A → Prop) : Prop := ∀ a, body a

@[simp] theorem sourceForall_eq (role : String) (body : A → Prop) :
    SourceForall role body = (∀ a, body a) := rfl

/-- The frontend records exact product paths, preserving product-valued resources as leaves. -/
inductive SourceShape where
  | leaf (binding : Nat) (name : String) (internal : Bool)
  | pair (left right : SourceShape)
  deriving Inhabited


end AlgoLib.Experimental.RAM.Prototype.Composition
