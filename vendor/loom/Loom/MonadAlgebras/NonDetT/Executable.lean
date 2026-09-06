/-
AlgoLib extension to the upstream Loom framework, Apache-2.0.
Lean 4.30 retains a generic CCPO dictionary in compiled recursive calls. Its
supremum operation is noncomputable. Specializing the loop to DivM removes that
runtime dictionary, while `runDivM_eq` proves equality with upstream extraction.
No unchecked executable override or additional axiom is introduced.
-/
import Loom.MonadAlgebras.NonDetT.Extract

universe u

/-- Executable specialization of Loom's loop to its concrete divergence monad. -/
def DivM.iterate {β : Type u} (f : Unit → β → DivM (ForInStep β)) (b : β) : DivM β := do
  match ← f () b with
  | .done b => pure b
  | .yield b => iterate f b
partial_fixpoint

/-- Specialization changes no logical execution. -/
theorem DivM.iterate_eq {β : Type u} (f : Unit → β → DivM (ForInStep β)) (b : β) :
    DivM.iterate f b = Loop.forIn.loop f b := by
  delta DivM.iterate Loop.forIn.loop
  rfl

/-- Fuel-free executable extraction for Velvet's concrete NonDetT DivM methods. -/
def NonDetT.runDivM {α : Type u} : NonDetT DivM α → DivM α
  | .pure x => .res x
  | .vis x f => x >>= fun a => (f a).runDivM
  | @NonDetT.pickCont _ _ _ p _ f =>
    match Findable.find (p := p) () with
    | none => .div
    | some x => (f x).runDivM
  | .repeatCont init f cont =>
    DivM.iterate (fun _ x => (f x).runDivM) init >>= fun x => (cont x).runDivM

/-- Kernel-checked equality with upstream Loom's independently specified extractor. -/
theorem NonDetT.runDivM_eq {α : Type u} (p : NonDetT DivM α) : p.runDivM = p.run := by
  induction p with
  | pure x => rfl
  | vis x f ih =>
    simp only [runDivM, run]
    cases x <;> simp_all [bind, pure]
  | pickCont ty predicate f ih =>
    simp only [runDivM, run]
    split <;> simp_all [CCPOBot.compBot]
  | repeatCont init f cont ihf ihc =>
    simp only [runDivM, run, DivM.iterate_eq]
    simp only [ihf, ihc]
    rfl
