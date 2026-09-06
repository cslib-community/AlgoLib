module
/- AlgoLib port: Lean 4.30 transformer and CCPO compatibility. -/
import all Init.Prelude
import all Init.Internal.Order.Basic
import all Init.Control.State
import all Init.Control.Reader
import all Init.Control.Except
public import Loom.MonadAlgebras.Defs
public import Loom.MonadAlgebras.Instances.Basic

@[expose] public section


abbrev Except.getD {ε α} (default : ε -> α)  : Except ε α -> α
  | Except.ok p => p
  | Except.error e => default e

abbrev Except.bind' {m : Type u -> Type v} {ε α β} [Monad m] : Except ε α -> (α -> ExceptT ε m β) -> ExceptT ε m β :=
  fun x f => bind (m := ExceptT ε m) (pure (f := m) x) f

lemma Except.bind'_bind {m : Type u -> Type v} {ε α β} [Monad m] [LawfulMonad m] (i : m (Except ε α)) (f : α -> ExceptT ε m β) :
  (i >>= fun a => Except.bind' a f) = bind (m := ExceptT ε m) i f := by
  simp [Except.bind', bind, ExceptT.bind]; rfl

/- Ordered Monad Algebra instance for ExceptT -/
@[reducible] noncomputable def MAlgExcept (ε : Type u) (df : ε -> Prop) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] : MAlgOrdered (ExceptT ε m) l where
  μ := fun e => inst.μ $ Except.getD (⌜df ·⌝) <$> e
  μ_ord_pure := by
    intro l; simp [pure, ExceptT.pure, ExceptT.mk]
    solve_by_elim [MAlgOrdered.μ_ord_pure]
  μ_ord_bind := by
    intros α f g
    try simp [Function.comp, Pi.hasLe]
    intros le x
    have leM := @inst.μ_ord_bind (Except ε α)
      (fun x => Except.getD (⌜df ·⌝) <$> Except.bind' x f)
      (fun x => Except.getD (⌜df ·⌝) <$> Except.bind' x g)
    simp only [Function.comp, Pi.hasLe, <-map_bind, Except.bind'_bind] at leM
    apply leM
    intro value
    cases value with
    | error e =>
      simp [Function.comp, Except.bind', Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk]
    | ok a =>
      simpa [Function.comp, Except.bind', Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk] using le a

section ExeceptHandler

variable (ε : Type u) (l : Type u) (m : Type u -> Type v) [Monad m] [LawfulMonad m]

class IsHandler {ε : Type*} (handler : outParam (ε -> Prop)) where

set_option linter.unusedVariables false in
noncomputable
instance OfHd {hd : ε -> Prop} [hdInst : IsHandler hd]
  [CompleteLattice l] [inst: MAlgOrdered m l] : MAlgOrdered (ExceptT ε m) l := MAlgExcept ε hd l m


/-- Extend a postcondition to exceptions using the selected logical handler. -/
noncomputable def Except.post {ε α l : Type u} [CompleteLattice l]
    (hd : ε → Prop) (post : α → l) : Except ε α → l
  | .ok a => post a
  | .error e => ⌜hd e⌝

lemma MAlg.lift_ExceptT ε (hd : ε -> Prop) [IsHandler hd] [CompleteLattice l] [inst: MAlgOrdered m l]
   (c : ExceptT ε m α) post :
  MAlg.lift c post = MAlg.lift (m := m) c (Except.post hd post) := by
    simp [MAlg.lift, MAlgOrdered.μ, OfHd, MAlgExcept, Functor.map, ExceptT.map, ExceptT.mk]
    rw [map_eq_pure_bind]
    apply MAlgOrdered.bind
    ext a
    cases a <;> simp [Except.getD, Except.post]

instance MAlgExceptHdDet (hd : ε -> Prop)
  [CompleteLattice l] [inst: MAlgOrdered m l] [IsHandler hd]
  [inst': MAlgDet m l] : MAlgDet (ExceptT ε m) l where
  angelic := by
    intro α ι c p hi
    simp only [MAlg.lift_ExceptT]
    have h := inst'.angelic (α := Except ε α) (c := c) (p := fun i => Except.post hd (p i))
    have eq : (fun e : Except ε α => ⨆ i : ι, Except.post hd (p i) e) =
        Except.post hd (fun a => ⨆ i, p i a) := by
      funext e; cases e <;> simp only [Except.post, iSup_const]
    rw [eq] at h
    exact h
  demonic := by
    intro α ι c p hi
    simp only [MAlg.lift_ExceptT]
    have h := inst'.demonic (α := Except ε α) (c := c) (p := fun i => Except.post hd (p i))
    have eq : (fun e : Except ε α => ⨅ i : ι, Except.post hd (p i) e) =
        Except.post hd (fun a => ⨅ i, p i a) := by
      funext e; cases e <;> simp only [Except.post, iInf_const]
    rw [eq] at h
    exact h

instance
  [CompleteLattice l] [inst: MAlgOrdered m l] [IsHandler (fun (_ : ε) => True)]
  [inst': NoFailure m] : NoFailure (ExceptT ε m) where
  noFailure := by
    rintro _ c
    rw (occs := [2]) [<-inst'.noFailure (c := c)]
    simp [MAlg.lift, MAlgOrdered.μ, Functor.map, LE.pure, ExceptT.map, ExceptT.mk, OfHd, MAlgExcept]
    rw [map_eq_pure_bind]; apply MAlgOrdered.bind; ext (_|_) <;> simp

/- Monad Transformer Algebra instance for ExceptT -/
noncomputable
instance [_root_.CompleteLattice l]
  [IsHandler (ε := ε) hd]
  [inst: MAlgOrdered m l] :
  MAlgLift m l (ExceptT ε m) l where
    cl := by exact LogicLift.refl
    μ_lift := by
      intros; simp [MAlg.lift_ExceptT];
      simp [liftM, MonadLiftT.monadLift, instMonadLiftTOfMonadLift, MonadLift.monadLift]
      simp [ExceptT.lift, ExceptT.mk, MAlg.lift, Except.post]

end ExeceptHandler

namespace ExceptionAsSuccess
scoped instance PartialHandler {ε} : IsHandler (ε := ε) fun _ => True where
end ExceptionAsSuccess

namespace ExceptionAsFailure
scoped instance TotalHandler {ε} : IsHandler (ε := ε) fun _ => False where
end ExceptionAsFailure

open Lean.Order

instance [Monad m] [CCPOBot m] : CCPOBot (ExceptT ε m) where
  compBot := CCPOBot.compBot (m := m)

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] : CCPOBotLawful (ExceptT ε m) where
  prop := CCPOBotLawful.prop (m := m)

instance (hd : ε -> _) [IsHandler hd] [_root_.CompleteLattice l] [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgPartial m] : MAlgPartial (ExceptT ε m) where
  csup_lift {α} chain := by
    intro post hchain; simp [MAlg.lift_ExceptT]
    solve_by_elim [MAlgPartial.csup_lift (m := m)]

attribute [-simp] le_bot_iff in
instance (hd : ε -> _) [IsHandler hd] [_root_.CompleteLattice l] [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgTotal m] : MAlgTotal (ExceptT ε m) where
  bot_lift := by
    intro post hchain; simp [MAlg.lift_ExceptT]
    solve_by_elim [MAlgTotal.bot_lift (m := m)]
