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


/- Ordered Monad Algebra instance for ReaderT -/
instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] : MAlgOrdered (ReaderT σ m) (σ -> l) where
  μ := fun rp r => inst.μ $ (· r) <$> rp r
  μ_ord_pure := by
    intros l; simp [pure, ReaderT.pure]; ext r
    solve_by_elim [MAlgOrdered.μ_ord_pure]
  μ_ord_bind := by
    intros α f g
    try simp [Function.comp, Pi.hasLe]
    intros le x r
    have leM := @inst.μ_ord_bind (α) (fun a => (· r) <$> f a r) (fun a => (· r) <$> g a r)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; intro; apply le


instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] [inst': MAlgDet m l]
   : MAlgDet (ReaderT σ m) (σ -> l) where
    angelic := by
      intros α ι c p _ s;
      simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map]
      have h := inst'.angelic (α := α) (c := c s) (p := fun i x => p i x s)
      simp [MAlg.lift, MAlg.μ] at h
      apply h
    demonic := by
      intros α ι c p _ s;
      simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map]
      have h := inst'.demonic (α := α) (c := c s) (p := fun i x => p i x s)
      simp [MAlg.lift, MAlg.μ] at h
      apply h


instance [Monad m] [CCPOBot m] : CCPOBot (ReaderT σ m) where
  compBot := fun _ => CCPOBot.compBot

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] : CCPOBotLawful (ReaderT σ m) where
  prop := by
    intro α
    apply Lean.Order.PartialOrder.rel_antisymm
    · intro s
      change Lean.Order.PartialOrder.rel (CCPOBot.compBot (m := m)) _
      rw [CCPOBotLawful.prop (m := m)]
      exact Lean.Order.bot_le _
    · exact Lean.Order.bot_le _


lemma MAlg.lift_ReaderT [Monad m] [LawfulMonad m] [CompleteLattice l] [inst: MAlgOrdered m l] (x : ReaderT σ m α) :
  MAlg.lift x post = fun s => MAlg.lift (x s) (fun xs => post xs s) := by
    simp [MAlg.lift, Functor.map, MAlgOrdered.μ]

open Lean.Order
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgPartial m] : MAlgPartial (ReaderT σ m) where
  csup_lift {α} chain := by
    intro post hchain
    simp only [MAlg.lift_ReaderT]
    rw [@Pi.le_def]; simp only [iInf_apply]; intro s
    rw [← fun_csup_eq]; unfold fun_csup
    apply le_trans' (MAlgPartial.csup_lift (m := m) _ _ (chain_apply hchain s))
    repeat rw [@iInf_subtype']
    refine iInf_mono' ?_; simp [Membership.mem, Set.Mem]; aesop

attribute [-simp] le_bot_iff in
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)]  [MonoBind m]
  [MAlgTotal m] : MAlgTotal (ReaderT σ m) where
  bot_lift := by
    intro α post s
    simp only [MAlg.lift_ReaderT]
    have hb : (bot : ReaderT σ m α) s = (bot : m α) := by
      have h := @Lean.Order.bot_le (σ → m α) inferInstance
        (fun (_ : σ) => (bot : m α))
      apply Lean.Order.PartialOrder.rel_antisymm
      · exact h s
      · exact Lean.Order.bot_le _
    rw [hb]
    apply MAlgTotal.bot_lift (m := m)

instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l]
  [inst': NoFailure m] : NoFailure (ReaderT σ m) where
  noFailure := by
    intro _ _; simp [MAlg.lift_ReaderT, inst'.noFailure]; rfl

/- Monad Transformer Algebra instance for ReaderT -/
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MAlgOrdered m l] :
  MAlgLift m l (ReaderT σ m) (σ -> l) where
    μ_lift := by
      intros; simp [MAlg.lift_ReaderT]; ext;
      simp [liftM, instMonadLiftTOfMonadLift, MonadLift.monadLift]; rfl
