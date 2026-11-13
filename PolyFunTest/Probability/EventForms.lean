/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Monad.Measure.OptionT

/-!
# Event laws in the form of downstream event notation

Downstream notation for events of `do` sequences, such as VCVio's `Pr{…}[…]`, builds its final map
with the functor of the monad, `Monad.toApplicative.toFunctor`. Over `OptionT m` and an
`AlternativeMonad`, `p <$> mx` finds its functor through `Alternative` instead. These examples
check through an ordinary import that the event laws over these monads map through the monad's
functor, up to syntactic equality (`guard_hyp … :ₐ`). They also check that the form `p <$> mx`
does not match. They spell the expected map out instead of using the scoped notation `<$>ₘ`, so
they also catch a change to the notation.
-/

public section

namespace PolyFunTest.Probability.EventForms

/-! ## Optional computations -/

section optionT

variable {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α : Type}

example (mx : OptionT m α) (p : α → Prop) : True := by
  have h := OptionT.prEvent_eq_run mx p
  guard_hyp h :ₐ prEvent (Functor.map (self := Monad.toApplicative.toFunctor) p mx) =
    prEvent ((fun value ↦ value.elim False p) <$> mx.run)
  fail_if_success
    guard_hyp h :ₐ prEvent (p <$> mx) = prEvent ((fun value ↦ value.elim False p) <$> mx.run)
  trivial

example (mx : m α) (p : α → Prop) : True := by
  have h := OptionT.prEvent_lift mx p
  guard_hyp h :ₐ
    prEvent (Functor.map (self := Monad.toApplicative.toFunctor) p (OptionT.lift mx)) =
      prEvent (p <$> mx)
  fail_if_success guard_hyp h :ₐ prEvent (p <$> OptionT.lift mx) = prEvent (p <$> mx)
  trivial

example (mx : m α) (p : α → Prop) : True := by
  have h := OptionT.prEvent_liftM mx p
  guard_hyp h :ₐ
    prEvent (Functor.map (self := Monad.toApplicative.toFunctor) p (liftM mx : OptionT m α)) =
      prEvent (p <$> mx)
  fail_if_success
    guard_hyp h :ₐ prEvent (p <$> (liftM mx : OptionT m α)) = prEvent (p <$> mx)
  trivial

example (mx : m α) (p q : α → Prop) [DecidablePred p] : True := by
  have h := OptionT.prEvent_bind_guard mx p q
  guard_hyp h :ₐ
    prEvent (OptionT.lift mx >>= fun x ↦
      Functor.map (self := Monad.toApplicative.toFunctor) (fun _ ↦ q x)
        (guard (p x) : OptionT m Unit)) =
      prEvent ((fun x ↦ p x ∧ q x) <$> mx)
  fail_if_success
    guard_hyp h :ₐ
      prEvent (OptionT.lift mx >>= fun x ↦ (fun _ ↦ q x) <$> (guard (p x) : OptionT m Unit)) =
        prEvent ((fun x ↦ p x ∧ q x) <$> mx)
  trivial

example (mx : m (Option α)) (p : α → Prop) : True := by
  have h := OptionT.prEvent_mk mx p
  guard_hyp h :ₐ
    prEvent (Functor.map (self := Monad.toApplicative.toFunctor) p (OptionT.mk mx)) =
      prEvent ((fun o ↦ o.elim False p) <$> mx)
  fail_if_success
    guard_hyp h :ₐ prEvent (p <$> OptionT.mk mx) = prEvent ((fun o ↦ o.elim False p) <$> mx)
  trivial

end optionT

/-! ## Failure -/

section failure

variable {m : Type → Type} [AlternativeMonad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] [LawfulFailureEvalDistSemantics m] {α : Type}

example (p : α → Prop) : True := by
  have h := prEvent_failure (m := m) p
  guard_hyp h :ₐ prEvent (Functor.map (self := Monad.toApplicative.toFunctor) p (failure : m α)) = 0
  fail_if_success guard_hyp h :ₐ prEvent (p <$> (failure : m α)) = 0
  trivial

end failure

end PolyFunTest.Probability.EventForms
