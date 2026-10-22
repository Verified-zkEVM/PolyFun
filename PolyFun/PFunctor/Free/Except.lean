/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Basic
public import PolyFun.PFunctor.Handler

/-!
# Explicit exceptional answers

`P.withExcept ε` preserves operation names and lets every answer be a core
`Except ε` value. `FreeM.withExcept` aborts on the first exceptional answer.
It is a fold over ordinary polynomial syntax, and its interpretation is exactly
the existing `ExceptT` interpretation. The syntax supports independent error,
answer and result universes; the transformer bridge aligns its monad universes.
-/

public section

universe uA uB uε uα uβ u v

namespace PFunctor

/-- The same dependent operations with explicit exceptional answers. -/
@[expose, reducible] def withExcept (P : PFunctor.{uA, uB}) (ε : Type uε) :
    PFunctor.{uA, max uε uB} where
  A := P.A
  B a := Except ε (P.B a)

namespace FreeM

variable {P : PFunctor.{uA, uB}} {ε : Type uε} {α : Type uα} {β : Type uβ}

/-- Adapt a finite client to explicit exceptional answers, returning its first error. -/
@[expose] def withExcept (program : FreeM P α) : FreeM (P.withExcept ε) (Except ε α) :=
  foldFreeM (P := P) (β := FreeM (P.withExcept ε) (Except ε α))
    (fun value => .pure (.ok value))
    (fun a next => FreeM.liftBind (P := P.withExcept ε) a fun
      | .error error => .pure (.error error)
      | .ok answer => next answer) program

@[simp] theorem withExcept_pure (value : α) :
    withExcept (ε := ε) (pure value : FreeM P α) = pure (.ok value) := by
  unfold withExcept
  rw [foldFreeM_pure]
  rfl

/-- An error answer returns immediately; only an ordinary answer enters the continuation. -/
@[freeM_unfold] theorem withExcept_liftBind (a : P.A) (next : P.B a → FreeM P α) :
    withExcept (ε := ε) (.liftBind a next) = .liftBind a (fun
      | .error error => .pure (.error error)
      | .ok answer => withExcept (next answer)) := by
  unfold withExcept
  rw [foldFreeM_liftBind]

/-- Adapting a dependent bind uses the ordinary exception-transformer continuation. -/
theorem withExcept_bind (program : FreeM P α) (next : α → FreeM P β) :
    withExcept (ε := ε) (program.bind next) =
      (withExcept program).bind (fun
        | .error error => .pure (.error error)
        | .ok value => withExcept (next value)) := by
  induction program with
  | pure value =>
    change withExcept (next value) = _
    rw [withExcept_pure]
    rfl
  | lift_bind a rest ih =>
    rw [← liftBind_eq]
    change withExcept (.liftBind a (fun answer => (rest answer).bind next)) = _
    rw [withExcept_liftBind, withExcept_liftBind]
    simp only [FreeM.bind]
    apply congrArg (FreeM.liftBind (P := P.withExcept ε) a)
    funext answer
    cases answer with
    | error error => rfl
    | ok answer => exact ih answer

end FreeM

namespace Handler

variable {P : PFunctor.{uA, u}} {ε : Type u} {m : Type u → Type v}

/-- Expose the core exception transformer's result as the interface's answer. -/
@[expose] def exceptAnswers (handler : Handler (ExceptT ε m) P) :
    Handler m (P.withExcept ε) := fun a => (handler a).run

end Handler

namespace FreeM

variable {P : PFunctor.{uA, u}} {ε α : Type u} {m : Type u → Type v} [Monad m]

/-- The explicit-answer fold agrees with exception-transformer interpretation. -/
theorem liftM_withExcept (handler : Handler (ExceptT ε m) P) (program : FreeM P α) :
    (withExcept program).liftM handler.exceptAnswers = (program.liftM handler).run := by
  induction program with
  | pure value => rw [withExcept_pure]; rfl
  | lift_bind a next ih =>
    rw [← liftBind_eq, withExcept_liftBind]
    change (handler.exceptAnswers a >>= fun answer => (match answer with
      | .error error => FreeM.pure (Except.error error)
      | .ok value => withExcept (next value) : FreeM (P.withExcept ε) (Except ε α)).liftM
        handler.exceptAnswers) =
        ((handler a >>= fun value => (next value).liftM handler).run)
    rw [ExceptT.run_bind]
    apply congrArg (Bind.bind (handler a).run)
    funext answer
    cases answer with
    | error error => rfl
    | ok value => exact ih value

end FreeM
end PFunctor
