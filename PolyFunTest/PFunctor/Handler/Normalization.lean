/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Handler.Normalization

/-!
# Handler normalization examples

Regression canaries for the `handler_nf` simp set. The concrete example uses
two distinguishable answers and state updates, so swapping the answer and
state components, choosing the wrong branch, or dropping a state update
changes the observed result.
-/

@[expose] public section

namespace PFunctor.Handler.Normalization.Examples

abbrev Query : PFunctor.{0, 0} := monomial Bool Nat

def answerAndAdvance : Handler.Stateful Option Nat Query :=
  fun query state =>
    Bool.rec (some (state + 20, state + 2))
      (some (state + 10, state + 1)) query

def twoQueries : FreeM Query (Nat × Nat) :=
  FreeM.liftBind true fun first =>
    FreeM.liftBind false fun second =>
      pure (first, second)

/-- `handler_nf` normalizes nested free-handler execution through the base
effect while preserving branch selection and state handoff. -/
example : answerAndAdvance.run twoQueries 3 = some ((13, 24), 6) := by
  simp only [handler_nf, twoQueries]
  rfl

/-- The direct `liftBind` and derived `bind` normalization paths agree. -/
example {m : Type → Type} [Monad m] [LawfulMonad m] {S α : Type}
    (h : Handler.Stateful m S Query)
    (query : Bool) (next : Nat → FreeM Query α) (state : S) :
    h.run (FreeM.lift query >>= next) state =
      (h query).run state >>= fun result => h.run (next result.1) result.2 := by
  simp only [handler_nf]

/-- Transformer run equations are part of the same explicit normal form. -/
example {m : Type → Type} [Monad m] {S α β : Type} (x : StateT S m α)
    (next : α → StateT S m β) (state : S) :
    (x >>= next).run state =
      x.run state >>= fun result => (next result.1).run result.2 := by
  simp only [handler_nf]

example {m : Type → Type} {α β ω : Type} [Monad m] [Monoid ω]
    (x : WriterT ω m α)
    (next : α → WriterT ω m β) :
    (x >>= next).run =
      x.run >>= fun result =>
        (fun output => (output.1, result.2 * output.2)) <$> (next result.1).run := by
  simp only [handler_nf]

end PFunctor.Handler.Normalization.Examples
