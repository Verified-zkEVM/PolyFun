/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Handler.Stateful.Combinators

/-!
# Deprecated stateful-handler contracts

The parallel handler retains its constructor unfolding and old run-lemma rewrite heads.
-/

@[expose] public section

set_option linter.deprecated false

universe u v uA uA'

namespace PFunctor.Handler.Stateful

variable {m : Type u → Type v} {S T : Type u}
variable {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}

-- Old explicit unfolding on each summand.
example [Functor m] (f : Stateful m S P) (g : Stateful m T Q) (a : P.A) :
    parallel f g (.inl a) =
      StateT.mk (fun st => Prod.map _root_.id (·, st.2) <$> (f a).run st.1) := by
  simp only [parallel]

example [Functor m] (f : Stateful m S P) (g : Stateful m T Q) (b : Q.A) :
    parallel f g (.inr b) =
      StateT.mk (fun st => Prod.map _root_.id (st.1, ·) <$> (g b).run st.2) := by
  simp only [parallel]

-- Old named arguments and rewrite heads through an ordinary import.
example [Functor m] (f : Stateful m S P) (g : Stateful m T Q) (a : P.A) (st : S × T) :
    (parallel (f := f) (g := g) (.inl a)).run st =
      Prod.map _root_.id (·, st.2) <$> (f a).run st.1 := by
  rw [parallel_inl_run (f := f) (g := g) (a := a) (st := st)]

example [Functor m] (f : Stateful m S P) (g : Stateful m T Q) (b : Q.A) (st : S × T) :
    (parallel (f := f) (g := g) (.inr b)).run st =
      Prod.map _root_.id (st.1, ·) <$> (g b).run st.2 := by
  rw [parallel_inr_run (f := f) (g := g) (b := b) (st := st)]

end PFunctor.Handler.Stateful
