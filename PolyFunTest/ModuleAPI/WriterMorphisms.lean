/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.Control.Monad.Hom.Writer

/-!
# Ordinary-import canaries for writer morphisms

Mapping a writer's output along a monoid hom, and reading an additive log as a running total, run
as their definitions say. The examples check that these runs stay definitional through ordinary
imports, with the base monad's result universe independent of its own.
-/

universe u v

namespace PolyFunTest.ModuleAPI.WriterMorphisms

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type u}

example {M N : Type u} [Monoid M] [Monoid N] (f : M →* N) (x : WriterT M m α) :
    (WriterT.mapOutputHom f x).run = Prod.map id f <$> x.run :=
  rfl

example {ω : Type u} [AddMonoid ω] (x : WriterT (Multiplicative ω) m α) (t : ω) :
    (WriterT.toStateTHom x).run t = (fun p => (p.1, t + Multiplicative.toAdd p.2)) <$> x.run :=
  rfl

end PolyFunTest.ModuleAPI.WriterMorphisms
