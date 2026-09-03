/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Cslib.Foundations.Control.Monad.IsMonadHom
public import PolyFun.Control.Monad.Hom

/-!
# Bundled monad morphisms as cslib's `IsMonadHom`

PolyFun's `MonadHom` bundles a family of maps with its `pure` and `bind` laws; cslib's
`IsMonadHom` is the unbundled predicate on such a family, requiring preservation of every
`Functor` / `Applicative` / `Monad` operator. For lawful monads the two agree, and this module
supplies the direction PolyFun consumes: every bundled morphism satisfies the predicate, so
cslib's transport lemmas (`IsMonadHom.map_listMapM`, `IsMonadHom.map_pfunctorFreeMLiftM`, …)
apply to it. It is separate from `PolyFun.Control.Monad.Hom` so consumers of the base morphism
API do not acquire the cslib dependency unless they use it.
-/

public section

universe u v w

namespace MonadHom

variable {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
  [LawfulMonad m] [LawfulMonad n]

/-- A bundled monad morphism between lawful monads is a monad morphism in cslib's sense. -/
theorem isMonadHom (F : m →ᵐ n) : Cslib.IsMonadHom m n fun {_} x => F x :=
  .mk' F.mmap_pure F.mmap_bind

end MonadHom
