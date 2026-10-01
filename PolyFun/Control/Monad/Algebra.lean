/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Order.CompleteLattice.Basic

/-!
# Monad algebras

This file contains two layers:

1. A minimal `MonadAlgebra` interface: a structure map `m α → α`, made Eilenberg-Moore
   by `LawfulMonadAlgebra`.
2. Ordered monad algebras `MAlgOrdered m l`: a structure map `μ : m l → l` into a complete
   lattice that fixes `pure` and is monotone under `bind`. An ordered algebra is the most
   economical presentation of an *exact* weakest-precondition interpretation: one map and two
   laws determine `wp x post := μ (x >>= fun a => pure (post a))`, which distributes over
   `pure` and `bind` with equality. `MAlgOrdered.toWPMonad`
   (`PolyFun.Control.Monad.Algebra.WP`) installs it as a core `WPMonad` together with its
   `ExactWPMonad` instance; reasoning then happens on core's `wp`, under the equational
   `simp` set of `PolyFun.Control.Monad.ExactWP`.

Public credit / attribution:
- Loom project: https://github.com/verse-lab/loom
- POPL 2026 paper: "Foundational Multi-Modal Program Verifiers", Vladimir Gladshtein, George
  Pîrlea, Qiyuan Zhao, Vitaly Kurin, and Ilya Sergey.
  DOI: https://doi.org/10.1145/3776719

The ordered monad algebra perspective (`MAlgOrdered`) in this file is adapted from Loom's
`MonadAlgebras` development.
-/

@[expose] public section

universe u v

/-- An algebra for a monad `m`: a structure map collapsing a monadic value `m α` into a plain
value of `α`. -/
class MonadAlgebra (m : Type u → Type v) where
  /-- The structure map of the algebra, collapsing `m α` into `α`. -/
  monadAlg {α : Type u} : m α → α

export MonadAlgebra (monadAlg)

/-- A monad algebra is lawful when its structure map is compatible with the monad's `pure` and
`bind`, making it an Eilenberg-Moore algebra. -/
class LawfulMonadAlgebra (m : Type u → Type v) [Monad m] [MonadAlgebra m] where
  monadAlg_pure {α : Type u} (a : α) : monadAlg (pure a : m α) = a
  monadAlg_bind {α β : Type u} (ma : m α) (mb : α → m β) :
    monadAlg (mb (monadAlg ma)) = monadAlg (ma >>= mb)

export LawfulMonadAlgebra (monadAlg_pure monadAlg_bind)

attribute [simp] monadAlg_pure monadAlg_bind

/-! ## Ordered monad algebras

There is deliberately no globally registered instance. The structure map `μ : m l → l` is a
choice of semantics, not something a monad determines: on `FreeM P` it is a per-operation spec
(`PFunctor.OpSpec.toMAlgOrdered` takes the spec and its monotonicity proof as arguments), and a
downstream probabilistic carrier integrates against a chosen measure. Install the intended
algebra locally or scoped at a verification boundary, and let core's transformer instances lift
the derived interpretation. -/

/-- An ordered monad algebra: a structure map into a complete lattice that fixes `pure` and is
monotone under `bind`. It presents an exact weakest-precondition interpretation;
see `MAlgOrdered.toWPMonad`. -/
class MAlgOrdered (m : Type u → Type v) (l : Type u) [Monad m] [CompleteLattice l] where
  /-- The ordered algebra's structure map, collapsing `m l` into a lattice element `l`. -/
  μ : m l → l
  μ_pure : ∀ x : l, μ (pure x) = x
  μ_bind_mono {α : Type u} :
    ∀ (f g : α → m l), (∀ a, μ (f a) ≤ μ (g a)) →
      ∀ x : m α, μ (x >>= f) ≤ μ (x >>= g)

namespace MAlgOrdered

variable {m : Type u → Type v} {l : Type u} [Monad m] [CompleteLattice l] [MAlgOrdered m l]
variable {α : Type u}

/-- Continuations with equal images under `μ` give binds with equal images. -/
theorem μ_bind (x : m α) (f g : α → m l) (h : ∀ a, MAlgOrdered.μ (f a) = MAlgOrdered.μ (g a)) :
    MAlgOrdered.μ (x >>= f) = MAlgOrdered.μ (x >>= g) := by
  apply le_antisymm
  · exact MAlgOrdered.μ_bind_mono f g (fun a => by simp [h a]) x
  · exact MAlgOrdered.μ_bind_mono g f (fun a => by simp [h a]) x

end MAlgOrdered
