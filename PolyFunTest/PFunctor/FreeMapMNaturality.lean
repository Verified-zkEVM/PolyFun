/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Basic

/-!
# Examples: universal property and naturality of the free-monad fold

Regression tests for the universal property and naturality of `FreeM.liftM` along a monad morphism:
`liftMHom_unique`, `liftM_natural`, `liftMHom_comp`, `run_liftM_mapHom`, `liftM_lift_eq_self`,
`liftMHom_lift_eq_id`, and `StateT.mapHom`. These are the upstream shape of the
fold-naturality bridges that VCVio's `simulateQ` / `evalDist` layer instantiates at
`φ := evalDist`.
-/

@[expose] public section

open PFunctor

namespace PolyFunTest.FreeMapM

/-- A small concrete polynomial for the canaries: two positions, `Bool`-many directions each. -/
def P : PFunctor := ⟨Bool, fun _ => Bool⟩

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]

/-- **Naturality** of the fold along a monad morphism applies. -/
example (s : (a : P.A) → m (P.B a)) (φ : m →ᵐ n) {α : Type} (x : FreeM P α) :
    φ (FreeM.liftM s x) = FreeM.liftM (fun a => φ (s a)) x :=
  FreeM.liftM_natural s φ x

/-- **Bundled naturality**: `φ ∘ₘ liftMHom s = liftMHom (φ ∘ s)`. -/
example (s : (a : P.A) → m (P.B a)) (φ : m →ᵐ n) :
    φ ∘ₘ FreeM.liftMHom s = FreeM.liftMHom (fun a => φ (s a)) :=
  FreeM.liftMHom_comp s φ

/-- **Universal property**: a monad hom out of `FreeM P` agreeing with `s` on generators is
`liftMHom s`. -/
example (s : (a : P.A) → m (P.B a)) (F : FreeM P →ᵐ m) (h : ∀ a, F (FreeM.lift a) = s a) :
    F = FreeM.liftMHom s :=
  FreeM.liftMHom_unique s F h

/-- The identity handler folds to the identity homomorphism. -/
example : FreeM.liftMHom (m := FreeM P) FreeM.lift = MonadHom.id (FreeM P) :=
  FreeM.liftMHom_lift_eq_id

/-- The identity handler folds any tree to itself. -/
example {α : Type} (x : FreeM P α) : FreeM.liftM FreeM.lift x = x :=
  FreeM.liftM_lift_eq_self x

/-- **Stateful naturality**: `φ` pushed through a `StateT`-threaded fold. -/
example (φ : m →ᵐ n) {σ α : Type} (impl : (a : P.A) → StateT σ m (P.B a))
    (x : FreeM P α) (s : σ) :
    (FreeM.liftM (fun a => StateT.mapHom φ (impl a)) x).run s = φ ((FreeM.liftM impl x).run s) :=
  FreeM.run_liftM_mapHom φ impl x s

/-- A concrete push-through: lifting `Id → Option` commutes with the fold — the shape a semantic
monad morphism (e.g. an evaluation-distribution map) instantiates. -/
example (s : (a : P.A) → Id (P.B a)) (x : FreeM P Bool) :
    MonadHom.ofLift Id Option (FreeM.liftM s x)
      = FreeM.liftM (fun a => MonadHom.ofLift Id Option (s a)) x :=
  FreeM.liftM_natural s (MonadHom.ofLift Id Option) x

end PolyFunTest.FreeMapM
