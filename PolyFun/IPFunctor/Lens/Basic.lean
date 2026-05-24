/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Basic

/-!
# Lenses Between Indexed Polynomial Functors

A `Lens P Q` between two indexed polynomial functors `P Q : IPFunctor I J` is a Cartesian
morphism over the same input/output indices: a forward map on positions and a *backward* map
on responses, together with the *source-index preservation law* `src_eq` that says the two
child sources (computed via `P.src` after pulling back, or via `Q.src` directly) agree in `I`.

The `src_eq` law is equality of index *values* in `I`, not of types, so most concrete lenses
discharge it by `rfl`. In general it induces transports in object maps because children live
in fibers over `src ...`.

This file provides the basic structure plus identity, composition, and a structural-equivalence
companion (`Lens.Equiv`). The richer monoidal / distributive infrastructure of
[`PFunctor.Lens`](../../PFunctor/Lens/Basic.lean) is intentionally not mirrored here yet —
add operations on demand as downstream consumers need them.
-/

@[expose] public section

universe uI uJ uA uA₁ uA₂ uA₃ uA₄ uB uB₁ uB₂ uB₃ uB₄

namespace IPFunctor

variable {I : Type uI} {J : Type uJ}

/-- A **lens** between indexed polynomial functors `P Q : IPFunctor I J`: a forward map on
positions, a backward map on responses, and the source-index preservation law `src_eq`. -/
structure Lens (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J)
                (Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J) where
  /-- Forward map on positions, indexed by the output index `j : J`. -/
  toFunA : ∀ j, P.A j → Q.A j
  /-- Backward map on responses: a `Q`-response at `toFunA j a` pulls back to a `P`-response
  at the original shape `a`. -/
  toFunB : ∀ j a, Q.B j (toFunA j a) → P.B j a
  /-- Source-index preservation: the pulled-back child source agrees with the original. -/
  src_eq : ∀ j a d, P.src j a (toFunB j a d) = Q.src j (toFunA j a) d

namespace Lens

/-- The identity lens. -/
protected def id (P : IPFunctor.{uI, uJ, uA, uB} I J) : Lens P P where
  toFunA _ := id
  toFunB _ _ := id
  src_eq _ _ _ := rfl

/-- Composition of lenses (diagrammatic / functor-composition order: `l ∘ₗ l'` applies `l'`
first, then `l`). -/
def comp {P : IPFunctor.{uI, uJ, uA₁, uB₁} I J}
    {Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J}
    {R : IPFunctor.{uI, uJ, uA₃, uB₃} I J}
    (l : Lens Q R) (l' : Lens P Q) : Lens P R where
  toFunA j := l.toFunA j ∘ l'.toFunA j
  toFunB j a := l'.toFunB j a ∘ l.toFunB j (l'.toFunA j a)
  src_eq j a d := by
    simp only [Function.comp_apply, l'.src_eq, l.src_eq]

@[inherit_doc] scoped infixl:75 " ∘ₗ " => IPFunctor.Lens.comp

variable {P : IPFunctor.{uI, uJ, uA₁, uB₁} I J}
  {Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J}
  {R : IPFunctor.{uI, uJ, uA₃, uB₃} I J}
  {S : IPFunctor.{uI, uJ, uA₄, uB₄} I J}

@[simp]
theorem id_comp (f : Lens P Q) : (Lens.id Q) ∘ₗ f = f := rfl

@[simp]
theorem comp_id (f : Lens P Q) : f ∘ₗ (Lens.id P) = f := rfl

theorem comp_assoc (l : Lens R S) (l' : Lens Q R) (l'' : Lens P Q) :
    (l ∘ₗ l') ∘ₗ l'' = l ∘ₗ (l' ∘ₗ l'') := rfl

/-! ## Equivalence (isomorphism in the lens category) -/

/-- A structural equivalence in the lens category: a pair of lenses that compose to identity
in both directions. -/
@[ext]
structure Equiv (P : IPFunctor.{uI, uJ, uA₁, uB₁} I J)
                (Q : IPFunctor.{uI, uJ, uA₂, uB₂} I J) where
  /-- The forward lens. -/
  toLens : Lens P Q
  /-- The inverse lens. -/
  invLens : Lens Q P
  /-- Round-trip on `P`. -/
  left_inv : invLens ∘ₗ toLens = Lens.id P
  /-- Round-trip on `Q`. -/
  right_inv : toLens ∘ₗ invLens = Lens.id Q

@[inherit_doc] scoped infix:50 " ≃ₗ " => IPFunctor.Lens.Equiv

namespace Equiv

@[refl]
def refl (P : IPFunctor.{uI, uJ, uA, uB} I J) : P ≃ₗ P where
  toLens := Lens.id P
  invLens := Lens.id P
  left_inv := rfl
  right_inv := rfl

@[symm]
def symm (e : P ≃ₗ Q) : Q ≃ₗ P where
  toLens := e.invLens
  invLens := e.toLens
  left_inv := e.right_inv
  right_inv := e.left_inv

@[trans]
def trans (e₁ : P ≃ₗ Q) (e₂ : Q ≃ₗ R) : P ≃ₗ R where
  toLens := e₂.toLens ∘ₗ e₁.toLens
  invLens := e₁.invLens ∘ₗ e₂.invLens
  left_inv := by
    rw [comp_assoc]
    rw (occs := [2]) [← comp_assoc]
    simp [e₁.left_inv, e₂.left_inv]
  right_inv := by
    rw [comp_assoc]
    rw (occs := [2]) [← comp_assoc]
    simp [e₁.right_inv, e₂.right_inv]

end Equiv

end Lens

end IPFunctor
