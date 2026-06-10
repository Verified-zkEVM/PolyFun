/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.GPFunctor.Basic
public import PolyFun.IPFunctor.Lens.Basic

/-!
# Lenses Between Graded Polynomial Functors

A `Lens P Q` between two graded polynomial functors `P Q : GPFunctor G` is a Cartesian
morphism over the same grading type: a forward map on positions and a *backward* map on
responses, together with the *grade preservation law* `grade_eq` saying the image shape
carries the same grade.

`grade_eq` is an equality of grade *values* in `G`, not of types, so most concrete lenses
discharge it by `rfl`. Because grading is per-shape, the law mentions no responses — it is
strictly simpler than the source-index preservation law `src_eq` of
[`IPFunctor.Lens`](../../IPFunctor/Lens/Basic.lean), and over `[Mul G]` it induces that law
on the indexed images (`toIPLens`).

This file provides the basic structure plus identity, composition, the structural-equivalence
companion (`Lens.Equiv`), and the bridges to `IPFunctor.Lens` and `PFunctor.Lens`. The richer
monoidal / distributive infrastructure of [`PFunctor.Lens`](../../PFunctor/Lens/Basic.lean)
is intentionally not mirrored here yet — add operations on demand as downstream consumers
need them. There is no transport of `GFreeM` trees along a lens yet, matching the indexed
layer (which has no `FreeM` transport along morphisms either).
-/

@[expose] public section

universe uG uA uA₁ uA₂ uA₃ uA₄ uB uB₁ uB₂ uB₃ uB₄

namespace GPFunctor

variable {G : Type uG}

/-- A **lens** between graded polynomial functors `P Q : GPFunctor G`: a forward map on
positions, a backward map on responses, and the grade preservation law `grade_eq`. -/
structure Lens (P : GPFunctor.{uG, uA₁, uB₁} G) (Q : GPFunctor.{uG, uA₂, uB₂} G) where
  /-- Forward map on positions. -/
  toFunA : P.A → Q.A
  /-- Backward map on responses: a `Q`-response at `toFunA a` pulls back to a `P`-response
  at the original shape `a`. -/
  toFunB : ∀ a, Q.B (toFunA a) → P.B a
  /-- Grade preservation: the image shape carries the same grade. -/
  grade_eq : ∀ a, P.grade a = Q.grade (toFunA a)

namespace Lens

/-- The identity lens. -/
protected def id (P : GPFunctor.{uG, uA, uB} G) : Lens P P where
  toFunA := id
  toFunB _ := id
  grade_eq _ := rfl

/-- Composition of lenses (diagrammatic / functor-composition order: `l ∘ₗ l'` applies `l'`
first, then `l`). -/
def comp {P : GPFunctor.{uG, uA₁, uB₁} G} {Q : GPFunctor.{uG, uA₂, uB₂} G}
    {R : GPFunctor.{uG, uA₃, uB₃} G} (l : Lens Q R) (l' : Lens P Q) : Lens P R where
  toFunA := l.toFunA ∘ l'.toFunA
  toFunB a := l'.toFunB a ∘ l.toFunB (l'.toFunA a)
  grade_eq a := (l'.grade_eq a).trans (l.grade_eq (l'.toFunA a))

@[inherit_doc] scoped infixl:75 " ∘ₗ " => GPFunctor.Lens.comp

variable {P : GPFunctor.{uG, uA₁, uB₁} G} {Q : GPFunctor.{uG, uA₂, uB₂} G}
  {R : GPFunctor.{uG, uA₃, uB₃} G} {S : GPFunctor.{uG, uA₄, uB₄} G}

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
structure Equiv (P : GPFunctor.{uG, uA₁, uB₁} G) (Q : GPFunctor.{uG, uA₂, uB₂} G) where
  /-- The forward lens. -/
  toLens : Lens P Q
  /-- The inverse lens. -/
  invLens : Lens Q P
  /-- Round-trip on `P`. -/
  left_inv : invLens ∘ₗ toLens = Lens.id P
  /-- Round-trip on `Q`. -/
  right_inv : toLens ∘ₗ invLens = Lens.id Q

@[inherit_doc] scoped infix:50 " ≃ₗ " => GPFunctor.Lens.Equiv

namespace Equiv

@[refl]
def refl (P : GPFunctor.{uG, uA, uB} G) : P ≃ₗ P where
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

/-! ## Induced indexed and plain lenses -/

/-- The indexed lens induced on the `toIPFunctor` images: the source-index preservation law
follows from grade preservation by left multiplication with the accumulated grade. -/
def toIPLens [Mul G] {P : GPFunctor.{uG, uA₁, uB₁} G} {Q : GPFunctor.{uG, uA₂, uB₂} G}
    (l : Lens P Q) : IPFunctor.Lens P.toIPFunctor Q.toIPFunctor where
  toFunA _ := l.toFunA
  toFunB _ a := l.toFunB a
  src_eq g a _ := congrArg (g * ·) (l.grade_eq a)

@[simp]
theorem toIPLens_id [Mul G] (P : GPFunctor.{uG, uA, uB} G) :
    (Lens.id P).toIPLens = IPFunctor.Lens.id P.toIPFunctor := rfl

@[simp]
theorem toIPLens_comp [Mul G] (l : Lens Q R) (l' : Lens P Q) :
    (l ∘ₗ l').toIPLens = IPFunctor.Lens.comp l.toIPLens l'.toIPLens := rfl

/-- The plain lens induced on the underlying containers, forgetting the grades. -/
def toPLens {P : GPFunctor.{uG, uA₁, uB₁} G} {Q : GPFunctor.{uG, uA₂, uB₂} G}
    (l : Lens P Q) : PFunctor.Lens P.toPFunctor Q.toPFunctor where
  toFunA := l.toFunA
  toFunB := l.toFunB

end Lens

end GPFunctor
