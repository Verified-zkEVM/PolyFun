/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.GPFunctor.Basic
public import PolyFun.IPFunctor.Chart.Basic

/-!
# Charts Between Graded Polynomial Functors

A `Chart P Q` between two graded polynomial functors `P Q : GPFunctor G` is a *covariant*
morphism: forward maps on both positions and responses, together with the grade preservation
law `grade_eq` in the chart direction (the pushed-forward shape and the original shape carry
the same grade).

Charts and lenses are dual: lenses pull responses *back* (contravariantly), charts push them
*forward*. See [`Lens`](../Lens/Basic.lean) for the contravariant analogue. As there,
`grade_eq` is an equality of grade values, discharged by `rfl` for most concrete charts, and
over `[Mul G]` it induces the indexed `src_eq` on the `toIPFunctor` images (`toIPChart`).
-/

@[expose] public section

universe uG uA uA₁ uA₂ uA₃ uA₄ uB uB₁ uB₂ uB₃ uB₄

namespace GPFunctor

variable {G : Type uG}

/-- A **chart** between graded polynomial functors `P Q : GPFunctor G`: a forward map on
positions, a forward map on responses, and the grade preservation law `grade_eq`. -/
structure Chart (P : GPFunctor.{uG, uA₁, uB₁} G) (Q : GPFunctor.{uG, uA₂, uB₂} G) where
  /-- Forward map on positions. -/
  toFunA : P.A → Q.A
  /-- Forward map on responses: a `P`-response at `a` pushes to a `Q`-response at the
  forward-mapped shape `toFunA a`. -/
  toFunB : ∀ a, P.B a → Q.B (toFunA a)
  /-- Grade preservation: the pushed-forward shape carries the same grade. -/
  grade_eq : ∀ a, Q.grade (toFunA a) = P.grade a

namespace Chart

/-- The identity chart. -/
protected def id (P : GPFunctor.{uG, uA, uB} G) : Chart P P where
  toFunA := id
  toFunB _ := id
  grade_eq _ := rfl

/-- Composition of charts (diagrammatic order: `c ∘c c'` applies `c'` first, then `c`). -/
def comp {P : GPFunctor.{uG, uA₁, uB₁} G} {Q : GPFunctor.{uG, uA₂, uB₂} G}
    {R : GPFunctor.{uG, uA₃, uB₃} G} (c : Chart Q R) (c' : Chart P Q) : Chart P R where
  toFunA := c.toFunA ∘ c'.toFunA
  toFunB a := c.toFunB (c'.toFunA a) ∘ c'.toFunB a
  grade_eq a := (c.grade_eq (c'.toFunA a)).trans (c'.grade_eq a)

@[inherit_doc] scoped infixl:75 " ∘c " => GPFunctor.Chart.comp

variable {P : GPFunctor.{uG, uA₁, uB₁} G} {Q : GPFunctor.{uG, uA₂, uB₂} G}
  {R : GPFunctor.{uG, uA₃, uB₃} G} {S : GPFunctor.{uG, uA₄, uB₄} G}

@[simp]
theorem id_comp (f : Chart P Q) : (Chart.id Q) ∘c f = f := rfl

@[simp]
theorem comp_id (f : Chart P Q) : f ∘c (Chart.id P) = f := rfl

theorem comp_assoc (c : Chart R S) (c' : Chart Q R) (c'' : Chart P Q) :
    (c ∘c c') ∘c c'' = c ∘c (c' ∘c c'') := rfl

/-! ## Equivalence (isomorphism in the chart category) -/

/-- A structural equivalence in the chart category. -/
@[ext]
structure Equiv (P : GPFunctor.{uG, uA₁, uB₁} G) (Q : GPFunctor.{uG, uA₂, uB₂} G) where
  /-- The forward chart. -/
  toChart : Chart P Q
  /-- The inverse chart. -/
  invChart : Chart Q P
  /-- Round-trip on `P`. -/
  left_inv : invChart ∘c toChart = Chart.id P
  /-- Round-trip on `Q`. -/
  right_inv : toChart ∘c invChart = Chart.id Q

@[inherit_doc] scoped infix:50 " ≃c " => GPFunctor.Chart.Equiv

namespace Equiv

@[refl]
def refl (P : GPFunctor.{uG, uA, uB} G) : P ≃c P where
  toChart := Chart.id P
  invChart := Chart.id P
  left_inv := rfl
  right_inv := rfl

@[symm]
def symm (e : P ≃c Q) : Q ≃c P where
  toChart := e.invChart
  invChart := e.toChart
  left_inv := e.right_inv
  right_inv := e.left_inv

@[trans]
def trans (e₁ : P ≃c Q) (e₂ : Q ≃c R) : P ≃c R where
  toChart := e₂.toChart ∘c e₁.toChart
  invChart := e₁.invChart ∘c e₂.invChart
  left_inv := by
    rw [comp_assoc]
    rw (occs := [2]) [← comp_assoc]
    simp [e₁.left_inv, e₂.left_inv]
  right_inv := by
    rw [comp_assoc]
    rw (occs := [2]) [← comp_assoc]
    simp [e₁.right_inv, e₂.right_inv]

end Equiv

/-! ## Induced indexed and plain charts -/

/-- The indexed chart induced on the `toIPFunctor` images: the source-index preservation law
follows from grade preservation by left multiplication with the accumulated grade. -/
def toIPChart [Mul G] {P : GPFunctor.{uG, uA₁, uB₁} G} {Q : GPFunctor.{uG, uA₂, uB₂} G}
    (c : Chart P Q) : IPFunctor.Chart P.toIPFunctor Q.toIPFunctor where
  toFunA _ := c.toFunA
  toFunB _ a := c.toFunB a
  src_eq g a _ := congrArg (g * ·) (c.grade_eq a)

@[simp]
theorem toIPChart_id [Mul G] (P : GPFunctor.{uG, uA, uB} G) :
    (Chart.id P).toIPChart = IPFunctor.Chart.id P.toIPFunctor := rfl

@[simp]
theorem toIPChart_comp [Mul G] (c : Chart Q R) (c' : Chart P Q) :
    (c ∘c c').toIPChart = IPFunctor.Chart.comp c.toIPChart c'.toIPChart := rfl

/-- The plain chart induced on the underlying containers, forgetting the grades. -/
def toPChart {P : GPFunctor.{uG, uA₁, uB₁} G} {Q : GPFunctor.{uG, uA₂, uB₂} G}
    (c : Chart P Q) : PFunctor.Chart P.toPFunctor Q.toPFunctor where
  toFunA := c.toFunA
  toFunB := c.toFunB

end Chart

end GPFunctor
