/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Left-distributivity of substitution and the monomial hom-set

This file collects the *left*-distributivity laws for the substitution product
`◃` over the coproduct and product of polynomial functors, promoted to
lens-equivalences `≃ₗ`, together with the representable-hom description of lenses
out of a monomial. These are distributive laws of Spivak–Niu, *Polynomial
Functors: A General Theory of Interaction*, Chapter 6.

Substitution distributes over the various operations *on the left* — that is,
in the outer position of `p ◃ r` — because at the level of the underlying
endofunctors `(p ◃ r)(X) = p(r(X))` and `p ↦ p(r(X))` preserves sums and
products.

* **Prop. 6.47 / (6.48)** `(p + q) ◃ r ≃ₗ (p ◃ r) + (q ◃ r)` is already available
  as `PFunctor.Lens.Equiv.sumCompDistrib`.
* **(6.50)** the `Σ`-indexed generalization `(Σ i, Fᵢ) ◃ r ≃ₗ Σ i, (Fᵢ ◃ r)` is
  `PFunctor.Lens.sigmaCompDistrib`.
* **(6.49)** `(p * q) ◃ r ≃ₗ (p ◃ r) * (q ◃ r)` is `Lens.Equiv.prodCompDistrib`
  below, obtained from the object-level `PFunctor.Equiv.prodCompDistrib`.
* **Ex. 6.55** the scalar special case `(A · p) ◃ q ≃ₗ A · (p ◃ q)`, phrased via
  the constant functor as `(C A * p) ◃ q ≃ₗ C A * (p ◃ q)`, is
  `Lens.Equiv.scalarCompDistrib` below.

Each lens-equivalence is produced from an object-level `≃ₚ` through
`PFunctor.Equiv.toLensEquiv`, which discharges the lens round-trips.

Substitution does **not** distribute over products on the *right*: in general
`p ◃ (q * r)` and `(p ◃ q) * (p ◃ r)` differ (Spivak–Niu, Ex. 6.56). A concrete
witness of this failure lives in the companion test file.

## Hom-sets out of a monomial

**(6.65) / (A8)** A lens `A y^ B ⇆ p` is exactly a function `A → p(B)`: its
forward position map is `A → p.A` and its backward direction map assigns to each
`a` a function `p.B (toFunA a) → B`, together packaging as an element of
`p.Obj B = Σ x : p.A, (p.B x → B)`. This is `Lens.homMonomialEquiv`.

## Future work

The `Π`-indexed law `(Π i, Fᵢ) ◃ r ≃ₗ Π i, (Fᵢ ◃ r)` (Spivak–Niu (6.51)) is not
yet formalized.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃

namespace PFunctor

namespace Equiv

/-! ## Substitution over a scalar (object level) -/

/-- **Spivak–Niu Ex. 6.55**, object level: substituting into a scalar multiple
splits off the scalar, `(C A * p) ◃ q ≃ₚ C A * (p ◃ q)`.

The empty direction type of `C A` makes the left injection of a direction
vacuous, so a position of `(C A * p) ◃ q` is a scalar `a : A` together with a
substitution position of `p ◃ q`; the fibers regroup via `Equiv.sumSigmaDistrib`
after discarding the empty summand. -/
def scalarCompDistrib {A : Type uA} {p : PFunctor.{uA₁, uB₁}} {q : PFunctor.{uA₂, uB₂}} :
    PFunctor.Equiv.{max uA uA₁ uA₂ uB₁, max uB₁ uB₂, max uA uA₁ uA₂ uB₁, max uB₁ uB₂}
      (((C A : PFunctor.{uA, uB₁}) * p : PFunctor.{max uA uA₁, uB₁}) ◃ q)
      ((C A : PFunctor.{uA, uB₁}) *
       (p ◃ q : PFunctor.{max uA₁ uA₂ uB₁, max uB₁ uB₂})) where
  equivA :=
    { toFun := fun x => (x.1.1, ⟨x.1.2, fun pb => x.2 (Sum.inr pb)⟩)
      invFun := fun y => ⟨(y.1, y.2.1), Sum.elim PEmpty.elim y.2.2⟩
      left_inv := by
        rintro ⟨⟨a, pa⟩, f⟩
        refine Sigma.ext rfl (heq_of_eq ?_)
        funext x
        cases x with
        | inl e => exact e.elim
        | inr pb => rfl
      right_inv := by
        rintro ⟨a, ⟨pa, g⟩⟩
        rfl }
  equivB := fun x =>
    (_root_.Equiv.sumSigmaDistrib (fun b => q.B (x.2 b))).trans
      (_root_.Equiv.sumCongr (_root_.Equiv.equivOfIsEmpty _ PEmpty) (_root_.Equiv.refl _))

end Equiv

namespace Lens

namespace Equiv

/-! ## Substitution over a product and a scalar (lens level) -/

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- **Spivak–Niu (6.49)**: `(P * Q) ◃ R ≃ₗ (P ◃ R) * (Q ◃ R)`, the
lens-equivalence obtained from the object-level `PFunctor.Equiv.prodCompDistrib`. -/
def prodCompDistrib :
    Lens.Equiv.{max uA₁ uA₂ uA₃ uB₁ uB₂, max uB₁ uB₂ uB₃,
                max uA₁ uA₂ uA₃ uB₁ uB₂, max uB₁ uB₂ uB₃}
      ((P * Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ◃ R)
      ((P ◃ R) * (Q ◃ R) : PFunctor.{max uA₁ uA₂ uA₃ uB₁ uB₂, max uB₁ uB₂ uB₃}) :=
  PFunctor.Equiv.toLensEquiv (PFunctor.Equiv.prodCompDistrib P Q R)

/-- **Spivak–Niu Ex. 6.55**: `(C A * p) ◃ q ≃ₗ C A * (p ◃ q)`, the
lens-equivalence obtained from `PFunctor.Equiv.scalarCompDistrib`. -/
def scalarCompDistrib {A : Type uA} {p : PFunctor.{uA₁, uB₁}} {q : PFunctor.{uA₂, uB₂}} :
    Lens.Equiv.{max uA uA₁ uA₂ uB₁, max uB₁ uB₂, max uA uA₁ uA₂ uB₁, max uB₁ uB₂}
      (((C A : PFunctor.{uA, uB₁}) * p : PFunctor.{max uA uA₁, uB₁}) ◃ q)
      ((C A : PFunctor.{uA, uB₁}) *
       (p ◃ q : PFunctor.{max uA₁ uA₂ uB₁, max uB₁ uB₂})) :=
  PFunctor.Equiv.toLensEquiv PFunctor.Equiv.scalarCompDistrib

end Equiv

/-! ## Lenses out of a monomial -/

/-- **Spivak–Niu (6.65) / (A8)**: a lens `A y^ B ⇆ p` is the same data as a
function `A → p(B)`.

The forward position map is a function `A → p.A` and the backward direction map
sends each `a` to a function `p.B (toFunA a) → B`; bundling these pointwise gives
an element of `p.Obj B = Σ x : p.A, (p.B x → B)`. Both round-trips hold
definitionally. -/
def homMonomialEquiv {A : Type uA} {B : Type uB} {p : PFunctor.{uA₂, uB₂}} :
    Lens (monomial A B) p ≃ (A → p.Obj B) where
  toFun := fun l a => ⟨l.toFunA a, l.toFunB a⟩
  invFun := fun g => (fun a => (g a).1) ⇆ (fun a => (g a).2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end Lens

end PFunctor
