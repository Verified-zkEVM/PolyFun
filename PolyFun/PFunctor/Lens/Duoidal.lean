/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Cartesian

/-!
# Interchange maps relating tensor and composition

The category `Poly` carries two monoidal products that are both relevant to
interaction: the tensor (Dirichlet) product `⊗`, whose positions are pairs and
whose directions are pairs, and the substitution product `◃`, whose positions
package a first move together with a continuation. Spivak–Niu, *Polynomial
Functors: A Mathematical Theory of Interaction* §6.3.4–6.3.5 show that these two
products are **duoidal**: they share the unit `y` and there is a canonical
family of interchange lenses that make `(Poly, ⊗, ◃)` a duoidal category.

This file records the concrete ordering and interchange lenses underlying the
duoidal structure, together with their naturality, cartesianness, and the
concrete middle-four and unit coherence laws. It deliberately does not add an
abstract duoidal-category typeclass: the current API needs only these canonical
lenses and equations.

* `orderingLens` (Example 6.85) is the canonical lens `p ⊗ q → p ◃ q` that
  *orders* a pair of simultaneous moves into a sequence: it keeps the position
  of `p` first and makes the `q`-position constant. Its backward map is a
  bijection on every fiber, so `orderingLens_isCartesian` holds — the two
  products agree on directions.

* The `Equiv`s in `PFunctor.Lens.Equiv` (Example 6.84) collect the special
  cases where `orderingLens` is invertible, i.e. where `⊗` and `◃` genuinely
  coincide. These are exactly the cases in which one factor's positions carry a
  unique continuation:

  - `linearTensorLinear` : `Ay ⊗ By ≅ Ay ◃ By`;
  - `purePowerTensorPurePower` : `y^A ⊗ y^B ≅ y^A ◃ y^B`;
  - `linearTensor` : `By ⊗ p ≅ By ◃ p` (linear factor on the left);
  - `tensorPurePower` : `p ⊗ y^A ≅ p ◃ y^A` (pure-power factor on the right).

  Note: the book's `Ay ⊗ By ≅ Ay ◃ By` family uses `Ay = linear A`, the
  *linear* functor, not the *constant* functor `C A`. The constant analogue
  `C B ⊗ p ≅ C B ◃ p` is **false** in general: `C B ⊗ p ≅ C (B × p.A)` has
  `B × p.A` positions, whereas `C B ◃ p ≅ C B` has only `B` positions (a
  constant functor absorbs whatever it is substituted into). They agree only
  when `p.A` is a singleton, so no such `Equiv` is provided.

* `duoidalLens` (Equation 6.86) is the interchange lens
  `(p ◃ p') ⊗ (q ◃ q') → (p ⊗ q) ◃ (p' ⊗ q')`. Read operationally, it runs the
  two-phase protocols `p ◃ p'` and `q ◃ q'` side by side and reshuffles them so
  that the two first phases `p` and `q` run in parallel, followed by the two
  second phases `p'` and `q'` in parallel.

The remaining boundary is abstract packaging and the higher associativity
diagram for three interchange maps. The naturality, middle-four compatibility,
and unit laws used by concrete developments are proved below.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄
  uA₅ uB₅ uA₆ uB₆ uA₇ uB₇ uA₈ uB₈

namespace PFunctor
namespace Lens

/-! ## The ordering lens `p ⊗ q → p ◃ q` -/

/-- The **ordering lens** `p ⊗ q → p ◃ q` (Spivak–Niu Example 6.85).

On positions it turns a pair of simultaneous moves `(a, b) : p.A × q.A` into a
sequential position `⟨a, fun _ => b⟩ : p ◃ q`, where the continuation is the
constant map returning `b`. On directions, a `p ◃ q`-direction over
`⟨a, fun _ => b⟩` is a dependent pair `⟨u, v⟩` with `u : p.B a` and `v : q.B b`,
which maps back to the tensor-direction `(u, v) : p.B a × q.B b`. -/
def orderingLens (p : PFunctor.{uA₁, uB₁}) (q : PFunctor.{uA₂, uB₂}) :
    Lens (p ⊗ q) (p ◃ q) :=
  (fun (a, b) => ⟨a, fun _ => b⟩) ⇆ fun _ ⟨u, v⟩ => (u, v)

/-- The ordering lens is cartesian: on every fiber the backward map
`⟨u, v⟩ ↦ (u, v)` is the bijection between the (constant-family) dependent pair
`Σ _ : p.B a, q.B b` and the plain product `p.B a × q.B b`. In duoidal terms,
`⊗` and `◃` carry the *same* directions; they differ only in how positions are
packaged. -/
theorem orderingLens_isCartesian (p : PFunctor.{uA₁, uB₁}) (q : PFunctor.{uA₂, uB₂}) :
    (orderingLens p q).IsCartesian := fun _ab =>
  Function.bijective_iff_has_inverse.mpr
    ⟨fun uv => ⟨uv.1, uv.2⟩, fun _ => rfl, fun _ => rfl⟩

/-- Naturality of the ordering lens in both polynomial arguments. -/
@[simp]
theorem orderingLens_natural {p : PFunctor.{uA₁, uB₁}} {p' : PFunctor.{uA₂, uB₂}}
    {q : PFunctor.{uA₃, uB₃}} {q' : PFunctor.{uA₄, uB₄}}
    (f : Lens p p') (g : Lens q q') :
    orderingLens p' q' ∘ₗ (f ⊗ₗ g) = (f ◃ₗ g) ∘ₗ orderingLens p q := rfl

/-! ## The duoidal interchange lens

The interchange lens `(p ◃ p') ⊗ (q ◃ q') → (p ⊗ q) ◃ (p' ⊗ q')` runs two
two-phase protocols in parallel and regroups their phases. -/

/-- The **duoidal interchange lens** (Spivak–Niu Equation 6.86)

`(p ◃ p') ⊗ (q ◃ q') → (p ⊗ q) ◃ (p' ⊗ q')`.

A source position is a pair `(⟨a, f⟩, ⟨c, g⟩)`: two first moves `a : p.A`,
`c : q.A` with continuations `f : p.B a → p'.A`, `g : q.B c → q'.A`. It maps to
the sequential position `⟨(a, c), fun (u, w) => (f u, g w)⟩`: the two first
phases run in parallel as a single `p ⊗ q` move `(a, c)`, and the joint
continuation feeds each side's direction to its own continuation, producing a
`p' ⊗ q'` position.

On directions, a target direction over that position is
`⟨(u, w), (x, y)⟩` with `u : p.B a`, `w : q.B c`, `x : p'.B (f u)`,
`y : q'.B (g w)`; it maps back to the tensor of two composite directions
`(⟨u, x⟩, ⟨w, y⟩)`.

The concrete naturality, middle-four, cartesianness, and unit coherence laws
used by the current API are formalized below. The remaining part of
Spivak–Niu Proposition 6.87 is the higher three-interchange associativity
diagram and abstract duoidal-category packaging. -/
def duoidalLens (p : PFunctor.{uA₁, uB₁}) (p' : PFunctor.{uA₂, uB₂})
    (q : PFunctor.{uA₃, uB₃}) (q' : PFunctor.{uA₄, uB₄}) :
    Lens ((p ◃ p') ⊗ (q ◃ q')) ((p ⊗ q) ◃ (p' ⊗ q')) :=
  (fun pos => ⟨(pos.1.1, pos.2.1), fun uw => (pos.1.2 uw.1, pos.2.2 uw.2)⟩) ⇆
    (fun _pos dir => (⟨dir.1.1, dir.2.1⟩, ⟨dir.1.2, dir.2.2⟩))

/-- The interchange lens is cartesian: its backward map is the middle-four
permutation on direction pairs. -/
theorem duoidalLens_isCartesian (p : PFunctor.{uA₁, uB₁}) (p' : PFunctor.{uA₂, uB₂})
    (q : PFunctor.{uA₃, uB₃}) (q' : PFunctor.{uA₄, uB₄}) :
    (duoidalLens p p' q q').IsCartesian := fun _ =>
  Function.bijective_iff_has_inverse.mpr
    ⟨fun dir => ⟨(dir.1.1, dir.2.1), (dir.1.2, dir.2.2)⟩,
      fun _ => rfl, fun _ => rfl⟩

/-- Full four-variable naturality of duoidal interchange. -/
@[simp]
theorem duoidalLens_natural
    {p₁ : PFunctor.{uA₁, uB₁}} {p₂ : PFunctor.{uA₂, uB₂}}
    {q₁ : PFunctor.{uA₃, uB₃}} {q₂ : PFunctor.{uA₄, uB₄}}
    {r₁ : PFunctor.{uA₅, uB₅}} {r₂ : PFunctor.{uA₆, uB₆}}
    {s₁ : PFunctor.{uA₇, uB₇}} {s₂ : PFunctor.{uA₈, uB₈}}
    (f₁ : Lens p₁ r₁) (f₂ : Lens p₂ r₂)
    (g₁ : Lens q₁ s₁) (g₂ : Lens q₂ s₂) :
    duoidalLens r₁ r₂ s₁ s₂ ∘ₗ ((f₁ ◃ₗ f₂) ⊗ₗ (g₁ ◃ₗ g₂)) =
      ((f₁ ⊗ₗ g₁) ◃ₗ (f₂ ⊗ₗ g₂)) ∘ₗ duoidalLens p₁ p₂ q₁ q₂ := rfl

/-- The canonical middle-four tensor permutation
`(p ⊗ p') ⊗ (q ⊗ q') ≅ (p ⊗ q) ⊗ (p' ⊗ q')`.

This is the structural reordering required to state the lax-monoidal law for
`orderingLens` without silently identifying differently ordered products. -/
def Equiv.tensorMiddleFour
    (p : PFunctor.{uA₁, uB₁}) (p' : PFunctor.{uA₂, uB₂})
    (q : PFunctor.{uA₃, uB₃}) (q' : PFunctor.{uA₄, uB₄}) :
    ((p ⊗ p') ⊗ (q ⊗ q')) ≃ₗ ((p ⊗ q) ⊗ (p' ⊗ q')) where
  toLens := (fun ((a, b), (c, d)) => ((a, c), (b, d))) ⇆
    (fun _ ((a, b), (c, d)) => ((a, c), (b, d)))
  invLens := (fun ((a, b), (c, d)) => ((a, c), (b, d))) ⇆
    (fun _ ((a, b), (c, d)) => ((a, c), (b, d)))
  left_inv := rfl
  right_inv := rfl

/-- `orderingLens : (⊗) ⇒ (◃)` preserves the binary multiplication:
ordering each pair and then interchanging phases agrees with first applying the
middle-four permutation and then ordering the regrouped tensor products. -/
@[simp]
theorem orderingLens_duoidal
    (p : PFunctor.{uA₁, uB₁}) (p' : PFunctor.{uA₂, uB₂})
    (q : PFunctor.{uA₃, uB₃}) (q' : PFunctor.{uA₄, uB₄}) :
    duoidalLens p p' q q' ∘ₗ (orderingLens p p' ⊗ₗ orderingLens q q') =
      orderingLens (p ⊗ q) (p' ⊗ q') ∘ₗ
        (Equiv.tensorMiddleFour p p' q q').toLens := rfl

/-- Right-unit compatibility of `orderingLens`. -/
@[simp] theorem orderingLens_unit_right (p : PFunctor.{uA₁, uB₁}) :
    Equiv.compX.toLens ∘ₗ orderingLens p X = Equiv.tensorX.toLens := rfl

/-- Left-unit compatibility of `orderingLens`. -/
@[simp] theorem orderingLens_unit_left (p : PFunctor.{uA₁, uB₁}) :
    Equiv.XComp.toLens ∘ₗ orderingLens X p = Equiv.xTensor.toLens := rfl

/-! ## Catalogue of `⊗`/`◃` coincidences (Example 6.84)

These are the special cases in which `orderingLens` is an isomorphism, i.e. the
two monoidal products agree outright. In each case one of the factors has a
unique continuation into the other, so the ordering of moves carries no
information.

These catalogue isos are reference API — book-completeness formalizations of
Example 6.84, exercised in `PolyFunTest/PFunctor/Lens/Duoidal.lean`. The
load-bearing formers of this file are `orderingLens` and `duoidalLens` above
(consumed by `PolyFun/PFunctor/Dynamical/Game.lean`). -/

namespace Equiv

/-- `Ay ⊗ By ≅ Ay ◃ By` (Spivak–Niu Example 6.84).

Both sides are `(A × B) y`: a pair of linear moves is the same data as a linear
move followed by a linear move, since each linear factor has a unique
direction. The forward lens is `orderingLens (linear A) (linear B)`. -/
def linearTensorLinear (A : Type u) (B : Type u) :
    (linear.{u, u} A ⊗ linear.{u, u} B) ≃ₗ (linear.{u, u} A ◃ linear.{u, u} B) where
  toLens := orderingLens (linear A) (linear B)
  invLens := (fun ⟨a, f⟩ => (a, f PUnit.unit)) ⇆ fun _ (u, w) => ⟨u, w⟩
  left_inv := rfl
  right_inv := rfl

/-- `y^A ⊗ y^B ≅ y^A ◃ y^B` (Spivak–Niu Example 6.84).

Both sides are `y^(A × B)`: a pair of directions `A × B` is the same as an
`A`-direction followed by a `B`-direction, since each pure-power factor has a
unique position. The forward lens is `orderingLens (purePower A) (purePower B)`. -/
def purePowerTensorPurePower (A : Type u) (B : Type u) :
    (purePower.{u, u} A ⊗ purePower.{u, u} B) ≃ₗ
      (purePower.{u, u} A ◃ purePower.{u, u} B) where
  toLens := orderingLens (purePower A) (purePower B)
  invLens := (fun uf => (uf.1, PUnit.unit)) ⇆ fun _ (x, y) => ⟨x, y⟩
  left_inv := rfl
  right_inv := rfl

/-- `By ⊗ p ≅ By ◃ p` (Spivak–Niu Example 6.84), with the *linear* factor `By`
on the left.

The linear factor `By = linear B` has a unique direction, so pairing a
`B`-labelled move with a `p`-move is the same as taking the `B`-labelled move
first and then continuing with `p`. The forward lens is
`orderingLens (linear B) p`. -/
def linearTensor (B : Type u) (p : PFunctor.{u, u}) :
    (linear.{u, u} B ⊗ p) ≃ₗ (linear.{u, u} B ◃ p) where
  toLens := orderingLens (linear B) p
  invLens := (fun ⟨b, f⟩ => (b, f PUnit.unit)) ⇆ fun _ (u, d) => ⟨u, d⟩
  left_inv := rfl
  right_inv := rfl

/-- `p ⊗ y^A ≅ p ◃ y^A` (Spivak–Niu Example 6.84), with the *pure-power* factor
`y^A` on the right.

The pure-power factor `y^A = purePower A` has a unique position, so a `p`-move
paired with an `A`-direction is the same as a `p`-move followed by an
`A`-direction. The forward lens is `orderingLens p (purePower A)`. -/
def tensorPurePower (p : PFunctor.{u, u}) (A : Type u) :
    (p ⊗ purePower.{u, u} A) ≃ₗ (p ◃ purePower.{u, u} A) where
  toLens := orderingLens p (purePower A)
  invLens := (fun pf => (pf.1, PUnit.unit)) ⇆ fun _ (x, y) => ⟨x, y⟩
  left_inv := rfl
  right_inv := rfl

end Equiv

end Lens
end PFunctor
