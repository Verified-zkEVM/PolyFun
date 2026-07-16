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

The remaining boundary is abstract duoidal-category packaging. Naturality,
middle-four compatibility, the internal and external interchange-unit
diagrams, both interchange-associativity diagrams, and the shared unit-object
laws are proved below.
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

The concrete naturality, middle-four, cartesianness, unit coherence, and both
interchange-associativity laws used by the current API are formalized below.
Abstract duoidal-category packaging remains deliberately absent. -/
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

/-! ## Unit and associativity coherence -/

/-- The unique comparison between two possibly differently instantiated
copies of the common tensor/composition unit `X`. -/
def unitComparison : Lens X.{uA₁, uB₁} X.{uA₂, uB₂} :=
  Lens.fromX PUnit.unit

/-- The canonical comparison from the tensor of two possibly differently
instantiated composition units to the unit at their componentwise maximum
universes.  Unlike `Equiv.tensorX`, this lens does not require the two copies
of `X` to use the same universe pair. -/
def tensorUnitMap :
    Lens (X.{uA₁, uB₁} ⊗ X.{uA₂, uB₂})
      X.{max uA₁ uA₂, max uB₁ uB₂} :=
  (fun _ => PUnit.unit) ⇆ (fun _ _ => (PUnit.unit, PUnit.unit))

/-- The canonical comparison from the composition unit at the target
universe pair into a composite of two independently instantiated units. -/
def compUnitMap :
    Lens X.{max uA₁ uA₂ uB₁, max uB₁ uB₂}
      (X.{uA₁, uB₁} ◃ X.{uA₂, uB₂}) :=
  (fun _ => ⟨PUnit.unit, fun _ => PUnit.unit⟩) ⇆
    (fun _ _ => PUnit.unit)

/-! ### The shared unit object -/

/-- Left unitality of the tensor-unit multiplication. -/
theorem tensorUnitMap_unit_left :
    (tensorUnitMap :
        Lens (X.{uA, uB} ⊗ X.{uA, uB}) X.{uA, uB}) ∘ₗ
      ((unitComparison : Lens X.{uA, uB} X.{uA, uB}) ⊗ₗ
        Lens.id X.{uA, uB}) =
      Equiv.xTensor.toLens := by
  rfl

/-- Right unitality of the tensor-unit multiplication. -/
theorem tensorUnitMap_unit_right :
    (tensorUnitMap :
        Lens (X.{uA, uB} ⊗ X.{uA, uB}) X.{uA, uB}) ∘ₗ
      (Lens.id X.{uA, uB} ⊗ₗ
        (unitComparison : Lens X.{uA, uB} X.{uA, uB})) =
      Equiv.tensorX.toLens := by
  rfl

/-- Associativity of the tensor-unit multiplication. -/
theorem tensorUnitMap_assoc :
    (tensorUnitMap :
        Lens (X.{uA, uB} ⊗ X.{uA, uB}) X.{uA, uB}) ∘ₗ
        ((tensorUnitMap :
          Lens (X.{uA, uB} ⊗ X.{uA, uB}) X.{uA, uB}) ⊗ₗ
          Lens.id X.{uA, uB}) =
      (tensorUnitMap :
        Lens (X.{uA, uB} ⊗ X.{uA, uB}) X.{uA, uB}) ∘ₗ
        (Lens.id X.{uA, uB} ⊗ₗ (tensorUnitMap :
          Lens (X.{uA, uB} ⊗ X.{uA, uB}) X.{uA, uB})) ∘ₗ
        Equiv.tensorAssoc.toLens := by
  rfl

/-- Left counitality of the composition-unit comultiplication. -/
theorem compUnitMap_counit_left :
    (Equiv.XComp (P := X.{uA, uB})).toLens ∘ₗ
        ((unitComparison : Lens X.{uA, uB} X.{uA, uB}) ◃ₗ
          Lens.id X.{uA, uB}) ∘ₗ
        (compUnitMap ∘ₗ
          (unitComparison :
            Lens X.{uA, uB} X.{max uA uB, uB})) =
      Lens.id X.{uA, uB} := by
  rfl

/-- Right counitality of the composition-unit comultiplication. -/
theorem compUnitMap_counit_right :
    (Equiv.compX (P := X.{uA, uB})).toLens ∘ₗ
        (Lens.id X.{uA, uB} ◃ₗ
          (unitComparison : Lens X.{uA, uB} X.{uA, uB})) ∘ₗ
        (compUnitMap ∘ₗ
          (unitComparison :
            Lens X.{uA, uB} X.{max uA uB, uB})) =
      Lens.id X.{uA, uB} := by
  rfl

/-- Coassociativity of the composition-unit comultiplication. -/
theorem compUnitMap_coassoc :
    (Equiv.compAssoc (P := X.{uA, uB})
      (Q := X.{uA, uB}) (R := X.{uA, uB})).toLens ∘ₗ
        ((compUnitMap ∘ₗ
          (unitComparison :
            Lens X.{uA, uB} X.{max uA uB, uB})) ◃ₗ
          Lens.id X.{uA, uB}) ∘ₗ
        (compUnitMap ∘ₗ
          (unitComparison :
            Lens X.{uA, uB} X.{max uA uB, uB})) =
      (Lens.id X.{uA, uB} ◃ₗ
        (compUnitMap ∘ₗ
          (unitComparison :
            Lens X.{uA, uB} X.{max uA uB, uB}))) ∘ₗ
        (compUnitMap ∘ₗ
          (unitComparison :
            Lens X.{uA, uB} X.{max uA uB, uB})) := by
  rfl

/-- Left-composition-unit coherence for duoidal interchange. Interchanging a pair of
left-unital composites and then combining their two unit components agrees
with applying the two composition left unitors in parallel. -/
theorem duoidalLens_comp_unit_left
    (p : PFunctor.{uA₁, uB₁}) (q : PFunctor.{uA₂, uB₂}) :
    Equiv.XComp.toLens ∘ₗ
        (tensorUnitMap ◃ₗ Lens.id (p ⊗ q)) ∘ₗ
        duoidalLens X p X q =
      (Equiv.XComp.toLens ⊗ₗ Equiv.XComp.toLens) := by
  rfl

/-- Right-composition-unit coherence for duoidal interchange. Interchanging a pair of
right-unital composites and then combining their two unit components agrees
with applying the two composition right unitors in parallel. -/
theorem duoidalLens_comp_unit_right
    (p : PFunctor.{uA₁, uB₁}) (q : PFunctor.{uA₂, uB₂}) :
    Equiv.compX.toLens ∘ₗ
        (Lens.id (p ⊗ q) ◃ₗ tensorUnitMap) ∘ₗ
        duoidalLens p X q X =
      (Equiv.compX.toLens ⊗ₗ Equiv.compX.toLens) := by
  rfl

/-- Composition-associativity coherence for three interchanges. Regrouping each of two
three-phase composites before interchanging gives the same ordered three
parallel phases as interchanging the outer grouping first. -/
theorem duoidalLens_comp_assoc
    (p₁ : PFunctor.{uA₁, uB₁}) (p₂ : PFunctor.{uA₂, uB₂})
    (p₃ : PFunctor.{uA₃, uB₃}) (q₁ : PFunctor.{uA₄, uB₄})
    (q₂ : PFunctor.{uA₅, uB₅}) (q₃ : PFunctor.{uA₆, uB₆}) :
    (Lens.id (p₁ ⊗ q₁) ◃ₗ duoidalLens p₂ p₃ q₂ q₃) ∘ₗ
        duoidalLens p₁ (p₂ ◃ p₃) q₁ (q₂ ◃ q₃) ∘ₗ
        (Equiv.compAssoc.toLens ⊗ₗ Equiv.compAssoc.toLens) =
      Equiv.compAssoc.toLens ∘ₗ
        (duoidalLens p₁ p₂ q₁ q₂ ◃ₗ
          Lens.id (p₃ ⊗ q₃)) ∘ₗ
        duoidalLens (p₁ ◃ p₂) p₃ (q₁ ◃ q₂) q₃ := by
  rfl

/-- Tensor-associativity coherence for three interchanges. Interchanging the
left pair of three parallel composites first agrees with interchanging the
right pair first, after applying the tensor associators. -/
theorem duoidalLens_tensor_assoc
    (p₁ : PFunctor.{uA₁, uB₁}) (p₂ : PFunctor.{uA₂, uB₂})
    (q₁ : PFunctor.{uA₃, uB₃}) (q₂ : PFunctor.{uA₄, uB₄})
    (r₁ : PFunctor.{uA₅, uB₅}) (r₂ : PFunctor.{uA₆, uB₆}) :
    duoidalLens p₁ p₂ (q₁ ⊗ r₁) (q₂ ⊗ r₂) ∘ₗ
        (Lens.id (p₁ ◃ p₂) ⊗ₗ duoidalLens q₁ q₂ r₁ r₂) ∘ₗ
        Equiv.tensorAssoc.toLens =
      (Equiv.tensorAssoc.toLens ◃ₗ Equiv.tensorAssoc.toLens) ∘ₗ
        duoidalLens (p₁ ⊗ q₁) (p₂ ⊗ q₂) r₁ r₂ ∘ₗ
        (duoidalLens p₁ p₂ q₁ q₂ ⊗ₗ Lens.id (r₁ ◃ r₂)) := by
  rfl

/-- Left-tensor-unit coherence for duoidal interchange. -/
theorem duoidalLens_tensor_unit_left
    (p : PFunctor.{uA₁, uB₁}) (q : PFunctor.{uA₂, uB₂}) :
    (Equiv.xTensor.toLens ◃ₗ Equiv.xTensor.toLens) ∘ₗ
        duoidalLens X X p q ∘ₗ
        (compUnitMap ⊗ₗ Lens.id (p ◃ q)) =
      Equiv.xTensor.toLens := by
  rfl

/-- Right-tensor-unit coherence for duoidal interchange. -/
theorem duoidalLens_tensor_unit_right
    (p : PFunctor.{uA₁, uB₁}) (q : PFunctor.{uA₂, uB₂}) :
    (Equiv.tensorX.toLens ◃ₗ Equiv.tensorX.toLens) ∘ₗ
        duoidalLens p q X X ∘ₗ
        (Lens.id (p ◃ q) ⊗ₗ compUnitMap) =
      Equiv.tensorX.toLens := by
  rfl

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
