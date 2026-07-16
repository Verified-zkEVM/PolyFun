/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Duoidal

/-!
# Examples for the duoidal structure relating `⊗` and `◃`

Regression tests: the ordering lens is cartesian on concrete polynomials, the
`⊗`/`◃` catalogue isomorphisms specialize to concrete small polynomials, and
the duoidal interchange and all concrete coherence paths preserve separated
universes and the intended backward-direction order.
-/

@[expose] public section

universe u pA₁ pB₁ pA₂ pB₂ qA₁ qB₁ qA₂ qB₂
  rA₁ rB₁ rA₂ rB₂ sA₁ sB₁ sA₂ sB₂

namespace PFunctor

/-- The ordering lens `p ⊗ q → p ◃ q` is cartesian on concrete polynomials. -/
example : (Lens.orderingLens (linear.{0, 0} Bool) (linear.{0, 0} (Fin 3))).IsCartesian :=
  Lens.orderingLens_isCartesian _ _

/-- The `Ay ⊗ By ≅ Ay ◃ By` catalogue isomorphism on concrete small polynomials. -/
example : (linear.{0, 0} Bool ⊗ linear.{0, 0} (Fin 3)) ≃ₗ
    (linear.{0, 0} Bool ◃ linear.{0, 0} (Fin 3)) :=
  Lens.Equiv.linearTensorLinear Bool (Fin 3)

/-- The `y^A ⊗ y^B ≅ y^A ◃ y^B` catalogue isomorphism on concrete small polynomials. -/
example : (purePower.{0, 0} Bool ⊗ purePower.{0, 0} (Fin 3)) ≃ₗ
    (purePower.{0, 0} Bool ◃ purePower.{0, 0} (Fin 3)) :=
  Lens.Equiv.purePowerTensorPurePower Bool (Fin 3)

/-- The `By ⊗ p ≅ By ◃ p` catalogue isomorphism (linear factor on the left). -/
example : (linear.{0, 0} Bool ⊗ purePower.{0, 0} (Fin 3)) ≃ₗ
    (linear.{0, 0} Bool ◃ purePower.{0, 0} (Fin 3)) :=
  Lens.Equiv.linearTensor Bool (purePower (Fin 3))

/-- The `p ⊗ y^A ≅ p ◃ y^A` catalogue isomorphism (pure-power factor on the right). -/
example : (linear.{0, 0} Bool ⊗ purePower.{0, 0} (Fin 3)) ≃ₗ
    (linear.{0, 0} Bool ◃ purePower.{0, 0} (Fin 3)) :=
  Lens.Equiv.tensorPurePower (linear Bool) (Fin 3)

/-- The duoidal interchange lens typechecks with its stated signature, generically. -/
example (p p' q q' : PFunctor.{u, u}) :
    Lens ((p ◃ p') ⊗ (q ◃ q')) ((p ⊗ q) ◃ (p' ⊗ q')) :=
  Lens.duoidalLens p p' q q'

/-- Ordering is natural in both arguments. -/
example {p p' q q' : PFunctor.{u, u}} (f : Lens p p') (g : Lens q q') :
    Lens.orderingLens p' q' ∘ₗ (f ⊗ₗ g) =
      (f ◃ₗ g) ∘ₗ Lens.orderingLens p q :=
  Lens.orderingLens_natural f g

/-- Interchange is natural in all four arguments. -/
example {p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂ : PFunctor.{u, u}}
    (f₁ : Lens p₁ r₁) (f₂ : Lens p₂ r₂)
    (g₁ : Lens q₁ s₁) (g₂ : Lens q₂ s₂) :
    Lens.duoidalLens r₁ r₂ s₁ s₂ ∘ₗ ((f₁ ◃ₗ f₂) ⊗ₗ (g₁ ◃ₗ g₂)) =
      ((f₁ ⊗ₗ g₁) ◃ₗ (f₂ ⊗ₗ g₂)) ∘ₗ Lens.duoidalLens p₁ p₂ q₁ q₂ :=
  Lens.duoidalLens_natural f₁ f₂ g₁ g₂

/-- Naturality does not identify the universe pairs of any source or target
interface. -/
example {p₁ : PFunctor.{pA₁, pB₁}} {p₂ : PFunctor.{pA₂, pB₂}}
    {q₁ : PFunctor.{qA₁, qB₁}} {q₂ : PFunctor.{qA₂, qB₂}}
    {r₁ : PFunctor.{rA₁, rB₁}} {r₂ : PFunctor.{rA₂, rB₂}}
    {s₁ : PFunctor.{sA₁, sB₁}} {s₂ : PFunctor.{sA₂, sB₂}}
    (f₁ : Lens p₁ r₁) (f₂ : Lens p₂ r₂)
    (g₁ : Lens q₁ s₁) (g₂ : Lens q₂ s₂) :
    Lens.duoidalLens r₁ r₂ s₁ s₂ ∘ₗ ((f₁ ◃ₗ f₂) ⊗ₗ (g₁ ◃ₗ g₂)) =
      ((f₁ ⊗ₗ g₁) ◃ₗ (f₂ ⊗ₗ g₂)) ∘ₗ Lens.duoidalLens p₁ p₂ q₁ q₂ :=
  Lens.duoidalLens_natural f₁ f₂ g₁ g₂

/-- Interchange is cartesian. -/
example (p p' q q' : PFunctor.{u, u}) :
    (Lens.duoidalLens p p' q q').IsCartesian :=
  Lens.duoidalLens_isCartesian p p' q q'

/-- The two unit-comparison maps preserve independent universe pairs. -/
example : Lens X.{pA₁, pB₁} X.{qA₁, qB₁} :=
  Lens.unitComparison

example :
    Lens X.{max pA₁ qA₁ pB₁, max pB₁ qB₁}
      (X.{pA₁, pB₁} ◃ X.{qA₁, qB₁}) :=
  Lens.compUnitMap

/-- The shared unit satisfies its tensor-monoid and composition-comonoid
laws. -/
example :
    (Lens.tensorUnitMap :
        Lens (X.{pA₁, pB₁} ⊗ X.{pA₁, pB₁}) X.{pA₁, pB₁}) ∘ₗ
      ((Lens.unitComparison : Lens X.{pA₁, pB₁} X.{pA₁, pB₁}) ⊗ₗ
        Lens.id X.{pA₁, pB₁}) =
      Lens.Equiv.xTensor.toLens :=
  Lens.tensorUnitMap_unit_left

example :
    (Lens.tensorUnitMap :
        Lens (X.{pA₁, pB₁} ⊗ X.{pA₁, pB₁}) X.{pA₁, pB₁}) ∘ₗ
      (Lens.id X.{pA₁, pB₁} ⊗ₗ
        (Lens.unitComparison : Lens X.{pA₁, pB₁} X.{pA₁, pB₁})) =
      Lens.Equiv.tensorX.toLens :=
  Lens.tensorUnitMap_unit_right

example :
    (Lens.tensorUnitMap :
        Lens (X.{pA₁, pB₁} ⊗ X.{pA₁, pB₁}) X.{pA₁, pB₁}) ∘ₗ
        ((Lens.tensorUnitMap :
          Lens (X.{pA₁, pB₁} ⊗ X.{pA₁, pB₁}) X.{pA₁, pB₁}) ⊗ₗ
          Lens.id X.{pA₁, pB₁}) =
      (Lens.tensorUnitMap :
        Lens (X.{pA₁, pB₁} ⊗ X.{pA₁, pB₁}) X.{pA₁, pB₁}) ∘ₗ
        (Lens.id X.{pA₁, pB₁} ⊗ₗ (Lens.tensorUnitMap :
          Lens (X.{pA₁, pB₁} ⊗ X.{pA₁, pB₁}) X.{pA₁, pB₁})) ∘ₗ
        Lens.Equiv.tensorAssoc.toLens :=
  Lens.tensorUnitMap_assoc

example :
    (Lens.Equiv.XComp (P := X.{pA₁, pB₁})).toLens ∘ₗ
        ((Lens.unitComparison : Lens X.{pA₁, pB₁} X.{pA₁, pB₁}) ◃ₗ
          Lens.id X.{pA₁, pB₁}) ∘ₗ
        (Lens.compUnitMap ∘ₗ
          (Lens.unitComparison :
            Lens X.{pA₁, pB₁} X.{max pA₁ pB₁, pB₁})) =
      Lens.id X.{pA₁, pB₁} :=
  Lens.compUnitMap_counit_left

example :
    (Lens.Equiv.compX (P := X.{pA₁, pB₁})).toLens ∘ₗ
        (Lens.id X.{pA₁, pB₁} ◃ₗ
          (Lens.unitComparison : Lens X.{pA₁, pB₁} X.{pA₁, pB₁})) ∘ₗ
        (Lens.compUnitMap ∘ₗ
          (Lens.unitComparison :
            Lens X.{pA₁, pB₁} X.{max pA₁ pB₁, pB₁})) =
      Lens.id X.{pA₁, pB₁} :=
  Lens.compUnitMap_counit_right

example :
    (Lens.Equiv.compAssoc (P := X.{pA₁, pB₁})
      (Q := X.{pA₁, pB₁}) (R := X.{pA₁, pB₁})).toLens ∘ₗ
        ((Lens.compUnitMap ∘ₗ
          (Lens.unitComparison :
            Lens X.{pA₁, pB₁} X.{max pA₁ pB₁, pB₁})) ◃ₗ
          Lens.id X.{pA₁, pB₁}) ∘ₗ
        (Lens.compUnitMap ∘ₗ
          (Lens.unitComparison :
            Lens X.{pA₁, pB₁} X.{max pA₁ pB₁, pB₁})) =
      (Lens.id X.{pA₁, pB₁} ◃ₗ
        (Lens.compUnitMap ∘ₗ
          (Lens.unitComparison :
            Lens X.{pA₁, pB₁} X.{max pA₁ pB₁, pB₁}))) ∘ₗ
        (Lens.compUnitMap ∘ₗ
          (Lens.unitComparison :
            Lens X.{pA₁, pB₁} X.{max pA₁ pB₁, pB₁})) :=
  Lens.compUnitMap_coassoc

/-- The internal interchange unit laws preserve independent universe pairs. -/
example (p : PFunctor.{pA₁, pB₁}) (q : PFunctor.{qA₁, qB₁}) :
    Lens.Equiv.XComp.toLens ∘ₗ
        (Lens.tensorUnitMap ◃ₗ Lens.id (p ⊗ q)) ∘ₗ
        Lens.duoidalLens X p X q =
      (Lens.Equiv.XComp.toLens ⊗ₗ Lens.Equiv.XComp.toLens) :=
  Lens.duoidalLens_comp_unit_left p q

example (p : PFunctor.{pA₁, pB₁}) (q : PFunctor.{qA₁, qB₁}) :
    Lens.Equiv.compX.toLens ∘ₗ
        (Lens.id (p ⊗ q) ◃ₗ Lens.tensorUnitMap) ∘ₗ
        Lens.duoidalLens p X q X =
      (Lens.Equiv.compX.toLens ⊗ₗ Lens.Equiv.compX.toLens) :=
  Lens.duoidalLens_comp_unit_right p q

/-- Three-interchange associativity keeps all six polynomial universe pairs
independent. -/
example (p₁ : PFunctor.{pA₁, pB₁}) (p₂ : PFunctor.{pA₂, pB₂})
    (p₃ : PFunctor.{qA₁, qB₁}) (q₁ : PFunctor.{qA₂, qB₂})
    (q₂ : PFunctor.{rA₁, rB₁}) (q₃ : PFunctor.{rA₂, rB₂}) :
    (Lens.id (p₁ ⊗ q₁) ◃ₗ Lens.duoidalLens p₂ p₃ q₂ q₃) ∘ₗ
        Lens.duoidalLens p₁ (p₂ ◃ p₃) q₁ (q₂ ◃ q₃) ∘ₗ
        (Lens.Equiv.compAssoc.toLens ⊗ₗ Lens.Equiv.compAssoc.toLens) =
      Lens.Equiv.compAssoc.toLens ∘ₗ
        (Lens.duoidalLens p₁ p₂ q₁ q₂ ◃ₗ
          Lens.id (p₃ ⊗ q₃)) ∘ₗ
        Lens.duoidalLens (p₁ ◃ p₂) p₃ (q₁ ◃ q₂) q₃ :=
  Lens.duoidalLens_comp_assoc p₁ p₂ p₃ q₁ q₂ q₃

/-- External tensor associativity also retains six independent universe
pairs. -/
example (p₁ : PFunctor.{pA₁, pB₁}) (p₂ : PFunctor.{pA₂, pB₂})
    (q₁ : PFunctor.{qA₁, qB₁}) (q₂ : PFunctor.{qA₂, qB₂})
    (r₁ : PFunctor.{rA₁, rB₁}) (r₂ : PFunctor.{rA₂, rB₂}) :
    Lens.duoidalLens p₁ p₂ (q₁ ⊗ r₁) (q₂ ⊗ r₂) ∘ₗ
        (Lens.id (p₁ ◃ p₂) ⊗ₗ Lens.duoidalLens q₁ q₂ r₁ r₂) ∘ₗ
        Lens.Equiv.tensorAssoc.toLens =
      (Lens.Equiv.tensorAssoc.toLens ◃ₗ
        Lens.Equiv.tensorAssoc.toLens) ∘ₗ
        Lens.duoidalLens (p₁ ⊗ q₁) (p₂ ⊗ q₂) r₁ r₂ ∘ₗ
        (Lens.duoidalLens p₁ p₂ q₁ q₂ ⊗ₗ
          Lens.id (r₁ ◃ r₂)) :=
  Lens.duoidalLens_tensor_assoc p₁ p₂ q₁ q₂ r₁ r₂

/-- The external tensor-unit laws preserve independent universe pairs. -/
example (p : PFunctor.{pA₁, pB₁}) (q : PFunctor.{qA₁, qB₁}) :
    (Lens.Equiv.xTensor.toLens ◃ₗ Lens.Equiv.xTensor.toLens) ∘ₗ
        Lens.duoidalLens X X p q ∘ₗ
        (Lens.compUnitMap ⊗ₗ Lens.id (p ◃ q)) =
      Lens.Equiv.xTensor.toLens :=
  Lens.duoidalLens_tensor_unit_left p q

example (p : PFunctor.{pA₁, pB₁}) (q : PFunctor.{qA₁, qB₁}) :
    (Lens.Equiv.tensorX.toLens ◃ₗ Lens.Equiv.tensorX.toLens) ∘ₗ
        Lens.duoidalLens p q X X ∘ₗ
        (Lens.id (p ◃ q) ⊗ₗ Lens.compUnitMap) =
      Lens.Equiv.tensorX.toLens :=
  Lens.duoidalLens_tensor_unit_right p q

/-! ## Observable coherence paths -/

/-- The left-hand path of composition-associativity coherence on six
distinguishable direction types. -/
def compAssocLeft :
    Lens
      (((purePower Bool ◃ purePower (Fin 3)) ◃ purePower String) ⊗
        ((purePower (Fin 4) ◃ purePower Nat) ◃ purePower Char))
      ((purePower Bool ⊗ purePower (Fin 4)) ◃
        ((purePower (Fin 3) ⊗ purePower Nat) ◃
          (purePower String ⊗ purePower Char))) :=
  (Lens.id (purePower Bool ⊗ purePower (Fin 4)) ◃ₗ
      Lens.duoidalLens (purePower (Fin 3)) (purePower String)
        (purePower Nat) (purePower Char)) ∘ₗ
    Lens.duoidalLens (purePower Bool)
      (purePower (Fin 3) ◃ purePower String)
      (purePower (Fin 4)) (purePower Nat ◃ purePower Char) ∘ₗ
    (Lens.Equiv.compAssoc.toLens ⊗ₗ Lens.Equiv.compAssoc.toLens)

/-- The right-hand path of composition-associativity coherence. -/
def compAssocRight :
    Lens
      (((purePower Bool ◃ purePower (Fin 3)) ◃ purePower String) ⊗
        ((purePower (Fin 4) ◃ purePower Nat) ◃ purePower Char))
      ((purePower Bool ⊗ purePower (Fin 4)) ◃
        ((purePower (Fin 3) ⊗ purePower Nat) ◃
          (purePower String ⊗ purePower Char))) :=
  Lens.Equiv.compAssoc.toLens ∘ₗ
    (Lens.duoidalLens (purePower Bool) (purePower (Fin 3))
        (purePower (Fin 4)) (purePower Nat) ◃ₗ
      Lens.id (purePower String ⊗ purePower Char)) ∘ₗ
    Lens.duoidalLens (purePower Bool ◃ purePower (Fin 3))
      (purePower String) (purePower (Fin 4) ◃ purePower Nat)
      (purePower Char)

/-- Both composition-associativity paths preserve each protocol's three-phase
direction order. -/
example :
    compAssocLeft.toFunB
      (⟨⟨PUnit.unit, fun _ => PUnit.unit⟩, fun _ => PUnit.unit⟩,
        ⟨⟨PUnit.unit, fun _ => PUnit.unit⟩, fun _ => PUnit.unit⟩)
      ⟨(true, (3 : Fin 4)),
        ⟨((2 : Fin 3), (7 : Nat)), ("third", 'z')⟩⟩ =
      (⟨⟨true, (2 : Fin 3)⟩, "third"⟩,
        ⟨⟨(3 : Fin 4), (7 : Nat)⟩, 'z'⟩) :=
  rfl

example :
    compAssocRight.toFunB
      (⟨⟨PUnit.unit, fun _ => PUnit.unit⟩, fun _ => PUnit.unit⟩,
        ⟨⟨PUnit.unit, fun _ => PUnit.unit⟩, fun _ => PUnit.unit⟩)
      ⟨(true, (3 : Fin 4)),
        ⟨((2 : Fin 3), (7 : Nat)), ("third", 'z')⟩⟩ =
      (⟨⟨true, (2 : Fin 3)⟩, "third"⟩,
        ⟨⟨(3 : Fin 4), (7 : Nat)⟩, 'z'⟩) :=
  rfl

/-- The left-hand path of tensor-associativity coherence. -/
def tensorAssocLeft :
    Lens
      (((purePower Bool ◃ purePower (Fin 3)) ⊗
          (purePower String ◃ purePower Nat)) ⊗
        (purePower (Fin 4) ◃ purePower Char))
      ((purePower Bool ⊗ (purePower String ⊗ purePower (Fin 4))) ◃
        (purePower (Fin 3) ⊗ (purePower Nat ⊗ purePower Char))) :=
  Lens.duoidalLens (purePower Bool) (purePower (Fin 3))
      (purePower String ⊗ purePower (Fin 4))
      (purePower Nat ⊗ purePower Char) ∘ₗ
    (Lens.id (purePower Bool ◃ purePower (Fin 3)) ⊗ₗ
      Lens.duoidalLens (purePower String) (purePower Nat)
        (purePower (Fin 4)) (purePower Char)) ∘ₗ
    Lens.Equiv.tensorAssoc.toLens

/-- The right-hand path of tensor-associativity coherence. -/
def tensorAssocRight :
    Lens
      (((purePower Bool ◃ purePower (Fin 3)) ⊗
          (purePower String ◃ purePower Nat)) ⊗
        (purePower (Fin 4) ◃ purePower Char))
      ((purePower Bool ⊗ (purePower String ⊗ purePower (Fin 4))) ◃
        (purePower (Fin 3) ⊗ (purePower Nat ⊗ purePower Char))) :=
  (Lens.Equiv.tensorAssoc.toLens ◃ₗ Lens.Equiv.tensorAssoc.toLens) ∘ₗ
    Lens.duoidalLens
      (purePower Bool ⊗ purePower String)
      (purePower (Fin 3) ⊗ purePower Nat)
      (purePower (Fin 4)) (purePower Char) ∘ₗ
    (Lens.duoidalLens (purePower Bool) (purePower (Fin 3))
      (purePower String) (purePower Nat) ⊗ₗ
      Lens.id (purePower (Fin 4) ◃ purePower Char))

/-- Both tensor-associativity paths preserve outer/inner pairing across all
three parallel protocols. -/
example :
    tensorAssocLeft.toFunB
      ((⟨PUnit.unit, fun _ => PUnit.unit⟩,
        ⟨PUnit.unit, fun _ => PUnit.unit⟩),
        ⟨PUnit.unit, fun _ => PUnit.unit⟩)
      ⟨(true, ("second", (3 : Fin 4))),
        ((2 : Fin 3), ((7 : Nat), 'z'))⟩ =
      ((⟨true, (2 : Fin 3)⟩, ⟨"second", (7 : Nat)⟩),
        ⟨(3 : Fin 4), 'z'⟩) :=
  rfl

example :
    tensorAssocRight.toFunB
      ((⟨PUnit.unit, fun _ => PUnit.unit⟩,
        ⟨PUnit.unit, fun _ => PUnit.unit⟩),
        ⟨PUnit.unit, fun _ => PUnit.unit⟩)
      ⟨(true, ("second", (3 : Fin 4))),
        ((2 : Fin 3), ((7 : Nat), 'z'))⟩ =
      ((⟨true, (2 : Fin 3)⟩, ⟨"second", (7 : Nat)⟩),
        ⟨(3 : Fin 4), 'z'⟩) :=
  rfl

/-- The external left-unit path preserves the nontrivial composite direction. -/
example :
    ((Lens.Equiv.xTensor.toLens ◃ₗ Lens.Equiv.xTensor.toLens) ∘ₗ
      Lens.duoidalLens X X (purePower Bool) (purePower String) ∘ₗ
      (Lens.compUnitMap ⊗ₗ
        Lens.id (purePower Bool ◃ purePower String))).toFunB
      (PUnit.unit, ⟨PUnit.unit, fun _ => PUnit.unit⟩)
      ⟨true, "inner"⟩ =
      (PUnit.unit, ⟨true, "inner"⟩) :=
  rfl

/-- The external right-unit path preserves the nontrivial composite direction. -/
example :
    ((Lens.Equiv.tensorX.toLens ◃ₗ Lens.Equiv.tensorX.toLens) ∘ₗ
      Lens.duoidalLens (purePower Bool) (purePower String) X X ∘ₗ
      (Lens.id (purePower Bool ◃ purePower String) ⊗ₗ
        Lens.compUnitMap)).toFunB
      (⟨PUnit.unit, fun _ => PUnit.unit⟩, PUnit.unit)
      ⟨true, "inner"⟩ =
      (⟨true, "inner"⟩, PUnit.unit) :=
  rfl

/-- The backward map preserves each protocol's outer-before-inner order; it
does not cross the inner directions between the two parallel protocols. -/
example :
    (Lens.duoidalLens
      (purePower.{0, 0} Bool) (purePower.{0, 0} (Fin 3))
      (purePower.{0, 0} String) (purePower.{0, 0} Nat)).toFunB
        (⟨PUnit.unit, fun _ => PUnit.unit⟩,
          ⟨PUnit.unit, fun _ => PUnit.unit⟩)
        ⟨(true, "right"), ((2 : Fin 3), (7 : Nat))⟩ =
      (⟨true, (2 : Fin 3)⟩, ⟨"right", (7 : Nat)⟩) :=
  rfl

/-- The concrete middle-four equation is the binary lax-monoidal law. -/
example (p p' q q' : PFunctor.{u, u}) :
    Lens.duoidalLens p p' q q' ∘ₗ
        (Lens.orderingLens p p' ⊗ₗ Lens.orderingLens q q') =
      Lens.orderingLens (p ⊗ q) (p' ⊗ q') ∘ₗ
        (Lens.Equiv.tensorMiddleFour p p' q q').toLens :=
  Lens.orderingLens_duoidal p p' q q'

/-- Ordering agrees with both tensor/composition unitors. -/
example (p : PFunctor.{u, u}) :
    Lens.Equiv.compX.toLens ∘ₗ Lens.orderingLens p X = Lens.Equiv.tensorX.toLens :=
  Lens.orderingLens_unit_right p

example (p : PFunctor.{u, u}) :
    Lens.Equiv.XComp.toLens ∘ₗ Lens.orderingLens X p = Lens.Equiv.xTensor.toLens :=
  Lens.orderingLens_unit_left p

/-- The duoidal interchange lens typechecks on concrete small polynomials. -/
example :
    Lens ((linear.{0, 0} Bool ◃ linear.{0, 0} (Fin 2)) ⊗
          (linear.{0, 0} (Fin 3) ◃ linear.{0, 0} (Fin 4)))
      ((linear.{0, 0} Bool ⊗ linear.{0, 0} (Fin 3)) ◃
        (linear.{0, 0} (Fin 2) ⊗ linear.{0, 0} (Fin 4))) :=
  Lens.duoidalLens (linear Bool) (linear (Fin 2)) (linear (Fin 3)) (linear (Fin 4))

end PFunctor
