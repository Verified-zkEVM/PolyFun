/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Comonoid
public import PolyFun.PFunctor.InternalHom
public import PolyFun.PFunctor.Lens.Duoidal
public import PolyFun.PFunctor.SubstMonoid

/-!
# Convolution substitution monoids

The internal hom from a composition comonoid `C` to a substitution monoid `M`
carries a canonical substitution-monoid structure. Its multiplication copies
the `C`-input with the comultiplication, evaluates the two internal-hom
positions, and combines their outputs with the multiplication of `M`.

This is the convolution monoid `[C, M]` induced by the duoidal interaction
between tensor and polynomial substitution. It is the algebraic construction
used to extend a curried map out of a free substitution monoid in the
Libkind--Spivak pattern-runs-on-matter action.

The comonoid and target monoid may use four independent universes. The
convolution carrier has position universe `max cA cB mA mB` and direction
universe `max cA mB`, exactly the universes of the internal hom `[C, M]`.

## References

* Libkind and Spivak, *Pattern Runs on Matter: The Free Monad Monad as a
  Module over the Cofree Comonad Comonad*.
-/

@[expose] public section

universe cA cB mA mB pA pB qA qB rA rB

namespace PFunctor
namespace SubstMonoid

/-! ## The comonoid action on tensor -/

/-- Unit comparison for the action `p ↦ p ⊗ C`, instantiated at the universe
pair of the convolution carrier. Tensoring with `C` may enlarge the direction
universe from `max cA mB` to `max cA cB mB`. -/
private def actionUnit (C : Comonoid.{cA, cB})
    (_M : SubstMonoid.{mA, mB}) :
    Lens (X.{max cA cB mA mB, max cA mB} ⊗ C.carrier)
      X.{max cA cB mA mB, max cA cB mB} :=
  (fun _ => PUnit.unit) ⇆
    (fun pos _ => (PUnit.unit, C.counit.toFunB pos.2 PUnit.unit))

/-- Binary comparison for the action `p ↦ p ⊗ C`. It copies the
`C`-input and then applies duoidal interchange. -/
private def actionMap (C : Comonoid.{cA, cB})
    (p : PFunctor.{pA, pB}) (q : PFunctor.{qA, qB}) :
    Lens ((p ◃ q) ⊗ C.carrier)
      ((p ⊗ C.carrier) ◃ (q ⊗ C.carrier)) :=
  Lens.duoidalLens p q C.carrier C.carrier ∘ₗ
    (Lens.id (p ◃ q) ⊗ₗ C.comult)

/-- The action comparison is associative. This is exactly the
three-interchange coherence followed by coassociativity of `C`. -/
private theorem action_assoc (C : Comonoid.{cA, cB})
    (p : PFunctor.{pA, pB}) (q : PFunctor.{qA, qB})
    (r : PFunctor.{rA, rB}) :
    Lens.Equiv.compAssoc.toLens ∘ₗ
        (actionMap C p q ◃ₗ Lens.id (r ⊗ C.carrier)) ∘ₗ
        actionMap C (p ◃ q) r =
      (Lens.id (p ⊗ C.carrier) ◃ₗ actionMap C q r) ∘ₗ
        actionMap C p (q ◃ r) ∘ₗ
        (Lens.Equiv.compAssoc.toLens ⊗ₗ Lens.id C.carrier) := by
  change
    (Lens.id (p ⊗ C.carrier) ◃ₗ
        Lens.duoidalLens q r C.carrier C.carrier) ∘ₗ
      Lens.duoidalLens p (q ◃ r) C.carrier
        (C.carrier ◃ C.carrier) ∘ₗ
      (Lens.Equiv.compAssoc.toLens ⊗ₗ
        (Lens.Equiv.compAssoc.toLens ∘ₗ
          (C.comult ◃ₗ Lens.id C.carrier) ∘ₗ C.comult)) =
    (Lens.id (p ⊗ C.carrier) ◃ₗ
        Lens.duoidalLens q r C.carrier C.carrier) ∘ₗ
      Lens.duoidalLens p (q ◃ r) C.carrier
        (C.carrier ◃ C.carrier) ∘ₗ
      (Lens.Equiv.compAssoc.toLens ⊗ₗ
        ((Lens.id C.carrier ◃ₗ C.comult) ∘ₗ C.comult))
  rw [C.coassoc]

/-- The unique lens from the post-action composition unit to the universe
instance required by `M.unit`. It carries no mathematical data; it only
compares two copies of `X`. -/
private def compositionUnitMap (_C : Comonoid.{cA, cB})
    (_M : SubstMonoid.{mA, mB}) :
    Lens X.{max cA cB mA mB, max cA cB mB}
      X.{max mA mB, mB} :=
  Lens.unitComparison

/-! ## Raw convolution operations -/

/-- The uncurried convolution unit. It discards the comonoid input with the
counit and then applies the unit of `M`. Public declarations cannot depend on
the private universe-normalization helpers above, so this body intentionally
copies `compositionUnitMap` and `actionUnit`; the copies must remain
definitionally identical to those helpers. -/
def convolutionUnitRaw (C : Comonoid.{cA, cB})
    (M : SubstMonoid.{mA, mB}) :
    Lens (X.{max cA cB mA mB, max cA mB} ⊗ C.carrier)
      M.carrier :=
  M.unit ∘ₗ
    (show Lens X.{max cA cB mA mB, max cA cB mB}
        X.{max mA mB, mB} from Lens.unitComparison) ∘ₗ
    ((fun _ => PUnit.unit) ⇆
      (fun pos _ => (PUnit.unit, C.counit.toFunB pos.2 PUnit.unit)))

/-- The uncurried convolution multiplication. It copies the `C`-input,
interchanges tensor with substitution, evaluates both internal-hom positions,
and multiplies their `M`-outputs. -/
def convolutionMultRaw (C : Comonoid.{cA, cB})
    (M : SubstMonoid.{mA, mB}) :
    Lens (((ihom C.carrier M.carrier) ◃
      (ihom C.carrier M.carrier)) ⊗ C.carrier) M.carrier :=
  M.mult ∘ₗ
    ((Lens.eval C.carrier M.carrier ◃ₗ
      Lens.eval C.carrier M.carrier) ∘ₗ
      Lens.duoidalLens (ihom C.carrier M.carrier)
        (ihom C.carrier M.carrier) C.carrier C.carrier ∘ₗ
      (Lens.id ((ihom C.carrier M.carrier) ◃
        (ihom C.carrier M.carrier)) ⊗ₗ C.comult))

/-! The following two factorization lemmas isolate the unit-universe
comparison and reduce the action unit laws exactly to the counit laws of `C`.
-/

private theorem unit_left_factor (C : Comonoid.{cA, cB})
    (M : SubstMonoid.{mA, mB}) :
    ((compositionUnitMap C M ∘ₗ actionUnit C M) ◃ₗ
        Lens.eval C.carrier M.carrier) ∘ₗ
        actionMap C X (ihom C.carrier M.carrier) ∘ₗ
        (Lens.Equiv.XComp.invLens ⊗ₗ Lens.id C.carrier) =
      Lens.Equiv.XComp.invLens ∘ₗ
        Lens.eval C.carrier M.carrier := by
  apply Lens.cancel_toLens Lens.Equiv.XComp
  change
    Lens.eval C.carrier M.carrier ∘ₗ
        (Lens.id (ihom C.carrier M.carrier) ⊗ₗ
          (Lens.Equiv.XComp.toLens ∘ₗ
            (C.counit ◃ₗ Lens.id C.carrier) ∘ₗ C.comult)) =
      Lens.eval C.carrier M.carrier
  rw [C.counit_left, Lens.tensorMap_id, Lens.comp_id]

private theorem unit_right_factor (C : Comonoid.{cA, cB})
    (M : SubstMonoid.{mA, mB}) :
    (Lens.eval C.carrier M.carrier ◃ₗ
        (compositionUnitMap C M ∘ₗ actionUnit C M)) ∘ₗ
        actionMap C (ihom C.carrier M.carrier) X ∘ₗ
        (Lens.Equiv.compX.invLens ⊗ₗ Lens.id C.carrier) =
      Lens.Equiv.compX.invLens ∘ₗ
        Lens.eval C.carrier M.carrier := by
  apply Lens.cancel_toLens Lens.Equiv.compX
  change
    Lens.eval C.carrier M.carrier ∘ₗ
        (Lens.id (ihom C.carrier M.carrier) ⊗ₗ
          (Lens.Equiv.compX.toLens ∘ₗ
            (Lens.id C.carrier ◃ₗ C.counit) ∘ₗ C.comult)) =
      Lens.eval C.carrier M.carrier
  rw [C.counit_right, Lens.tensorMap_id, Lens.comp_id]

private theorem convolution_assoc_raw (C : Comonoid.{cA, cB})
    (M : SubstMonoid.{mA, mB}) :
    convolutionMultRaw C M ∘ₗ
        ((Lens.curry (convolutionMultRaw C M) ◃ₗ
          Lens.id (ihom C.carrier M.carrier)) ⊗ₗ Lens.id C.carrier) =
      convolutionMultRaw C M ∘ₗ
        (((Lens.id (ihom C.carrier M.carrier) ◃ₗ
            Lens.curry (convolutionMultRaw C M)) ∘ₗ
          Lens.Equiv.compAssoc.toLens) ⊗ₗ Lens.id C.carrier) := by
  calc
    _ = M.mult ∘ₗ (M.mult ◃ₗ Lens.id M.carrier) ∘ₗ
        ((Lens.eval C.carrier M.carrier ◃ₗ
            Lens.eval C.carrier M.carrier) ◃ₗ
          Lens.eval C.carrier M.carrier) ∘ₗ
        (actionMap C (ihom C.carrier M.carrier)
            (ihom C.carrier M.carrier) ◃ₗ
          Lens.id (ihom C.carrier M.carrier ⊗ C.carrier)) ∘ₗ
        actionMap C
          (ihom C.carrier M.carrier ◃ ihom C.carrier M.carrier)
          (ihom C.carrier M.carrier) := by
      rfl
    _ = (M.mult ∘ₗ (Lens.id M.carrier ◃ₗ M.mult) ∘ₗ
          Lens.Equiv.compAssoc.toLens) ∘ₗ
        ((Lens.eval C.carrier M.carrier ◃ₗ
            Lens.eval C.carrier M.carrier) ◃ₗ
          Lens.eval C.carrier M.carrier) ∘ₗ
        (actionMap C (ihom C.carrier M.carrier)
            (ihom C.carrier M.carrier) ◃ₗ
          Lens.id (ihom C.carrier M.carrier ⊗ C.carrier)) ∘ₗ
        actionMap C
          (ihom C.carrier M.carrier ◃ ihom C.carrier M.carrier)
          (ihom C.carrier M.carrier) := by
      exact congrArg
        (fun l => l ∘ₗ
          ((Lens.eval C.carrier M.carrier ◃ₗ
              Lens.eval C.carrier M.carrier) ◃ₗ
            Lens.eval C.carrier M.carrier) ∘ₗ
          (actionMap C (ihom C.carrier M.carrier)
              (ihom C.carrier M.carrier) ◃ₗ
            Lens.id (ihom C.carrier M.carrier ⊗ C.carrier)) ∘ₗ
          actionMap C
            (ihom C.carrier M.carrier ◃ ihom C.carrier M.carrier)
            (ihom C.carrier M.carrier)) M.assoc
    _ = M.mult ∘ₗ (Lens.id M.carrier ◃ₗ M.mult) ∘ₗ
        (Lens.eval C.carrier M.carrier ◃ₗ
          (Lens.eval C.carrier M.carrier ◃ₗ
            Lens.eval C.carrier M.carrier)) ∘ₗ
        (Lens.Equiv.compAssoc.toLens ∘ₗ
          (actionMap C (ihom C.carrier M.carrier)
              (ihom C.carrier M.carrier) ◃ₗ
            Lens.id (ihom C.carrier M.carrier ⊗ C.carrier)) ∘ₗ
          actionMap C
            (ihom C.carrier M.carrier ◃ ihom C.carrier M.carrier)
            (ihom C.carrier M.carrier)) := by
      rfl
    _ = M.mult ∘ₗ (Lens.id M.carrier ◃ₗ M.mult) ∘ₗ
        (Lens.eval C.carrier M.carrier ◃ₗ
          (Lens.eval C.carrier M.carrier ◃ₗ
            Lens.eval C.carrier M.carrier)) ∘ₗ
        ((Lens.id (ihom C.carrier M.carrier ⊗ C.carrier) ◃ₗ
            actionMap C (ihom C.carrier M.carrier)
              (ihom C.carrier M.carrier)) ∘ₗ
          actionMap C (ihom C.carrier M.carrier)
            (ihom C.carrier M.carrier ◃ ihom C.carrier M.carrier) ∘ₗ
          (Lens.Equiv.compAssoc.toLens ⊗ₗ Lens.id C.carrier)) := by
      rw [action_assoc]
    _ = _ := by
      rfl

/-! ## The convolution monoid -/

/-- The convolution substitution monoid `[C, M]`. -/
def convolution (C : Comonoid.{cA, cB}) (M : SubstMonoid.{mA, mB}) :
    SubstMonoid.{max cA cB mA mB, max cA mB} where
  carrier := ihom C.carrier M.carrier
  unit := Lens.curry (convolutionUnitRaw C M)
  mult := Lens.curry (convolutionMultRaw C M)
  unit_left := by
    apply Lens.curryEquiv.symm.injective
    change
      convolutionMultRaw C M ∘ₗ
          (((Lens.curry (convolutionUnitRaw C M) ◃ₗ
              Lens.id (ihom C.carrier M.carrier)) ∘ₗ
            Lens.Equiv.XComp.invLens) ⊗ₗ Lens.id C.carrier) =
        Lens.eval C.carrier M.carrier
    calc
      _ = M.mult ∘ₗ (M.unit ◃ₗ Lens.id M.carrier) ∘ₗ
          (((compositionUnitMap C M ∘ₗ actionUnit C M) ◃ₗ
              Lens.eval C.carrier M.carrier) ∘ₗ
            actionMap C X (ihom C.carrier M.carrier) ∘ₗ
            (Lens.Equiv.XComp.invLens ⊗ₗ Lens.id C.carrier)) := by
        rfl
      _ = M.mult ∘ₗ (M.unit ◃ₗ Lens.id M.carrier) ∘ₗ
          Lens.Equiv.XComp.invLens ∘ₗ
          Lens.eval C.carrier M.carrier := by
        rw [unit_left_factor]
        rfl
      _ = Lens.eval C.carrier M.carrier := by
        simpa only [Lens.id_comp] using congrArg
          (fun l => l ∘ₗ Lens.eval C.carrier M.carrier) M.unit_left
  unit_right := by
    apply Lens.curryEquiv.symm.injective
    change
      convolutionMultRaw C M ∘ₗ
          (((Lens.id (ihom C.carrier M.carrier) ◃ₗ
              Lens.curry (convolutionUnitRaw C M)) ∘ₗ
            Lens.Equiv.compX.invLens) ⊗ₗ Lens.id C.carrier) =
        Lens.eval C.carrier M.carrier
    calc
      _ = M.mult ∘ₗ (Lens.id M.carrier ◃ₗ M.unit) ∘ₗ
          ((Lens.eval C.carrier M.carrier ◃ₗ
              (compositionUnitMap C M ∘ₗ actionUnit C M)) ∘ₗ
            actionMap C (ihom C.carrier M.carrier) X ∘ₗ
            (Lens.Equiv.compX.invLens ⊗ₗ Lens.id C.carrier)) := by
        rfl
      _ = M.mult ∘ₗ (Lens.id M.carrier ◃ₗ M.unit) ∘ₗ
          Lens.Equiv.compX.invLens ∘ₗ
          Lens.eval C.carrier M.carrier := by
        rw [unit_right_factor]
        rfl
      _ = Lens.eval C.carrier M.carrier := by
        simpa only [Lens.id_comp] using congrArg
          (fun l => l ∘ₗ Lens.eval C.carrier M.carrier) M.unit_right
  assoc := by
    apply Lens.curryEquiv.symm.injective
    change
      convolutionMultRaw C M ∘ₗ
          ((Lens.curry (convolutionMultRaw C M) ◃ₗ
            Lens.id (ihom C.carrier M.carrier)) ⊗ₗ Lens.id C.carrier) =
        convolutionMultRaw C M ∘ₗ
          (((Lens.id (ihom C.carrier M.carrier) ◃ₗ
              Lens.curry (convolutionMultRaw C M)) ∘ₗ
            Lens.Equiv.compAssoc.toLens) ⊗ₗ Lens.id C.carrier)
    exact convolution_assoc_raw C M

@[simp]
theorem convolution_carrier (C : Comonoid.{cA, cB})
    (M : SubstMonoid.{mA, mB}) :
    (convolution C M).carrier = ihom C.carrier M.carrier :=
  rfl

/-- Uncurrying the convolution unit recovers its counit-then-unit semantic
map. -/
theorem uncurry_convolution_unit (C : Comonoid.{cA, cB})
    (M : SubstMonoid.{mA, mB}) :
    Lens.uncurry (convolution C M).unit = convolutionUnitRaw C M :=
  rfl

/-- Uncurrying the convolution multiplication recovers its
copy-interchange-evaluate-multiply semantic map. -/
theorem uncurry_convolution_mult (C : Comonoid.{cA, cB})
    (M : SubstMonoid.{mA, mB}) :
    Lens.uncurry (convolution C M).mult = convolutionMultRaw C M :=
  rfl

end SubstMonoid
end PFunctor
