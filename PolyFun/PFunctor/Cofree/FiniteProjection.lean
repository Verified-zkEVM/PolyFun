/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.Universal

/-!
# Finite projections of the cofree polynomial comonoid

For a polynomial `P`, the cofree polynomial `CofreeP P` stores an infinite
`P`-tree as its position and a finite vertex as its direction.  The lens
`CofreeP.projectionN P n` truncates this data to the first `n` layers, with
codomain the right-nested composition power `compNth P n`.

The definition is structural and remains polymorphic in the two universes of
`P`.  At the current homogeneous `Comonoid.Hom` boundary it agrees with the
abstract composite of iterated comultiplication and the iterated cogenerator.
This gives the general finite-run equation of Spivak--Niu Proposition 8.49.

The additive splitting equation for arbitrary pairs of depths is deliberately
not stated here: with right-nested composition powers it first requires an
explicit reassociation equivalence between `compNth P (l + m)` and
`compNth P l ◃ compNth P m`.
-/

@[expose] public section

universe uA uB u

namespace PFunctor
namespace CofreeP

/-! ## Structural finite projections -/

/-- The depth-`n` finite projection of a cofree polynomial tree.

At depth zero it keeps only the composition unit and pulls its unique
direction back to the root.  At a successor depth it exposes the root layer
and recursively projects each child subtree.  Consequently every composite
direction pulls back to a vertex of exactly depth `n`. -/
def projectionN (P : PFunctor.{uA, uB}) : (n : ℕ) →
    Lens (CofreeP P) (compNth P n)
  | 0 =>
      { toFunA := fun _ => PUnit.unit
        toFunB := fun tree _ => .root tree }
  | n + 1 =>
      (cogenerator P ◃ₗ projectionN P n) ∘ₗ comult

@[simp]
theorem projectionN_zero_toFunA (P : PFunctor.{uA, uB}) (tree : M P) :
    (projectionN P 0).toFunA tree = PUnit.unit :=
  rfl

@[simp]
theorem projectionN_zero_toFunB (P : PFunctor.{uA, uB}) (tree : M P)
    (direction : (compNth P 0).B ((projectionN P 0).toFunA tree)) :
    (projectionN P 0).toFunB tree direction = .root tree :=
  rfl

@[simp]
theorem projectionN_succ_toFunA (P : PFunctor.{uA, uB}) (n : ℕ)
    (tree : M P) :
    (projectionN P (n + 1)).toFunA tree =
      ⟨M.head tree, fun direction =>
        (projectionN P n).toFunA (M.children tree direction)⟩ :=
  rfl

@[simp]
theorem projectionN_succ_toFunB (P : PFunctor.{uA, uB}) (n : ℕ)
    (tree : M P)
    (direction :
      (compNth P (n + 1)).B ((projectionN P (n + 1)).toFunA tree)) :
    (projectionN P (n + 1)).toFunB tree direction =
      .child direction.1
        ((projectionN P n).toFunB
          (M.children tree direction.1) direction.2) :=
  rfl

/-- Pulling a depth-`n` composite direction back through `projectionN`
selects a cofree vertex at exactly depth `n`. -/
theorem depth_projectionN_toFunB (P : PFunctor.{uA, uB}) :
    (n : ℕ) → (tree : M P) →
      (direction :
        (compNth P n).B ((projectionN P n).toFunA tree)) →
      M.Vertex.depth ((projectionN P n).toFunB tree direction) = n
  | 0, tree, direction => by
      simp only [projectionN_zero_toFunB, M.Vertex.depth_root]
  | n + 1, tree, direction => by
      simp only [projectionN_succ_toFunB, M.Vertex.depth_child,
        depth_projectionN_toFunB P n]

/-! ## Low-depth coherence -/

/-- In the homogeneous universe boundary, the zero-stage projection is the
cofree counit. -/
@[simp]
theorem projectionN_zero (P : PFunctor.{u, u}) :
    projectionN P 0 = counit :=
  rfl

/-- The first finite projection is the cogenerator after removing the
right-hand composition unit.  The unitor is necessary because
`compNth P 1 = P ◃ X`, not `P`. -/
theorem projectionN_one_comp_compX (P : PFunctor.{uA, uB}) :
    Lens.Equiv.compX.toLens ∘ₗ projectionN P 1 = cogenerator P := by
  rfl

/-- The second finite projection agrees with one comultiplication followed by
the cogenerator on both components, after removing the innermost right unit. -/
theorem projectionN_two_comp_compX (P : PFunctor.{uA, uB}) :
    (Lens.id P ◃ₗ Lens.Equiv.compX.toLens) ∘ₗ projectionN P 2 =
      (cogenerator P ◃ₗ cogenerator P) ∘ₗ comult := by
  rfl

/-! ## Algebraic characterization and Proposition 8.49 -/

/-- At the homogeneous universe boundary, structural finite projection is
iterated comultiplication followed by the iterated cogenerator. -/
theorem projectionN_eq_comultN_compNthMap
    (P : PFunctor.{u, u}) (n : ℕ) :
    projectionN P n =
      (cogenerator P).compNthMap n ∘ₗ (comonoid P).comultN n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [projectionN, Comonoid.comultN_succ, Lens.compNthMap_succ, ih]
      have hmap :
          cogenerator P ◃ₗ
              ((cogenerator P).compNthMap n ∘ₗ
                (comonoid P).comultN n) =
            (cogenerator P ◃ₗ (cogenerator P).compNthMap n) ∘ₗ
              (Lens.id (CofreeP P) ◃ₗ (comonoid P).comultN n) := by
        change
          ((cogenerator P ∘ₗ Lens.id (CofreeP P)) ◃ₗ
              ((cogenerator P).compNthMap n ∘ₗ
                (comonoid P).comultN n)) = _
        exact Lens.compMap_comp
          (Lens.id (CofreeP P)) ((comonoid P).comultN n)
          (cogenerator P) ((cogenerator P).compNthMap n)
      have houter := congrArg (fun lens => lens ∘ₗ comult) hmap
      have hassoc := Lens.comp_assoc
        (cogenerator P ◃ₗ (cogenerator P).compNthMap n)
        (Lens.id (CofreeP P) ◃ₗ (comonoid P).comultN n)
        comult
      have houter' :
          (cogenerator P ◃ₗ
              ((cogenerator P).compNthMap n ∘ₗ
                (comonoid P).comultN n)) ∘ₗ comult =
            ((cogenerator P ◃ₗ
                (cogenerator P).compNthMap n) ∘ₗ
              (Lens.id (CofreeP P) ◃ₗ
                (comonoid P).comultN n)) ∘ₗ comult := by
        simpa only [comonoid_carrier, comonoid_comult] using houter
      have hassoc' :
          ((cogenerator P ◃ₗ
              (cogenerator P).compNthMap n) ∘ₗ
            (Lens.id (CofreeP P) ◃ₗ
              (comonoid P).comultN n)) ∘ₗ comult =
            (cogenerator P ◃ₗ
              (cogenerator P).compNthMap n) ∘ₗ
              ((Lens.id (CofreeP P) ◃ₗ
                (comonoid P).comultN n) ∘ₗ comult) := by
        simpa only [comonoid_carrier, comonoid_comult] using hassoc
      exact houter'.trans hassoc'

/-- A retrofunctor into the cofree comonoid commutes with every finite
projection.  This is the structural form of the finite-run equation, with the
one-layer restriction of the retrofunctor on the right. -/
theorem hom_comp_projectionN
    {P : PFunctor.{u, u}} {C : Comonoid.{u, u}}
    (hom : Comonoid.Hom C (comonoid P)) (n : ℕ) :
    projectionN P n ∘ₗ hom.toLens =
      (restrict C hom).compNthMap n ∘ₗ C.comultN n := by
  rw [projectionN_eq_comultN_compNthMap]
  change ((cogenerator P).compNthMap n ∘ₗ
      (comonoid P).comultN n) ∘ₗ hom.toLens = _
  calc
    _ = (cogenerator P).compNthMap n ∘ₗ
          ((comonoid P).comultN n ∘ₗ hom.toLens) :=
      Lens.comp_assoc _ _ _
    _ = (cogenerator P).compNthMap n ∘ₗ
          (hom.toLens.compNthMap n ∘ₗ C.comultN n) := by
      simpa only [comonoid_carrier] using
        congrArg (fun lens => (cogenerator P).compNthMap n ∘ₗ lens)
          (hom.map_comultN n)
    _ = ((cogenerator P).compNthMap n ∘ₗ
          hom.toLens.compNthMap n) ∘ₗ C.comultN n :=
      (Lens.comp_assoc _ _ _).symm
    _ = (cogenerator P ∘ₗ hom.toLens).compNthMap n ∘ₗ
          C.comultN n := by
      exact congrArg (fun lens => lens ∘ₗ C.comultN n)
        (Lens.compNthMap_comp (cogenerator P) hom.toLens n).symm
    _ = _ := rfl

/-- **Spivak--Niu Proposition 8.49.** Projecting the cofree extension of a
generator lens to depth `n` is its `n`-step run. -/
theorem extend_comp_projectionN
    {P : PFunctor.{u, u}} (C : Comonoid.{u, u})
    (lens : Lens C.carrier P) (n : ℕ) :
    projectionN P n ∘ₗ (extend C lens).toLens =
      lens.compNthMap n ∘ₗ C.comultN n := by
  simpa only [restrict_extend] using
    hom_comp_projectionN (extend C lens) n

end CofreeP
end PFunctor
