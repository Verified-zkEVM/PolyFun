/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.FiniteProjection
public import PolyFunTest.PFunctor.CofreePolynomial

/-!
# Regression tests for finite cofree projections

The tests pin the independent-universe API, the structural zero/successor
equations, actual backward-map path order at depths one and two, and the full
lens equality of Proposition 8.49.
-/

@[expose] public section

universe uA uB u

namespace PFunctor
namespace CofreeFiniteProjectionTest

open CofreePolynomialTest

/-! ## Universe and structural canaries -/

/-- Structural truncation keeps the generator's position and direction
universes independent. -/
example (P : PFunctor.{uA, uB}) (n : ℕ) :
    Lens (CofreeP P) (compNth P n) :=
  CofreeP.projectionN P n

example (P : PFunctor.{uA, uB}) (n : ℕ) (tree : M P)
    (direction :
      (compNth P n).B ((CofreeP.projectionN P n).toFunA tree)) :
    M.Vertex.depth
        ((CofreeP.projectionN P n).toFunB tree direction) = n :=
  CofreeP.depth_projectionN_toFunB P n tree direction

example (P : PFunctor.{uA, uB}) :
    CofreeP.projectionN P 1 ⨟ Lens.Equiv.compX.toLens =
      CofreeP.cogenerator P :=
  CofreeP.projectionN_one_comp_compX P

example (P : PFunctor.{uA, uB}) :
    CofreeP.projectionN P 2 ⨟
        (Lens.id P ◃ₗ Lens.Equiv.compX.toLens) =
      CofreeP.comult ⨟
        (CofreeP.cogenerator P ◃ₗ CofreeP.cogenerator P) :=
  CofreeP.projectionN_two_comp_compX P

/-! ## Concrete finite paths -/

/-- The unique depth-zero direction selects the root vertex. -/
example : (CofreeP.projectionN binaryP 0).toFunB binaryTree PUnit.unit =
    .root binaryTree :=
  rfl

/-- A one-stage composite direction selects the corresponding one-edge
vertex; the trailing unit direction does not add an edge. -/
example : (CofreeP.projectionN binaryP 1).toFunB binaryTree
      ⟨false, PUnit.unit⟩ =
    .child false (.root (M.children binaryTree false)) :=
  rfl

/-- Two distinct directions are retained in outer-then-inner order. -/
example : (CofreeP.projectionN binaryP 2).toFunB binaryTree
      ⟨false, ⟨true, PUnit.unit⟩⟩ =
    .child false
      (.child true
        (.root (M.children (M.children binaryTree false) true))) :=
  rfl

/-- The concrete two-edge pullback has exactly depth two. -/
example : M.Vertex.depth
      ((CofreeP.projectionN binaryP 2).toFunB binaryTree
        ⟨false, ⟨true, PUnit.unit⟩⟩) = 2 := by
  exact CofreeP.depth_projectionN_toFunB binaryP 2 binaryTree
    ⟨false, ⟨true, PUnit.unit⟩⟩

/-! ## Proposition 8.49 canaries -/

/-- The stronger arbitrary-retrofunctor equation is exported as a full lens
equality, not merely an equality of position maps. -/
example (P : PFunctor.{u, u}) (C : Comonoid.{u, u})
    (hom : Comonoid.Hom C (CofreeP.comonoid P)) (n : ℕ) :
    hom.toLens ⨟ CofreeP.projectionN P n =
      C.comultN n ⨟
        (CofreeP.restrict C hom).compNthMap n :=
  CofreeP.hom_comp_projectionN hom n

/-- Proposition 8.49 itself holds for an arbitrary generator lens and every
finite depth. -/
example (P : PFunctor.{u, u}) (C : Comonoid.{u, u})
    (lens : Lens C.carrier P) (n : ℕ) :
    (CofreeP.extend C lens).toLens ⨟ CofreeP.projectionN P n =
      C.comultN n ⨟ lens.compNthMap n :=
  CofreeP.extend_comp_projectionN C lens n

end CofreeFiniteProjectionTest
end PFunctor
