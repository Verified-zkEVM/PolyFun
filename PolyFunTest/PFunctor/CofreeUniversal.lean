/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.Universal
public import PolyFunTest.PFunctor.CofreePolynomial
public import PolyFunTest.PFunctor.Comonoid.Category

/-!
# Regression tests for the cofree polynomial universal property

The tests keep generic coiteration universe-independent, make coiterated
branching observable on a three-state category, and use the non-thin Boolean
list category to distinguish root, one-edge, and two-edge path pulls.  Both
round trips and both naturality variables of the hom-set equivalence are
exercised through exported declarations.
-/

@[expose] public section

universe uA uB uCA uCB

namespace PFunctor
namespace CofreeUniversalTest

open CofreePolynomialTest
open ComonoidCategoryTest

/-! ## Universe and cogenerator canaries -/

/-- Generic coiteration keeps the comonoid and generator universe pairs
independent. -/
example (P : PFunctor.{uA, uB}) (C : Comonoid.{uCA, uCB})
    (lens : Lens C.carrier P) : Lens C.carrier (CofreeP P) :=
  CofreeP.unfoldLens C lens

/-- The underlying cogenerator square retains the heterogeneous universe
boundary of cofree mapping, even though `mapHom` later specializes it. -/
example (P : PFunctor.{uA, uB}) (Q : PFunctor.{uCA, uCB})
    (lens : Lens P Q) :
    CofreeP.cogenerator Q ∘ₗ CofreeP.map lens =
      lens ∘ₗ CofreeP.cogenerator P :=
  CofreeP.cogenerator_comp_map lens

/-- The semantic subtree equation is available at the same fully
heterogeneous boundary. -/
example (P : PFunctor.{uA, uB}) (C : Comonoid.{uCA, uCB})
    (lens : Lens C.carrier P) (object : C.carrier.A)
    (vertex : M.Vertex (CofreeP.unfoldShape C lens object)) :
    M.Vertex.subtree vertex =
      CofreeP.unfoldShape C lens
        (Comonoid.target C object
          (CofreeP.unfoldDirection C lens object vertex)) :=
  CofreeP.subtree_unfoldShape C lens object vertex

/-- Homomorphism packaging is localized to the homogeneous maximum occupied
by `CofreeP P`. -/
example (P : PFunctor.{uA, uB})
    (C : Comonoid.{max uA uB, max uA uB})
    (lens : Lens C.carrier P) :
    Comonoid.Hom C (CofreeP.comonoid P) :=
  CofreeP.extend C lens

example (P : PFunctor.{uA, uB})
    (C : Comonoid.{max uA uB, max uA uB}) :
    Comonoid.Hom C (CofreeP.comonoid P) ≃ Lens C.carrier P :=
  CofreeP.homEquiv C

/-- The cogenerator exposes the root label. -/
example : (CofreeP.cogenerator binaryP).toFunA binaryTree =
    M.head binaryTree :=
  rfl

/-- Its backward map really selects the requested depth-one vertex. -/
example : (CofreeP.cogenerator binaryP).toFunB binaryTree false =
    .child false (.root (M.children binaryTree false)) :=
  rfl

/-! ## Observable three-state unfolding -/

/-- A state-category generator whose two source branches enter states with
different exposed labels. -/
def branchingLens : Lens (stateComonoid ThreeState).carrier binaryP where
  toFunA
    | .source => false
    | .middle => true
    | .final => false
  toFunB state direction :=
    match state, direction with
    | .source, false => .middle
    | .source, true => .final
    | .middle, false => .source
    | .middle, true => .final
    | .final, false => .source
    | .final, true => .middle

def branchingTree : M binaryP :=
  CofreeP.unfoldShape (stateComonoid ThreeState) branchingLens .source

example : M.head branchingTree = false := by
  exact CofreeP.head_unfoldShape
    (stateComonoid ThreeState) branchingLens .source

/-- The `false` branch enters `middle`, whose label is observably `true`. -/
example : M.head (M.children branchingTree false) = true := by
  unfold branchingTree
  rw [CofreeP.children_unfoldShape]
  exact CofreeP.head_unfoldShape
    (stateComonoid ThreeState) branchingLens .middle

/-- The other branch enters `final`, whose label remains distinct. -/
example : M.head (M.children branchingTree true) = false := by
  unfold branchingTree
  rw [CofreeP.children_unfoldShape]
  exact CofreeP.head_unfoldShape
    (stateComonoid ThreeState) branchingLens .final

/-! ## Non-thin path-order model -/

/-- Fix the otherwise unconstrained position universe of the test-local pure
power comonoid. -/
abbrev boolListComonoid : Comonoid.{0, 0} :=
  listMonoidComonoid

/-- Interpret a Boolean generator direction as the corresponding singleton
arrow in the one-object Boolean-list category. -/
def bitGenerator : Lens boolListComonoid.carrier binaryP :=
  (fun _ => false) ⇆ (fun _ direction => [direction])

def listExtension : Comonoid.Hom
    boolListComonoid (CofreeP.comonoid binaryP) :=
  CofreeP.extend boolListComonoid bitGenerator

def listObject : boolListComonoid.carrier.A :=
  PUnit.unit

def listTree : M binaryP :=
  listExtension.toLens.toFunA listObject

def falseVertex : M.Vertex listTree :=
  .child false (.root _)

def innerTrueVertex : M.Vertex (M.Vertex.subtree falseVertex) :=
  .child true (.root _)

def falseThenTrueVertex : M.Vertex listTree :=
  M.Vertex.append falseVertex innerTrueVertex

/-- The concrete extension uses the generic coiterated shape. -/
example : listTree =
    CofreeP.unfoldShape boolListComonoid bitGenerator listObject :=
  rfl

/-- The root path is the identity arrow, hence the empty list. -/
example : listExtension.toLens.toFunB listObject (.root listTree) = [] := by
  calc
    _ = Comonoid.identity boolListComonoid listObject := by
      simpa [listTree] using listExtension.map_identity listObject
    _ = [] := rfl

/-- Every one-edge path pulls back to the corresponding singleton arrow. -/
theorem listExtension_oneLayer (object : boolListComonoid.carrier.A)
    (direction : Bool) :
    listExtension.toLens.toFunB object
        (.child direction (.root
          (M.children (listExtension.toLens.toFunA object) direction))) =
      [direction] := by
  have h := congrArg
    (fun lens : Lens boolListComonoid.carrier binaryP =>
      lens.toFunB object direction)
    (CofreeP.restrict_extend boolListComonoid bitGenerator)
  change (CofreeP.restrict boolListComonoid listExtension).toFunB
    object direction = [direction]
  simpa [listExtension, bitGenerator] using h

/-- A concrete one-edge path exposes the `false` singleton. -/
example : listExtension.toLens.toFunB listObject falseVertex = [false] :=
  listExtension_oneLayer listObject false

/-- A two-edge path records both arrows in outer-then-inner order. -/
example : listExtension.toLens.toFunB listObject falseThenTrueVertex =
    [false, true] := by
  have hmap := listExtension.map_compose
    listObject falseVertex innerTrueVertex
  let nextObject := Comonoid.target boolListComonoid listObject
    (listExtension.toLens.toFunB listObject falseVertex)
  let nextTrueVertex : M.Vertex
      (listExtension.toLens.toFunA nextObject) :=
    .child true (.root _)
  have htree : M.Vertex.subtree falseVertex =
      listExtension.toLens.toFunA nextObject :=
    (listExtension.map_target listObject falseVertex).symm
  have hraw : innerTrueVertex ≍ nextTrueVertex := by
    cases htree
    rfl
  have htailAny (vertex : M.Vertex
      (listExtension.toLens.toFunA nextObject))
      (hvertex : vertex ≍ nextTrueVertex) :
      listExtension.toLens.toFunB nextObject vertex = [true] := by
    have hvertexEq : vertex = nextTrueVertex := eq_of_heq hvertex
    rw [hvertexEq]
    exact listExtension_oneLayer nextObject true
  have hfirst :
      listExtension.toLens.toFunB listObject falseVertex = [false] :=
    listExtension_oneLayer listObject false
  change listExtension.toLens.toFunB listObject
    (M.Vertex.append falseVertex innerTrueVertex) = [false, true]
  refine hmap.trans ?_
  rw [hfirst]
  change [false] ++ _ = [false] ++ [true]
  congr 1
  apply htailAny
  exact (cast_heq _ innerTrueVertex).trans hraw

/-! ## Universal-property round trips -/

example : CofreeP.restrict boolListComonoid listExtension = bitGenerator := by
  simp [listExtension]

example (hom : Comonoid.Hom
    boolListComonoid (CofreeP.comonoid binaryP)) :
    CofreeP.extend boolListComonoid
        (CofreeP.restrict boolListComonoid hom) = hom := by
  simp

example : (CofreeP.homEquiv boolListComonoid).symm
      ((CofreeP.homEquiv boolListComonoid) listExtension) =
    listExtension :=
  (CofreeP.homEquiv boolListComonoid).symm_apply_apply _

example : CofreeP.homEquiv boolListComonoid
      ((CofreeP.homEquiv boolListComonoid).symm bitGenerator) =
    bitGenerator :=
  (CofreeP.homEquiv boolListComonoid).apply_symm_apply _

/-- Extending the canonical cogenerator recovers the identity retrofunctor. -/
example : CofreeP.extend (CofreeP.comonoid binaryP)
      (CofreeP.cogenerator binaryP) =
    Comonoid.Hom.id (CofreeP.comonoid binaryP) := by
  simpa [CofreeP.restrict] using
    CofreeP.extend_restrict
      (C := CofreeP.comonoid binaryP)
      (Comonoid.Hom.id (CofreeP.comonoid binaryP))

/-! ## Naturality canaries -/

/-- Source-side naturality is exercised with the nontrivial state projection
retrofunctor. -/
example :
    CofreeP.homEquiv (stateComonoid (ThreeState × Bool))
        (fstHom.comp
          (CofreeP.extend (stateComonoid ThreeState) branchingLens)) =
      CofreeP.homEquiv (stateComonoid ThreeState)
          (CofreeP.extend (stateComonoid ThreeState) branchingLens) ∘ₗ
        fstHom.toLens :=
  CofreeP.homEquiv_natural_left fstHom
    (CofreeP.extend (stateComonoid ThreeState) branchingLens)

/-- Generator-side naturality is exercised with a branch-reversing lens. -/
example :
    CofreeP.homEquiv boolListComonoid
        (listExtension.comp (CofreeP.mapHom reverseBranchLens)) =
      reverseBranchLens ∘ₗ
        CofreeP.homEquiv boolListComonoid listExtension :=
  CofreeP.homEquiv_natural_right boolListComonoid
    reverseBranchLens listExtension

end CofreeUniversalTest
end PFunctor
