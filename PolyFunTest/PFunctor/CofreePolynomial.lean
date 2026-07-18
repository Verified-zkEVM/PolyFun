/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.Polynomial

/-!
# Regression tests for the cofree polynomial comonoid

The examples make vertex labels, backward branch transport, and path
concatenation observable on a concrete binary M-type tree.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uA₃ uB₃

namespace PFunctor
namespace CofreePolynomialTest

/-- A binary signature whose positions and directions are both bits. -/
abbrev binaryP : PFunctor := ⟨Bool, fun _ => Bool⟩

/-- The current node remembers the most recently selected branch. -/
def binaryStep (history : List Bool) : binaryP (List Bool) :=
  ⟨history.head?.getD false, fun direction => direction :: history⟩

def binaryTree : M binaryP :=
  M.corec binaryStep []

/-- Distinct first-edge labels make branch orientation observable. -/
def vertexLabel : M.Vertex binaryTree → Nat
  | .root _ => 3
  | .child false _ => 5
  | .child true _ => 7

def labelledTree : (CofreeP binaryP).Obj Nat :=
  ⟨binaryTree, vertexLabel⟩

example : CofreeC.head (CofreeP.decode labelledTree) = 3 := by
  exact congrArg Prod.fst (CofreeP.head_decode labelledTree)

/-- Decoding the `true` child exposes its distinct label. -/
example : CofreeC.head
      (M.children (CofreeP.decode labelledTree)
        (CofreeP.toDecodeDirection labelledTree true)) = 7 := by
  rw [CofreeP.children_decode]
  exact congrArg Prod.fst
    (CofreeP.head_decode (CofreeP.childObj labelledTree true))

/-- The other branch remains distinguishable, ruling out a constant or
reversed child-label implementation. -/
example : CofreeC.head
      (M.children (CofreeP.decode labelledTree)
        (CofreeP.toDecodeDirection labelledTree false)) = 5 := by
  rw [CofreeP.children_decode]
  exact congrArg Prod.fst
    (CofreeP.head_decode (CofreeP.childObj labelledTree false))

/-- Exported round-trip simp contracts remain usable without naming the
underlying transport theorems. -/
example : CofreeP.encode (CofreeP.decode labelledTree) = labelledTree := by
  simp

example : CofreeP.decode (CofreeP.encode (CofreeP.decode labelledTree)) =
    CofreeP.decode labelledTree := by
  simp

/-- The label universe of the extension equivalence is independent of both
generator universes. -/
example (P : PFunctor.{uA, uB}) (α : Type uA₂) :
    (CofreeP P).Obj α ≃ CofreeC P α :=
  CofreeP.objEquiv

/-- Reverse target branches in the backward direction of a lens. -/
def reverseBranchLens : Lens binaryP binaryP :=
  id ⇆ fun _ direction => !direction

def mappedFalse : M.Vertex (M.mapLens reverseBranchLens binaryTree) :=
  .child false (.root _)

/-- The cofree-polynomial map really pulls target `false` back to source
`true`. -/
example :
    match (CofreeP.map reverseBranchLens).toFunB binaryTree mappedFalse with
    | .root _ => False
    | .child direction _ => direction = true := by
  change
    match M.Vertex.pullMapLens reverseBranchLens binaryTree mappedFalse with
    | .root _ => False
    | .child direction _ => direction = true
  unfold mappedFalse
  rw [M.Vertex.pullMapLens_child]
  rfl

/-- Comultiplication concatenates the outer and inner finite paths. -/
def outerVertex : M.Vertex binaryTree :=
  .child true (.root _)

def innerVertex : M.Vertex (M.Vertex.subtree outerVertex) :=
  .child false (.root _)

example : M.Vertex.depth
      ((CofreeP.comult (P := binaryP)).toFunB binaryTree
        ⟨outerVertex, innerVertex⟩) = 2 :=
  rfl

/-- Concatenation preserves the concrete outer-then-inner order, not merely
the total path length. -/
example :
    match (CofreeP.comult (P := binaryP)).toFunB binaryTree
        ⟨outerVertex, innerVertex⟩ with
    | .child outer (.child inner _) => outer = true ∧ inner = false
    | _ => False := by
  change
    match M.Vertex.append outerVertex innerVertex with
    | .child outer (.child inner _) => outer = true ∧ inner = false
    | _ => False
  simp [outerVertex, innerVertex]

/-- A third independently visible path component for coassociativity. -/
def thirdVertex : M.Vertex (M.Vertex.subtree innerVertex) :=
  .child true (.root _)

def depthThree : M.Vertex binaryTree :=
  .child true (.child false (.child true (.root _)))

def coassocLeft :
    Lens (CofreeP binaryP)
      (CofreeP binaryP ◃ (CofreeP binaryP ◃ CofreeP binaryP)) :=
  Lens.Equiv.compAssoc.toLens ∘ₗ
      (CofreeP.comult (P := binaryP) ◃ₗ Lens.id (CofreeP binaryP)) ∘ₗ
    CofreeP.comult (P := binaryP)

def coassocRight :
    Lens (CofreeP binaryP)
      (CofreeP binaryP ◃ (CofreeP binaryP ◃ CofreeP binaryP)) :=
  (Lens.id (CofreeP binaryP) ◃ₗ
      CofreeP.comult (P := binaryP)) ∘ₗ
    CofreeP.comult (P := binaryP)

/-- Left-associated comultiplication concatenates all three backward path
components in outer-to-inner order. -/
example : coassocLeft.toFunB binaryTree
    ⟨outerVertex, ⟨innerVertex, thirdVertex⟩⟩ = depthThree :=
  rfl

/-- Right-associated comultiplication has the same observable three-level
backward behavior. -/
example : coassocRight.toFunB binaryTree
    ⟨outerVertex, ⟨innerVertex, thirdVertex⟩⟩ = depthThree :=
  rfl

example :
    Lens.Equiv.compAssoc.toLens ∘ₗ
          (CofreeP.comult (P := binaryP) ◃ₗ Lens.id (CofreeP binaryP)) ∘ₗ
        CofreeP.comult (P := binaryP) =
      (Lens.id (CofreeP binaryP) ◃ₗ CofreeP.comult (P := binaryP)) ∘ₗ
        CofreeP.comult (P := binaryP) :=
  CofreeP.comult_coassoc

/-- Cofree-polynomial mapping leaves all source, intermediate, and target
polynomial universes independent. -/
example (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB₂})
    (lens : Lens P Q) : Lens (CofreeP P) (CofreeP Q) :=
  CofreeP.map lens

example : CofreeP.map (Lens.id binaryP) = Lens.id (CofreeP binaryP) := by
  simp

example (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB₂})
    (R : PFunctor.{uA₃, uB₃}) (f : Lens P Q) (g : Lens Q R) :
    CofreeP.map g ∘ₗ CofreeP.map f = CofreeP.map (g ∘ₗ f) :=
  CofreeP.map_comp g f

/-- The current comonoid-morphism API chooses one common generator universe
pair, ensuring the two carrier maxima agree for `Comonoid.Hom`. -/
example (P Q : PFunctor.{uA, uB}) (lens : Lens P Q) :
    Comonoid.Hom (CofreeP.comonoid P) (CofreeP.comonoid Q) :=
  CofreeP.mapHom lens

example :
    (CofreeP.mapHom reverseBranchLens).toLens =
      CofreeP.map reverseBranchLens := by
  simp

example :
    (CofreeP.comonoid binaryP).comult ∘ₗ
        CofreeP.map reverseBranchLens =
      (CofreeP.map reverseBranchLens ◃ₗ
          CofreeP.map reverseBranchLens) ∘ₗ
        (CofreeP.comonoid binaryP).comult :=
  CofreeP.map_comult reverseBranchLens

example :
    CofreeP.mapHom (Lens.id binaryP) =
      Comonoid.Hom.id (CofreeP.comonoid binaryP) := by
  simp

example (P Q R : PFunctor.{uA, uB})
    (f : Lens P Q) (g : Lens Q R) :
    (CofreeP.mapHom f).comp (CofreeP.mapHom g) =
      CofreeP.mapHom (g ∘ₗ f) := by
  simp

end CofreePolynomialTest
end PFunctor
