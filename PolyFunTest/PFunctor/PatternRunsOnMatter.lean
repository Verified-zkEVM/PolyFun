/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.PatternRunsOnMatter.Module
public import PolyFun.PFunctor.Cofree.FiniteProjection

/-!
# Regression tests for pattern running on matter

The decisive example below uses different branching types in the pattern and
matter and follows two different directions in each. It detects a swapped
tensor factor, a repeated root, a discarded continuation, or a backward map
that records only the final edge.
-/

@[expose] public section

universe pA pB pA' pB' qA qB qA' qB' u

namespace PFunctor
namespace PatternRunsOnMatterTest

/-- The executable interaction does not identify any of the four generator
universes. -/
example (P : PFunctor.{pA, pB}) (Q : PFunctor.{qA, qB}) :
    Lens (FreeP P ⊗ CofreeP Q) (FreeP (P ⊗ Q)) :=
  FreeP.runOn P Q

/-- Naturality likewise preserves all eight source/target generator
universes. -/
example {P : PFunctor.{pA, pB}} {P' : PFunctor.{pA', pB'}}
    {Q : PFunctor.{qA, qB}} {Q' : PFunctor.{qA', qB'}}
    (f : Lens P P') (g : Lens Q Q') :
    FreeP.runOn P' Q' ∘ₗ (FreeP.map f ⊗ₗ CofreeP.map g) =
      FreeP.map (f ⊗ₗ g) ∘ₗ FreeP.runOn P Q :=
  FreeP.runOn_natural f g

/-- The convolution/free-universal construction needs only the direction
ceiling induced by the matter polynomial, not a square category. -/
example (P : PFunctor.{pA, max qA qB}) (Q : PFunctor.{qA, qB}) :
    Lens (FreeP P ⊗ CofreeP Q) (FreeP (P ⊗ Q)) :=
  FreeP.xi P Q

example (P : PFunctor.{pA, max qA qB}) (Q : PFunctor.{qA, qB}) :
    FreeP.runOn P Q = FreeP.xi P Q :=
  FreeP.runOn_eq_xi P Q

example {P : PFunctor.{pA, max qA qB}}
    {P' : PFunctor.{pA', max qA' qB'}}
    {Q : PFunctor.{qA, qB}} {Q' : PFunctor.{qA', qB'}}
    (f : Lens P P') (g : Lens Q Q') :
    FreeP.xi P' Q' ∘ₗ (FreeP.map f ⊗ₗ CofreeP.map g) =
      FreeP.map (f ⊗ₗ g) ∘ₗ FreeP.xi P Q :=
  FreeP.xi_natural f g

/-- A square category remains an important specialization for the module
coherence laws. -/
example (P Q : PFunctor.{u, u}) :
    Lens (FreeP P ⊗ CofreeP Q) (FreeP (P ⊗ Q)) :=
  FreeP.xi P Q

example (P Q : PFunctor.{u, u}) :
    FreeP.runOn P Q = FreeP.xi P Q :=
  FreeP.runOn_eq_xi P Q

example (P : PFunctor.{u, u}) :
    (FreeP.map (Lens.Equiv.tensorX (P := P)).toLens ∘ₗ
        FreeP.runOn P X.{u, u}) ∘ₗ
        (Lens.id (FreeP P) ⊗ₗ CofreeP.laxUnit.{u, u}) =
      (Lens.Equiv.tensorX (P := FreeP P)).toLens :=
  FreeP.runOn_unit P

example (P Q R : PFunctor.{u, u}) :
    (FreeP.runOn P (Q ⊗ R) ∘ₗ
        (Lens.id (FreeP P) ⊗ₗ CofreeP.laxTensor Q R)) ∘ₗ
        (Lens.Equiv.tensorAssoc
          (P := FreeP P) (Q := CofreeP Q)
          (R := CofreeP R)).toLens =
      (FreeP.map
          (Lens.Equiv.tensorAssoc
            (P := P) (Q := Q) (R := R)).toLens ∘ₗ
        FreeP.runOn (P ⊗ Q) R) ∘ₗ
        (FreeP.runOn P Q ⊗ₗ Lens.id (CofreeP R)) :=
  FreeP.runOn_assoc P Q R

abbrev patternP : PFunctor := ⟨Bool, fun _ => Bool⟩

inductive MatterLabel where
  | initial
  | afterZero
  | afterOne
  | afterTwo
  deriving DecidableEq

abbrev matterP : PFunctor := ⟨MatterLabel, fun _ => Fin 3⟩

def pattern : (FreeP patternP).A :=
  .liftBind false fun first =>
    .liftBind first fun _ =>
      .pure PUnit.unit

def matterStep (history : List (Fin 3)) : matterP (List (Fin 3)) :=
  ⟨match history.head? with
    | none => .initial
    | some 0 => .afterZero
    | some 1 => .afterOne
    | some _ => .afterTwo,
    fun direction => direction :: history⟩

def matter : (CofreeP matterP).A := M.corec matterStep []

def oneNode : (FreeP patternP).A :=
  .liftBind false fun _ : Bool => .pure PUnit.unit

def oneNodeOutputPath : FreeM.Path
    ((FreeP.runOn patternP matterP).toFunA (oneNode, matter)) :=
  ⟨(true, 2), ⟨⟩⟩

/-- Observe the root operation label of a nonempty free tree. -/
def rootLabel {P : PFunctor} {α : Type} : FreeM P α → Option P.A
  | .pure _ => none
  | .liftBind operation _ => some operation

/-- The forward one-node run synchronizes the pattern and matter root labels
in the advertised tensor order. -/
example : rootLabel
    ((FreeP.runOn patternP matterP).toFunA (oneNode, matter)) =
      some (false, .initial) := by
  rfl

/-- One synchronized step pairs the two root labels and preserves the order
of the pattern and matter directions in the backward result. -/
example :
    (FreeP.runOn patternP matterP).toFunB
      (oneNode, matter) oneNodeOutputPath =
      (⟨true, ⟨⟩⟩, .child 2 (.root _)) := by
  rfl

/-- A leaf pattern terminates immediately and returns the unadvanced matter
root through the backward map. -/
example :
    (FreeP.runOn patternP matterP).toFunB
        ((FreeM.pure PUnit.unit : (FreeP patternP).A), matter)
        ⟨⟩ =
      (⟨⟩, .root matter) :=
  rfl

/-- The chosen output path takes pattern branches `[false, true]` and matter
branches `[2, 0]`. -/
def outputPath : FreeM.Path
    ((FreeP.runOn patternP matterP).toFunA (pattern, matter)) :=
  ⟨(false, 2), ⟨(true, 0), ⟨⟩⟩⟩

def expectedPatternPath : FreeM.Path pattern :=
  ⟨false, ⟨true, ⟨⟩⟩⟩

def expectedMatterVertex : M.Vertex matter :=
  .child 2 (.child 0 (.root _))

/-- The complete dependent backward result records both synchronized steps in
the correct factor order. -/
example :
    (FreeP.runOn patternP matterP).toFunB (pattern, matter) outputPath =
      (expectedPatternPath, expectedMatterVertex) := by
  rfl

/-- The synchronized traversal consumes exactly two matter edges before the
finite pattern terminates. -/
example : M.Vertex.depth expectedMatterVertex = 2 := by
  rfl

/-- Change both operation labels and pull target branches back through a
nonidentity permutation. -/
def patternFlip : Lens patternP patternP :=
  (fun label => !label) ⇆ (fun _ direction => !direction)

/-- Rotate ternary directions while changing the visible matter state. -/
def matterRotate : Lens matterP matterP :=
  (fun label => match label with
    | .initial => .afterOne
    | .afterZero => .afterTwo
    | .afterOne => .initial
    | .afterTwo => .afterZero) ⇆
  (fun _ direction => (direction + 1) % 3)

def mappedAction : Lens (FreeP patternP ⊗ CofreeP matterP)
    (FreeP (patternP ⊗ matterP)) :=
  FreeP.runOn patternP matterP ∘ₗ
    (FreeP.map patternFlip ⊗ₗ CofreeP.map matterRotate)

def mappedOutputPath : FreeM.Path
    (mappedAction.toFunA (pattern, matter)) :=
  ⟨(false, 2), ⟨(true, 0), ⟨⟩⟩⟩

/-- Read a pattern path as its root-to-leaf direction sequence. -/
def patternDirections : (tree : (FreeP patternP).A) →
    FreeM.Path tree → List Bool
  | .pure _, _ => []
  | .liftBind _ rest, path =>
      path.1 :: patternDirections (rest path.1) path.2

/-- Observe the first direction of a matter vertex without exposing its
dependent tail. -/
def matterFirst : {tree : (CofreeP matterP).A} →
    M.Vertex tree → Option (Fin 3)
  | _, .root _ => none
  | _, .child direction _ => some direction

/-- Read every matter direction, erasing only the dependent subtree indices. -/
def matterDirections : {tree : (CofreeP matterP).A} →
    M.Vertex tree → List (Fin 3)
  | _, .root _ => []
  | _, .child direction next => direction :: matterDirections next

/-- The nonidentity pattern map is observable in the complete pulled-back
pattern path: both Boolean directions are flipped. -/
example :
    let pulled := mappedAction.toFunB (pattern, matter) mappedOutputPath
    patternDirections pattern pulled.1 = [true, false] := by
  rfl

/-- The mapped forward root observes both nonidentity label maps. -/
example : rootLabel (mappedAction.toFunA (pattern, matter)) =
    some (true, .afterOne) := by
  rfl

/-- The mapped matter vertex starts with the rotated source direction. -/
example :
    let pulled := mappedAction.toFunB (pattern, matter) mappedOutputPath
    matterFirst pulled.2 = some 0 := by
  change matterFirst
      (M.Vertex.pullMapLens matterRotate matter
        (.child 2 (.child 0 (.root _)))) = some 0
  rw [M.Vertex.pullMapLens_child]
  rfl

/-- Pulling through the nonidentity matter map preserves the complete
two-edge traversal rather than truncating its dependent tail. -/
example :
    let pulled := mappedAction.toFunB (pattern, matter) mappedOutputPath
    M.Vertex.depth pulled.2 = 2 := by
  change M.Vertex.depth
      (M.Vertex.pullMapLens matterRotate matter
        (.child 2 (.child 0 (.root _)))) = 2
  rw [M.Vertex.depth_pullMapLens]
  rfl

/-- Both generator-level direction rotations used by the depth-two mapped
path are pinned independently. -/
example : matterRotate.toFunB .initial 2 = 0 := by rfl

example : matterRotate.toFunB .afterZero 0 = 1 := by rfl

def mappedMatter : (CofreeP matterP).A :=
  (CofreeP.map matterRotate).toFunA matter

def mappedMatterDirection :
    (compNth matterP 2).B
      ((CofreeP.projectionN matterP 2).toFunA mappedMatter) :=
  ⟨2, ⟨0, PUnit.unit⟩⟩

def mappedMatterVertex : M.Vertex mappedMatter :=
  (CofreeP.projectionN matterP 2).toFunB
    mappedMatter mappedMatterDirection

/-- Both rotated directions occur in the actual mapped cofree traversal. -/
theorem mappedMatterDirections :
    matterDirections
      ((CofreeP.map matterRotate).toFunB matter mappedMatterVertex) =
        [0, 1] := by
  let F := CofreeP.mapHom matterRotate
  have h := congrArg
    (fun lens : Lens (CofreeP.comonoid matterP).carrier
        (compNth matterP 2) =>
      lens.toFunB matter mappedMatterDirection)
    (CofreeP.hom_comp_projectionN F 2)
  dsimp only [mappedMatterVertex]
  change matterDirections
      ((F.toLens ⨟ CofreeP.projectionN matterP 2).toFunB
        matter mappedMatterDirection) = [0, 1]
  have hdirections := congrArg matterDirections h
  have hrestrict :
      CofreeP.restrict (CofreeP.comonoid matterP) F =
        matterRotate ∘ₗ CofreeP.cogenerator matterP := by
    dsimp only [F, CofreeP.restrict]
    exact CofreeP.cogenerator_comp_map matterRotate
  exact hdirections.trans (by
    rw [hrestrict]
    simp only [CofreeP.comonoid_carrier, compNth,
      Lens.compNthMap_succ, Lens.compNthMap_zero,
      Comonoid.comultN_succ, Comonoid.comultN_zero]
    rfl)

/-- The mapped interaction uses that complete cofree pullback, not merely its
first edge and depth. -/
example :
    let pulled := mappedAction.toFunB (pattern, matter) mappedOutputPath
    matterDirections pulled.2 = [0, 1] := by
  change matterDirections
      ((CofreeP.map matterRotate).toFunB matter mappedMatterVertex) = [0, 1]
  exact mappedMatterDirections

/-- Proposition 3.3 is exercised with observable nonidentity maps in both
factors, rather than only identities or unit signatures. -/
example :
    FreeP.runOn patternP matterP ∘ₗ
        (FreeP.map patternFlip ⊗ₗ CofreeP.map matterRotate) =
      FreeP.map (patternFlip ⊗ₗ matterRotate) ∘ₗ
        FreeP.runOn patternP matterP :=
  FreeP.runOn_natural patternFlip matterRotate

/-- The universal construction computes the same complete labelled object on
the decisive depth-two input, including its backward map. -/
example :
    FreeP.runObj pattern matter =
      Lens.mapObj (FreeP.xi patternP matterP)
        (⟨(pattern, matter), id⟩ :
          (FreeP patternP ⊗ CofreeP matterP).Obj
            (FreeM.Path pattern × M.Vertex matter)) :=
  FreeP.runObj_eq_xi_mapObj patternP matterP pattern matter

/-- Unit coherence is operationally nontrivial on the two-node pattern. -/
example :
    ((FreeP.map (Lens.Equiv.tensorX (P := patternP)).toLens ∘ₗ
        FreeP.runOn patternP X) ∘ₗ
        (Lens.id (FreeP patternP) ⊗ₗ CofreeP.laxUnit)).toFunA
        (pattern, PUnit.unit) = pattern := by
  have h := congrArg
    (fun lens : Lens (FreeP patternP ⊗ X) (FreeP patternP) =>
      lens.toFunA (pattern, PUnit.unit))
    (FreeP.runOn_unit patternP)
  exact h

def unitAction : Lens (FreeP patternP ⊗ X.{0, 0}) (FreeP patternP) :=
  (FreeP.map (Lens.Equiv.tensorX (P := patternP)).toLens ∘ₗ
      FreeP.runOn patternP X) ∘ₗ
    (Lens.id (FreeP patternP) ⊗ₗ CofreeP.laxUnit)

/-- Unit coherence preserves a complete nonempty pattern path through the
backward map, including the unit direction discarded by tensor unitor. -/
example :
    unitAction.toFunB (pattern, PUnit.unit) expectedPatternPath =
      (expectedPatternPath, PUnit.unit) := by
  rfl

abbrev auxiliaryP : PFunctor := ⟨Bool, fun _ => Bool⟩

def auxiliaryStep (history : List Bool) : auxiliaryP (List Bool) :=
  ⟨history.head?.getD false, fun direction => direction :: history⟩

def auxiliaryMatter : (CofreeP auxiliaryP).A :=
  M.corec auxiliaryStep []

def assocLhs :
    Lens ((FreeP patternP ⊗ CofreeP matterP) ⊗ CofreeP auxiliaryP)
      (FreeP (patternP ⊗ (matterP ⊗ auxiliaryP))) :=
  (FreeP.runOn patternP (matterP ⊗ auxiliaryP) ∘ₗ
      (Lens.id (FreeP patternP) ⊗ₗ
        CofreeP.laxTensor matterP auxiliaryP)) ∘ₗ
    (Lens.Equiv.tensorAssoc
      (P := FreeP patternP) (Q := CofreeP matterP)
      (R := CofreeP auxiliaryP)).toLens

def assocRhs :
    Lens ((FreeP patternP ⊗ CofreeP matterP) ⊗ CofreeP auxiliaryP)
      (FreeP (patternP ⊗ (matterP ⊗ auxiliaryP))) :=
  (FreeP.map
      (Lens.Equiv.tensorAssoc
        (P := patternP) (Q := matterP) (R := auxiliaryP)).toLens ∘ₗ
      FreeP.runOn (patternP ⊗ matterP) auxiliaryP) ∘ₗ
    (FreeP.runOn patternP matterP ⊗ₗ Lens.id (CofreeP auxiliaryP))

def assocOutputPath : FreeM.Path
    (assocRhs.toFunA ((pattern, matter), auxiliaryMatter)) :=
  ⟨(false, (2, true)), ⟨(true, (0, false)), ⟨⟩⟩⟩

def expectedAuxiliaryVertex : M.Vertex auxiliaryMatter :=
  .child true (.child false (.root _))

/-- Read every auxiliary direction, erasing only dependent subtree indices. -/
def auxiliaryDirections : {tree : (CofreeP auxiliaryP).A} →
    M.Vertex tree → List Bool
  | _, .root _ => []
  | _, .child direction next => direction :: auxiliaryDirections next

def synchronizedMatter : (CofreeP (matterP ⊗ auxiliaryP)).A :=
  (CofreeP.laxTensor matterP auxiliaryP).toFunA
    (matter, auxiliaryMatter)

def synchronizedDirection :
    (compNth (matterP ⊗ auxiliaryP) 2).B
      ((CofreeP.projectionN (matterP ⊗ auxiliaryP) 2).toFunA
        synchronizedMatter) :=
  ⟨(2, true), ⟨(0, false), PUnit.unit⟩⟩

def synchronizedVertex : M.Vertex synchronizedMatter :=
  (CofreeP.projectionN (matterP ⊗ auxiliaryP) 2).toFunB
    synchronizedMatter synchronizedDirection

/-- The cofree laxator's finite projection independently exposes both
component direction streams through its cast-free universal equation. -/
theorem synchronizedBackwardDirections :
    let pulled := (CofreeP.laxTensor matterP auxiliaryP).toFunB
      (matter, auxiliaryMatter) synchronizedVertex
    matterDirections pulled.1 = [2, 0] ∧
      auxiliaryDirections pulled.2 = [true, false] := by
  let F := CofreeP.laxTensorHom matterP auxiliaryP
  have h := congrArg
    (fun lens : Lens
        ((CofreeP.comonoid matterP).tensor
          (CofreeP.comonoid auxiliaryP)).carrier
        (compNth (matterP ⊗ auxiliaryP) 2) =>
      lens.toFunB (matter, auxiliaryMatter) synchronizedDirection)
    (CofreeP.hom_comp_projectionN F 2)
  dsimp only [synchronizedVertex]
  change
    matterDirections
        ((F.toLens ⨟
          CofreeP.projectionN (matterP ⊗ auxiliaryP) 2).toFunB
          (matter, auxiliaryMatter) synchronizedDirection).1 = [2, 0] ∧
      auxiliaryDirections
        ((F.toLens ⨟
          CofreeP.projectionN (matterP ⊗ auxiliaryP) 2).toFunB
          (matter, auxiliaryMatter) synchronizedDirection).2 = [true, false]
  have hmatter := congrArg (fun pair => matterDirections pair.1) h
  have hauxiliary := congrArg (fun pair => auxiliaryDirections pair.2) h
  constructor
  · exact hmatter.trans (by
      dsimp only [F, CofreeP.laxTensorHom]
      rw [CofreeP.restrict_extend]
      simp only [CofreeP.comonoid_carrier, Comonoid.tensor_carrier, compNth,
        Lens.compNthMap_succ, Lens.compNthMap_zero,
        Comonoid.comultN_succ, Comonoid.comultN_zero]
      rfl)
  · exact hauxiliary.trans (by
      dsimp only [F, CofreeP.laxTensorHom]
      rw [CofreeP.restrict_extend]
      simp only [CofreeP.comonoid_carrier, Comonoid.tensor_carrier, compNth,
        Lens.compNthMap_succ, Lens.compNthMap_zero,
        Comonoid.comultN_succ, Comonoid.comultN_zero]
      rfl)

/-- The two parenthesizations compute the same depth-two output position. -/
example : assocLhs.toFunA ((pattern, matter), auxiliaryMatter) =
    assocRhs.toFunA ((pattern, matter), auxiliaryMatter) := by
  rfl

def assocLhsOutputPath : FreeM.Path
    (assocLhs.toFunA ((pattern, matter), auxiliaryMatter)) :=
  ⟨(false, (2, true)), ⟨(true, (0, false)), ⟨⟩⟩⟩

/-- The cast-heavy combined route is evaluated directly, independently of
`runOn_assoc`: it preserves the complete pattern path and both distinguishable
matter streams. -/
example :
    let pulled := assocLhs.toFunB
      ((pattern, matter), auxiliaryMatter) assocLhsOutputPath
    patternDirections pattern pulled.1.1 = [false, true] ∧
      matterDirections pulled.1.2 = [2, 0] ∧
      auxiliaryDirections pulled.2 = [true, false] := by
  dsimp only [assocLhs, assocLhsOutputPath]
  change [false, true] = [false, true] ∧
    matterDirections
        ((CofreeP.laxTensor matterP auxiliaryP).toFunB
          (matter, auxiliaryMatter) synchronizedVertex).1 = [2, 0] ∧
      auxiliaryDirections
        ((CofreeP.laxTensor matterP auxiliaryP).toFunB
          (matter, auxiliaryMatter) synchronizedVertex).2 = [true, false]
  exact ⟨rfl, synchronizedBackwardDirections⟩

/-- The decisive associativity canary independently evaluates the sequential
route, distinguishing all three direction streams. Together with the explicit
full-lens theorem surface above, this pins the combined route as well. -/
example :
    assocRhs.toFunB ((pattern, matter), auxiliaryMatter)
        assocOutputPath =
      ((expectedPatternPath, expectedMatterVertex),
        expectedAuxiliaryVertex) := by
  rfl

end PatternRunsOnMatterTest
end PFunctor
