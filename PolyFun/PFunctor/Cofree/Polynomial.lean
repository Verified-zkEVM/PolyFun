/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree
public import PolyFun.PFunctor.Comonoid
public import PolyFun.PFunctor.M.Vertex

/-!
# The cofree polynomial comonoid

For a polynomial `P`, `CofreeP P` has potentially infinite `P`-trees as
positions and finite rooted vertices of each tree as directions.  Labelling
every finite vertex by `X` recovers the ordinary cofree comonad `CofreeC P X`.

This is the direct M-type presentation of the cofree polynomial comonoid in
Libkind–Spivak, *Pattern Runs on Matter*.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uA₃ uB₃ v

namespace PFunctor

/-- The polynomial of potentially infinite `P`-trees and their finite rooted
vertices. -/
@[reducible]
def CofreeP (P : PFunctor.{uA, uB}) :
    PFunctor.{max uA uB, max uA uB} :=
  ⟨M P, M.Vertex⟩

namespace CofreeP

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-! ## Polynomial extension and `CofreeC` -/

/-- One coalgebra step for decorating every finite vertex of an unlabelled
M-type tree. -/
def decodeStep (x : (CofreeP P).Obj α) :
    constProd P α ((CofreeP P).Obj α) :=
  ⟨(x.2 (.root x.1), M.head x.1), fun direction =>
    ⟨M.children x.1 direction, fun vertex =>
      x.2 (.child direction vertex)⟩⟩

/-- Restrict a vertex-labelled M-type tree to one child subtree. -/
def childObj (x : (CofreeP P).Obj α)
    (direction : P.B (M.head x.1)) : (CofreeP P).Obj α :=
  ⟨M.children x.1 direction, fun vertex =>
    x.2 (.child direction vertex)⟩

/-- Decorate every finite vertex of an unlabelled M-type tree, producing the
ordinary type-level cofree comonad. -/
def decode (x : (CofreeP P).Obj α) : CofreeC P α :=
  M.corec decodeStep x

/-- Forget the label component of one `constProd P α` node. -/
def forgetLabels (P : PFunctor.{uA, uB}) (α : Type v) :
    Lens (constProd P α) P :=
  Prod.snd ⇆ fun _ => id

/-- Erase all labels from a type-level cofree tree. -/
def erase (tree : CofreeC P α) : M P :=
  M.mapLens (forgetLabels P α) tree

/-- Recover an unlabelled shape together with the label observed at every
finite vertex. -/
def encode (tree : CofreeC P α) : (CofreeP P).Obj α :=
  ⟨erase tree, fun vertex =>
    CofreeC.head
      (M.Vertex.subtree
        (M.Vertex.pullMapLens (forgetLabels P α) tree vertex))⟩

/-- One-step unfolding of `decode`. -/
theorem dest_decode (x : (CofreeP P).Obj α) :
    M.dest (decode x) =
      ⟨(x.2 (.root x.1), M.head x.1), fun direction =>
        decode ⟨M.children x.1 direction, fun vertex =>
          x.2 (.child direction vertex)⟩⟩ := by
  simpa only [decode, decodeStep] using M.dest_corec_apply decodeStep x

/-- Decoding and then erasing preserves the exact unlabelled M-type shape. -/
@[simp]
theorem erase_decode (x : (CofreeP P).Obj α) :
    erase (decode x) = x.1 := by
  rw [erase, decode, M.mapLens_corec]
  conv_rhs => rw [← M.corec_dest x.1]
  refine M.corec_eq_corec
    (fun state => Lens.mapObj (forgetLabels P α) (decodeStep state))
    M.dest (fun state tree => state.1 = tree) x x.1 rfl ?_
  rintro state _ rfl
  refine ⟨M.head state.1,
    fun direction =>
      (⟨M.children state.1 direction, fun vertex =>
        state.2 (.child direction vertex)⟩ : (CofreeP P).Obj α),
    fun direction => M.children state.1 direction, rfl, rfl, fun _ => rfl⟩

/-- The root of `decode x` contains exactly the root label and polynomial
shape stored by `x`. -/
theorem head_decode (x : (CofreeP P).Obj α) :
    M.head (decode x) = (x.2 (.root x.1), M.head x.1) :=
  congrArg Sigma.fst (dest_decode x)

/-- Transport a source direction to the corresponding root direction of the
decoded cofree tree. -/
def toDecodeDirection (x : (CofreeP P).Obj α)
    (direction : P.B (M.head x.1)) :
    P.B (M.head (decode x)).2 :=
  cast (congrArg (constProd P α).B (head_decode x).symm) direction

/-- Decoding commutes with restriction to a child subtree. -/
theorem children_decode (x : (CofreeP P).Obj α)
    (direction : P.B (M.head x.1)) :
    M.children (decode x) (toDecodeDirection x direction) =
      decode (childObj x direction) := by
  have hChildren := (Sigma.ext_iff.mp (dest_decode x)).2
  exact congr_heq hChildren (cast_heq _ direction)

@[simp]
theorem forgetLabels_toFunB (shape : (constProd P α).A)
    (direction : P.B shape.2) :
    (forgetLabels P α).toFunB shape direction = direction :=
  rfl

/-- Pulling back the transported direction through label erasure selects the
same decoded child direction. -/
theorem pullDirection_decode (x : (CofreeP P).Obj α)
    (direction : P.B (M.head x.1)) :
    M.pullDirection (forgetLabels P α) (decode x)
        (M.castDirection (erase_decode x).symm direction) =
      toDecodeDirection x direction := by
  unfold M.pullDirection M.castDirection toDecodeDirection
  rw [forgetLabels_toFunB]
  apply eq_of_heq
  exact (cast_heq _ _).trans
    ((cast_heq _ direction).trans (cast_heq _ direction).symm)

@[simp]
theorem encode_root_label (tree : CofreeC P α) :
    (encode tree).2 (.root (erase tree)) = CofreeC.head tree := by
  change CofreeC.head
      (M.Vertex.subtree
        (M.Vertex.pullMapLens (forgetLabels P α) tree
          (.root (erase tree)))) = CofreeC.head tree
  unfold erase
  rw [M.Vertex.pullMapLens_root]
  rfl

/-- Restricting an encoding to one erased child is exactly the encoding of
the corresponding source child. -/
theorem encode_child (tree : CofreeC P α)
    (direction : P.B (M.head (erase tree))) :
    (⟨M.children (erase tree) direction, fun vertex =>
        (encode tree).2 (.child direction vertex)⟩ :
      (CofreeP P).Obj α) =
    encode (M.children tree
      (M.pullDirection (forgetLabels P α) tree direction)) := by
  let childEq := M.children_mapLens (forgetLabels P α) tree direction
  apply Sigma.ext childEq
  apply Function.hfunext (congrArg M.Vertex childEq)
  intro leftVertex rightVertex hVertex
  have hcast : cast (congrArg M.Vertex childEq) leftVertex = rightVertex :=
    (cast_eq_iff_heq).2 hVertex
  subst rightVertex
  apply heq_of_eq
  change CofreeC.head
      (M.Vertex.subtree
        (M.Vertex.pullMapLens (forgetLabels P α) tree
          (.child direction leftVertex))) =
    CofreeC.head
      (M.Vertex.subtree
        (M.Vertex.pullMapLens (forgetLabels P α)
          (M.children tree
            (M.pullDirection (forgetLabels P α) tree direction))
          (cast (congrArg M.Vertex childEq) leftVertex)))
  rw [M.Vertex.pullMapLens_child]
  rfl

/-- `encode` is a coalgebra morphism from a labelled cofree tree to the
vertex-decoration coalgebra used by `decode`. -/
theorem decodeStep_encode (tree : CofreeC P α) :
    decodeStep (encode tree) =
      (constProd P α).map encode (M.dest tree) := by
  let hPosition : (decodeStep (encode tree)).1 = (M.dest tree).1 := by
    apply Prod.ext
    · exact encode_root_label tree
    · exact M.head_mapLens (forgetLabels P α) tree
  apply Sigma.ext hPosition
  apply Function.hfunext
    (congrArg (constProd P α).B hPosition)
  intro leftDirection rightDirection hDirection
  apply heq_of_eq
  have hSource :
      M.pullDirection (forgetLabels P α) tree leftDirection =
        rightDirection := by
    change cast
      (congrArg P.B
        (M.head_mapLens (forgetLabels P α) tree)) leftDirection =
      rightDirection
    apply eq_of_heq
    exact (cast_heq
      (congrArg P.B (M.head_mapLens (forgetLabels P α) tree))
      leftDirection).trans hDirection
  calc
    (decodeStep (encode tree)).2 leftDirection =
        encode (M.children tree
          (M.pullDirection (forgetLabels P α) tree leftDirection)) :=
      encode_child tree leftDirection
    _ = encode (M.children tree rightDirection) := by rw [hSource]
    _ = ((constProd P α).map encode (M.dest tree)).2 rightDirection :=
      rfl

private theorem encode_decode_label (x : (CofreeP P).Obj α)
    (vertex : M.Vertex x.1) :
    (encode (decode x)).2
        (cast (congrArg M.Vertex (erase_decode x).symm) vertex) =
      x.2 vertex := by
  rcases x with ⟨tree, labels⟩
  change M.Vertex tree at vertex
  induction vertex with
  | root tree =>
      let x : (CofreeP P).Obj α := ⟨tree, labels⟩
      have hcast :
          cast (congrArg M.Vertex (erase_decode x).symm) (.root tree) =
            .root (erase (decode x)) :=
        M.Vertex.cast_root (erase_decode x).symm
      change (encode (decode x)).2
        (cast (congrArg M.Vertex (erase_decode x).symm) (.root tree)) =
          labels (.root tree)
      calc
        (encode (decode x)).2
            (cast (congrArg M.Vertex (erase_decode x).symm) (.root tree)) =
            (encode (decode x)).2 (.root (erase (decode x))) :=
          congrArg (encode (decode x)).2 hcast
        _ = CofreeC.head (decode x) := encode_root_label (decode x)
        _ = labels (.root tree) := congrArg Prod.fst (head_decode x)
  | child direction next ih =>
      let x : (CofreeP P).Obj α := ⟨_, labels⟩
      let erasedDirection :=
        M.castDirection (erase_decode x).symm direction
      let childShapeEq :=
        M.children_castDirection (erase_decode x).symm direction
      let erasedNext :=
        cast (congrArg M.Vertex childShapeEq) next
      have hvertex :
          cast (congrArg M.Vertex (erase_decode x).symm)
              (.child direction next) =
            .child erasedDirection erasedNext :=
        M.Vertex.cast_child (erase_decode x).symm direction next
      change (encode (decode x)).2
          (cast (congrArg M.Vertex (erase_decode x).symm)
            (.child direction next)) =
        labels (.child direction next)
      calc
        (encode (decode x)).2
            (cast (congrArg M.Vertex (erase_decode x).symm)
              (.child direction next)) =
            (encode (decode x)).2
              (.child erasedDirection erasedNext) :=
          congrArg (encode (decode x)).2 hvertex
        _ = (encode (decode (childObj x direction))).2
              (cast (congrArg M.Vertex
                (erase_decode (childObj x direction)).symm) next) := by
          have hobj := encode_child (decode x) erasedDirection
          have hpull := pullDirection_decode x direction
          change M.pullDirection (forgetLabels P α) (decode x)
              erasedDirection = toDecodeDirection x direction at hpull
          rw [hpull, children_decode] at hobj
          have hfunctions := (Sigma.ext_iff.mp hobj).2
          have hvertices : erasedNext ≍
              cast (congrArg M.Vertex
                (erase_decode (childObj x direction)).symm) next :=
            (cast_heq _ next).trans (cast_heq _ next).symm
          have happ := congr_heq hfunctions hvertices
          apply eq_of_heq
          exact heq_of_eq happ
        _ = labels (.child direction next) := by
          simpa only [x, childObj] using
            ih (fun vertex => labels (.child direction vertex))

/-- Decoding and then re-encoding preserves the exact unlabelled tree and
every finite vertex label. -/
@[simp]
theorem encode_decode (x : (CofreeP P).Obj α) :
    encode (decode x) = x := by
  apply Sigma.ext (erase_decode x)
  apply Function.hfunext (congrArg M.Vertex (erase_decode x))
  intro leftVertex rightVertex hVertex
  have hBack :
      cast (congrArg M.Vertex (erase_decode x).symm) rightVertex =
        leftVertex :=
    (cast_eq_iff_heq).2 hVertex.symm
  apply heq_of_eq
  calc
    (encode (decode x)).2 leftVertex =
        (encode (decode x)).2
          (cast (congrArg M.Vertex (erase_decode x).symm) rightVertex) :=
      congrArg (encode (decode x)).2 hBack.symm
    _ = x.2 rightVertex := encode_decode_label x rightVertex

/-- Encoding and then decoding a type-level cofree tree is the identity. -/
@[simp]
theorem decode_encode (tree : CofreeC P α) :
    decode (encode tree) = tree := by
  change M.corec decodeStep (encode tree) = tree
  conv_rhs => rw [← M.corec_dest tree]
  refine M.corec_eq_corec decodeStep M.dest
    (fun state source => state = encode source)
    (encode tree) tree rfl ?_
  rintro _ source rfl
  rcases hdest : M.dest source with ⟨shape, children⟩
  refine ⟨shape, fun direction => encode (children direction), children,
    ?_, rfl, fun _ => rfl⟩
  rw [decodeStep_encode, hdest]
  rfl

/-- Pointwise, the extension of the cofree polynomial is represented by the
ordinary type-level cofree comonad. This declaration does not claim a
naturality theorem; that compatibility belongs to the universal-property
layer. -/
def objEquiv : (CofreeP P).Obj α ≃ CofreeC P α where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

/-! ## Functoriality in the generating polynomial -/

/-- Map cofree-polynomial trees covariantly along a generating lens and pull
their finite vertices back contravariantly. -/
def map {Q : PFunctor.{uA₂, uB₂}} (lens : Lens P Q) :
    Lens (CofreeP P) (CofreeP Q) where
  toFunA := M.mapLens lens
  toFunB := M.Vertex.pullMapLens lens

@[simp]
theorem map_toFunA {Q : PFunctor.{uA₂, uB₂}} (lens : Lens P Q)
    (tree : (CofreeP P).A) :
    (map lens).toFunA tree = M.mapLens lens tree :=
  rfl

@[simp]
theorem map_toFunB {Q : PFunctor.{uA₂, uB₂}} (lens : Lens P Q)
    (tree : (CofreeP P).A)
    (vertex : (CofreeP Q).B ((map lens).toFunA tree)) :
    (map lens).toFunB tree vertex =
      M.Vertex.pullMapLens lens tree vertex :=
  rfl

/-- Pointwise container form of identity preservation for `CofreeP.map`. -/
private theorem map_obj_id (tree : (CofreeP P).A) :
    (⟨(map (Lens.id P)).toFunA tree,
        (map (Lens.id P)).toFunB tree⟩ :
      (CofreeP P).Obj (M.Vertex tree)) =
    ⟨tree, id⟩ := by
  let hPosition := M.mapLens_id tree
  apply Sigma.ext hPosition
  apply Function.hfunext (congrArg M.Vertex hPosition)
  intro leftVertex rightVertex hVertex
  have hcast :
      cast (congrArg M.Vertex hPosition) leftVertex = rightVertex :=
    (cast_eq_iff_heq).2 hVertex
  apply heq_of_eq
  calc
    (map (Lens.id P)).toFunB tree leftVertex =
        cast (congrArg M.Vertex hPosition) leftVertex :=
      M.Vertex.pullMapLens_id tree leftVertex
    _ = rightVertex := hcast

@[simp]
theorem map_id : map (Lens.id P) = Lens.id (CofreeP P) := by
  let hPosition : ∀ tree, (map (Lens.id P)).toFunA tree =
      (Lens.id (CofreeP P)).toFunA tree :=
    fun tree => congrArg Sigma.fst (map_obj_id tree)
  refine Lens.ext _ _ hPosition ?_
  intro tree
  apply eq_of_heq
  have hraw : (map (Lens.id P)).toFunB tree ≍
      (Lens.id (CofreeP P)).toFunB tree :=
    (Sigma.ext_iff.mp (map_obj_id tree)).2
  have hcast : (hPosition tree ▸
      (Lens.id (CofreeP P)).toFunB tree) ≍
      (Lens.id (CofreeP P)).toFunB tree :=
    eqRec_heq_self _ _
  exact hraw.trans hcast.symm

variable {Q : PFunctor.{uA₂, uB₂}}

/-- Pointwise container form of composition preservation for `CofreeP.map`. -/
private theorem map_obj_comp {R : PFunctor.{uA₃, uB₃}}
    (g : Lens Q R) (f : Lens P Q) (tree : (CofreeP P).A) :
    (⟨(map g ∘ₗ map f).toFunA tree,
        (map g ∘ₗ map f).toFunB tree⟩ :
      (CofreeP R).Obj (M.Vertex tree)) =
    ⟨(map (g ∘ₗ f)).toFunA tree,
      (map (g ∘ₗ f)).toFunB tree⟩ := by
  let hPosition := (M.mapLens_comp g f tree).symm
  apply Sigma.ext hPosition
  apply Function.hfunext (congrArg M.Vertex hPosition)
  intro leftVertex rightVertex hVertex
  have hBack :
      cast (congrArg M.Vertex (M.mapLens_comp g f tree)) rightVertex =
        leftVertex :=
    (cast_eq_iff_heq).2 hVertex.symm
  apply heq_of_eq
  change M.Vertex.pullMapLens f tree
      (M.Vertex.pullMapLens g (M.mapLens f tree) leftVertex) =
    M.Vertex.pullMapLens (g ∘ₗ f) tree rightVertex
  calc
    M.Vertex.pullMapLens f tree
        (M.Vertex.pullMapLens g (M.mapLens f tree) leftVertex) =
        M.Vertex.pullMapLens f tree
          (M.Vertex.pullMapLens g (M.mapLens f tree)
            (cast (congrArg M.Vertex (M.mapLens_comp g f tree))
              rightVertex)) := by rw [hBack]
    _ = (map (g ∘ₗ f)).toFunB tree rightVertex :=
      (M.Vertex.pullMapLens_comp g f tree rightVertex).symm

@[simp]
theorem map_comp {R : PFunctor.{uA₃, uB₃}}
    (g : Lens Q R) (f : Lens P Q) :
    map g ∘ₗ map f = map (g ∘ₗ f) := by
  let hPosition : ∀ tree, (map g ∘ₗ map f).toFunA tree =
      (map (g ∘ₗ f)).toFunA tree :=
    fun tree => congrArg Sigma.fst (map_obj_comp g f tree)
  refine Lens.ext _ _ hPosition ?_
  intro tree
  apply eq_of_heq
  have hraw : (map g ∘ₗ map f).toFunB tree ≍
      (map (g ∘ₗ f)).toFunB tree :=
    (Sigma.ext_iff.mp (map_obj_comp g f tree)).2
  have hcast : (hPosition tree ▸ (map (g ∘ₗ f)).toFunB tree) ≍
      (map (g ∘ₗ f)).toFunB tree :=
    eqRec_heq_self _ _
  exact hraw.trans hcast.symm

/-! ## Substitution-comonoid structure -/

/-- The counit selects the root vertex of an infinite tree. -/
def counit : Lens (CofreeP P) X.{max uA uB, max uA uB} where
  toFunA _ := PUnit.unit
  toFunB tree _ := .root tree

/-- Comultiplication exposes every rooted subtree. A nested pair of vertices
is pulled back by path concatenation. -/
def comult : Lens (CofreeP P) (CofreeP P ◃ CofreeP P) where
  toFunA tree := ⟨tree, M.Vertex.subtree⟩
  toFunB _ vertices := M.Vertex.append vertices.1 vertices.2

@[simp]
theorem counit_toFunB (tree : (CofreeP P).A)
    (direction : X.{max uA uB, max uA uB}.B
      ((counit (P := P)).toFunA tree)) :
    (counit (P := P)).toFunB tree direction = .root tree :=
  rfl

@[simp]
theorem comult_toFunA (tree : (CofreeP P).A) :
    (comult (P := P)).toFunA tree =
      ⟨tree, M.Vertex.subtree⟩ :=
  rfl

@[simp]
theorem comult_toFunB (tree : (CofreeP P).A)
    (vertices : (CofreeP P ◃ CofreeP P).B
      ((comult (P := P)).toFunA tree)) :
    (comult (P := P)).toFunB tree vertices =
      M.Vertex.append vertices.1 vertices.2 :=
  rfl

theorem comult_counit_left :
    Lens.Equiv.XComp.toLens ∘ₗ
        ((counit (P := P)) ◃ₗ Lens.id (CofreeP P)) ∘ₗ
      comult (P := P) =
    Lens.id (CofreeP P) :=
  rfl

/-- Pointwise container form of right counitality. -/
private theorem comult_counit_right_obj (tree : (CofreeP P).A) :
    let composite :=
      Lens.Equiv.compX.toLens ∘ₗ
          (Lens.id (CofreeP P) ◃ₗ counit (P := P)) ∘ₗ
        comult (P := P)
    (⟨composite.toFunA tree, composite.toFunB tree⟩ :
      (CofreeP P).Obj (M.Vertex tree)) = ⟨tree, id⟩ := by
  dsimp only
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext vertex
  exact M.Vertex.append_root_right vertex

theorem comult_counit_right :
    Lens.Equiv.compX.toLens ∘ₗ
        (Lens.id (CofreeP P) ◃ₗ counit (P := P)) ∘ₗ
      comult (P := P) =
    Lens.id (CofreeP P) := by
  ext tree
  · rfl
  · rename_i vertex
    exact M.Vertex.append_root_right vertex

/-- The left-associated composite of cofree-tree comultiplication. -/
private def comultAssocLeft :
    Lens (CofreeP P) (CofreeP P ◃ (CofreeP P ◃ CofreeP P)) :=
  Lens.Equiv.compAssoc.toLens ∘ₗ
      (comult (P := P) ◃ₗ Lens.id (CofreeP P)) ∘ₗ
    comult (P := P)

/-- The right-associated composite of cofree-tree comultiplication. -/
private def comultAssocRight :
    Lens (CofreeP P) (CofreeP P ◃ (CofreeP P ◃ CofreeP P)) :=
  (Lens.id (CofreeP P) ◃ₗ comult (P := P)) ∘ₗ comult (P := P)

/-- The left-associated two-level subtree object below a fixed first vertex. -/
private def comultAssocLeftAt {tree : M P} (first : M.Vertex tree) :
    (CofreeP P ◃ CofreeP P).Obj (M.Vertex tree) :=
  ⟨⟨M.Vertex.subtree first, fun second =>
      M.Vertex.subtree (M.Vertex.append first second)⟩,
    fun direction =>
      M.Vertex.append (M.Vertex.append first direction.1) direction.2⟩

/-- The right-associated two-level subtree object below a fixed first vertex. -/
private def comultAssocRightAt {tree : M P} (first : M.Vertex tree) :
    (CofreeP P ◃ CofreeP P).Obj (M.Vertex tree) :=
  ⟨⟨M.Vertex.subtree first, M.Vertex.subtree⟩,
    fun direction =>
      M.Vertex.append first
        (M.Vertex.append direction.1 direction.2)⟩

/-- Associativity below a fixed first vertex. Induction on that finite vertex
turns the child case into ordinary payload relabelling. -/
private theorem comult_assoc_at {tree : M P} : (first : M.Vertex tree) →
    comultAssocLeftAt first = comultAssocRightAt first
  | .root _ => rfl
  | .child direction next => by
      change
        (CofreeP P ◃ CofreeP P).map (M.Vertex.child direction)
            (comultAssocLeftAt next) =
          (CofreeP P ◃ CofreeP P).map (M.Vertex.child direction)
            (comultAssocRightAt next)
      exact congrArg
        ((CofreeP P ◃ CofreeP P).map (M.Vertex.child direction))
        (comult_assoc_at next)

/-- Assemble a three-level object from the two-level object below each first
vertex. -/
private def comultAssocNode (tree : M P)
    (below : (first : M.Vertex tree) →
      (CofreeP P ◃ CofreeP P).Obj α) :
    (CofreeP P ◃ (CofreeP P ◃ CofreeP P)).Obj α :=
  ⟨⟨tree, fun first => (below first).1⟩,
    fun direction => (below direction.1).2 direction.2⟩

/-- Pointwise container form of coassociativity. -/
private theorem comult_coassoc_obj (tree : M P) :
    (⟨(comultAssocLeft (P := P)).toFunA tree,
        (comultAssocLeft (P := P)).toFunB tree⟩ :
      (CofreeP P ◃ (CofreeP P ◃ CofreeP P)).Obj (M.Vertex tree)) =
    ⟨(comultAssocRight (P := P)).toFunA tree,
      (comultAssocRight (P := P)).toFunB tree⟩ := by
  change comultAssocNode tree comultAssocLeftAt =
    comultAssocNode tree comultAssocRightAt
  exact congrArg (comultAssocNode tree)
    (funext fun first => comult_assoc_at first)

/-- Cofree comultiplication is coassociative: selecting a subtree and then a
subtree inside it is the same as selecting the concatenated vertex. -/
theorem comult_coassoc :
    Lens.Equiv.compAssoc.toLens ∘ₗ
          (comult (P := P) ◃ₗ Lens.id (CofreeP P)) ∘ₗ
        comult (P := P) =
      (Lens.id (CofreeP P) ◃ₗ comult (P := P)) ∘ₗ
        comult (P := P) := by
  change comultAssocLeft (P := P) = comultAssocRight (P := P)
  let hA : ∀ tree, (comultAssocLeft (P := P)).toFunA tree =
      (comultAssocRight (P := P)).toFunA tree :=
    fun tree => congrArg Sigma.fst (comult_coassoc_obj tree)
  refine Lens.ext _ _ hA ?_
  intro tree
  apply eq_of_heq
  have hraw : (comultAssocLeft (P := P)).toFunB tree ≍
      (comultAssocRight (P := P)).toFunB tree :=
    (Sigma.ext_iff.mp (comult_coassoc_obj tree)).2
  have hcast :
      (hA tree ▸ (comultAssocRight (P := P)).toFunB tree) ≍
        (comultAssocRight (P := P)).toFunB tree := by
    rw [eqRec_heq_iff_heq]
  exact hraw.trans hcast.symm

/-- The cofree substitution comonoid generated by `P`. -/
def comonoid (P : PFunctor.{uA, uB}) :
    Comonoid.{max uA uB, max uA uB} where
  carrier := CofreeP P
  counit := counit
  comult := comult
  counit_left := comult_counit_left
  counit_right := comult_counit_right
  coassoc := comult_coassoc

@[simp]
theorem comonoid_carrier (P : PFunctor.{uA, uB}) :
    (comonoid P).carrier = CofreeP P :=
  rfl

@[simp]
theorem comonoid_counit (P : PFunctor.{uA, uB}) :
    (comonoid P).counit = counit :=
  rfl

@[simp]
theorem comonoid_comult (P : PFunctor.{uA, uB}) :
    (comonoid P).comult = comult :=
  rfl

/-! ## Functoriality of the cofree comonoid -/

private theorem cast_composite_direction {Q : PFunctor.{uA, uB}}
    (tree : M Q) {children children' : M.Vertex tree → M Q}
    (h : children = children') (vertex : M.Vertex tree)
    (next : M.Vertex (children vertex)) :
    cast (congrArg (CofreeP Q ◃ CofreeP Q).B
      (congrArg
        (fun current =>
          (⟨tree, current⟩ : (CofreeP Q ◃ CofreeP Q).A)) h))
      (⟨vertex, next⟩ : (CofreeP Q ◃ CofreeP Q).B ⟨tree, children⟩) =
    (⟨vertex, M.Vertex.castEquiv (congrFun h vertex) next⟩ :
      (CofreeP Q ◃ CofreeP Q).B ⟨tree, children'⟩) := by
  subst h
  rfl

/-- Mapping cofree trees along a generating lens preserves the root counit.
This theorem uses the common-generator-universe specialization chosen for
`mapHom`; the underlying `CofreeP.map` remains heterogeneous. -/
theorem map_counit {Q : PFunctor.{uA, uB}} (lens : Lens P Q) :
    (comonoid Q).counit ∘ₗ map lens = (comonoid P).counit := by
  ext tree
  · rfl
  · exact M.Vertex.pullMapLens_root lens tree

private theorem map_comult_obj {Q : PFunctor.{uA, uB}}
    (lens : Lens P Q) (tree : M P) :
    let left := (comonoid Q).comult ∘ₗ map lens
    let right := (map lens ◃ₗ map lens) ∘ₗ (comonoid P).comult
    (⟨left.toFunA tree, left.toFunB tree⟩ :
      (CofreeP Q ◃ CofreeP Q).Obj (M.Vertex tree)) =
    ⟨right.toFunA tree, right.toFunB tree⟩ := by
  dsimp only
  let hChildren :
      (fun vertex : M.Vertex (M.mapLens lens tree) =>
        M.Vertex.subtree vertex) =
      (fun vertex : M.Vertex (M.mapLens lens tree) =>
        M.mapLens lens
          (M.Vertex.subtree (M.Vertex.pullMapLens lens tree vertex))) := by
    funext vertex
    exact (M.Vertex.subtree_pullMapLens lens tree vertex).symm
  let hPosition :
      ((comonoid Q).comult ∘ₗ map lens).toFunA tree =
        ((map lens ◃ₗ map lens) ∘ₗ
          (comonoid P).comult).toFunA tree := by
    exact congrArg
      (fun current =>
        (⟨M.mapLens lens tree, current⟩ :
          (CofreeP Q ◃ CofreeP Q).A)) hChildren
  apply Sigma.ext hPosition
  apply Function.hfunext (congrArg (CofreeP Q ◃ CofreeP Q).B hPosition)
  intro leftDirection rightDirection hDirection
  have hcast :
      cast (congrArg (CofreeP Q ◃ CofreeP Q).B hPosition)
        leftDirection = rightDirection :=
    (cast_eq_iff_heq).2 hDirection
  change
    cast (congrArg (CofreeP Q ◃ CofreeP Q).B
      (congrArg
        (fun current =>
          (⟨M.mapLens lens tree, current⟩ :
            (CofreeP Q ◃ CofreeP Q).A)) hChildren))
      leftDirection = rightDirection at hcast
  let transportedNext :=
    M.Vertex.castEquiv (congrFun hChildren leftDirection.1)
      leftDirection.2
  let canonical :
      (CofreeP Q ◃ CofreeP Q).B
        ⟨M.mapLens lens tree,
          fun vertex => M.mapLens lens
            (M.Vertex.subtree
              (M.Vertex.pullMapLens lens tree vertex))⟩ :=
    ⟨leftDirection.1, transportedNext⟩
  have hcanonical :
      cast (congrArg (CofreeP Q ◃ CofreeP Q).B
        (congrArg
          (fun current =>
            (⟨M.mapLens lens tree, current⟩ :
              (CofreeP Q ◃ CofreeP Q).A)) hChildren))
        leftDirection = canonical :=
    cast_composite_direction (M.mapLens lens tree) hChildren
      leftDirection.1 leftDirection.2
  have hright : canonical = rightDirection := hcanonical.symm.trans hcast
  clear hDirection hcast hcanonical
  subst rightDirection
  dsimp only [canonical, transportedNext]
  rcases leftDirection with ⟨vertex, next⟩
  apply heq_of_eq
  change M.Vertex.pullMapLens lens tree (M.Vertex.append vertex next) =
    M.Vertex.append (M.Vertex.pullMapLens lens tree vertex)
      (M.Vertex.pullMapLens lens
        (M.Vertex.subtree (M.Vertex.pullMapLens lens tree vertex))
        (M.Vertex.castEquiv (congrFun hChildren vertex) next))
  rw [M.Vertex.pullMapLens_append]

/-- Mapping cofree trees along a generating lens preserves vertex
concatenation, hence cofree comultiplication. -/
theorem map_comult {Q : PFunctor.{uA, uB}} (lens : Lens P Q) :
    (comonoid Q).comult ∘ₗ map lens =
      (map lens ◃ₗ map lens) ∘ₗ (comonoid P).comult := by
  let hPosition : ∀ tree,
      ((comonoid Q).comult ∘ₗ map lens).toFunA tree =
        ((map lens ◃ₗ map lens) ∘ₗ
          (comonoid P).comult).toFunA tree :=
    fun tree => congrArg Sigma.fst (map_comult_obj lens tree)
  refine Lens.ext _ _ hPosition ?_
  intro tree
  apply eq_of_heq
  have hraw :
      ((comonoid Q).comult ∘ₗ map lens).toFunB tree ≍
        ((map lens ◃ₗ map lens) ∘ₗ
          (comonoid P).comult).toFunB tree :=
    (Sigma.ext_iff.mp (map_comult_obj lens tree)).2
  have htransport :
      (hPosition tree ▸
        ((map lens ◃ₗ map lens) ∘ₗ
          (comonoid P).comult).toFunB tree) ≍
        ((map lens ◃ₗ map lens) ∘ₗ
          (comonoid P).comult).toFunB tree :=
    eqRec_heq_self _ _
  exact hraw.trans htransport.symm

/-- The cofree-comonoid action on a generating lens. Unlike the underlying
heterogeneous `map`, this packaging currently chooses a common generator
universe pair, which makes the two `max` carrier universes definitionally
agree as required by `Comonoid.Hom`. A lifted or equal-maximum API could later
relax this specialization. -/
def mapHom {Q : PFunctor.{uA, uB}} (lens : Lens P Q) :
    Comonoid.Hom (comonoid P) (comonoid Q) where
  toLens := map lens
  map_counit := map_counit lens
  map_comult := map_comult lens

@[simp]
theorem mapHom_toLens {Q : PFunctor.{uA, uB}} (lens : Lens P Q) :
    (mapHom lens).toLens = map lens :=
  rfl

@[simp]
theorem mapHom_id :
    mapHom (Lens.id P) = Comonoid.Hom.id (comonoid P) :=
  Comonoid.Hom.ext _ _ map_id

@[simp]
theorem mapHom_comp {Q R : PFunctor.{uA, uB}}
    (f : Lens P Q) (g : Lens Q R) :
    (mapHom f).comp (mapHom g) = mapHom (g ∘ₗ f) :=
  Comonoid.Hom.ext _ _ (map_comp g f)

end CofreeP
end PFunctor
