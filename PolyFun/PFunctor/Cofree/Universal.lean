/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.Polynomial
public import PolyFun.PFunctor.Comonoid.Category

/-!
# The universal property of the cofree polynomial comonoid

For a polynomial `P`, the cofree comonoid `CofreeP.comonoid P` is right
adjoint to the carrier-forgetful functor from polynomial comonoids.  Concretely,
a lens from a comonoid carrier to `P` extends uniquely to a retrofunctor into
the cofree comonoid.

This file packages the adjunction at the hom-set level.  It does not install a
bundled `CategoryTheory.Adjunction`: `PFunctor` currently has overlapping lens
and chart category instances, whereas the concrete hom-set equivalence is
unambiguous and is the API needed by downstream dynamical systems. Generic
coiteration remains universe-polymorphic; only the retrofunctor packaging uses
the common-maximum universe boundary currently required by `Comonoid.Hom`.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uCA uCB

namespace PFunctor
namespace CofreeP

variable {P : PFunctor.{uA, uB}}

/-! ## Cogeneration and coiteration -/

/-- The one-layer projection from the cofree polynomial to its generator.
It exposes the root position and pulls a generator direction back to the
corresponding depth-one vertex.  This is `ε_P^{(1)}` in Spivak--Niu. -/
def cogenerator (P : PFunctor.{uA, uB}) : Lens (CofreeP P) P where
  toFunA := M.head
  toFunB tree direction :=
    .child direction (.root (M.children tree direction))

@[simp]
theorem cogenerator_toFunA (tree : M P) :
    (cogenerator P).toFunA tree = M.head tree :=
  rfl

@[simp]
theorem cogenerator_toFunB (tree : M P)
    (direction : P.B ((cogenerator P).toFunA tree)) :
    (cogenerator P).toFunB tree direction =
      .child direction (.root (M.children tree direction)) :=
  rfl

/-- The cofree generator projection is natural with respect to a generating
lens, across independent source and target generator universes. -/
@[simp]
theorem cogenerator_comp_map {Q : PFunctor.{uA₂, uB₂}}
    (lens : Lens P Q) :
    cogenerator Q ∘ₗ map lens = lens ∘ₗ cogenerator P := by
  let hA : ∀ tree,
      (cogenerator Q ∘ₗ map lens).toFunA tree =
        (lens ∘ₗ cogenerator P).toFunA tree :=
    M.head_mapLens lens
  refine Lens.ext _ _ hA ?_
  intro tree
  have hhead := M.head_mapLens lens tree
  cases hhead
  have hproof : hA tree = rfl := Subsingleton.elim _ _
  rw [hproof]
  funext direction
  dsimp only [Lens.comp, cogenerator, map]
  change M.Vertex.pullMapLens lens tree
      (.child direction
        (.root (M.children (M.mapLens lens tree) direction))) =
    .child (lens.toFunB (M.head tree) direction)
      (.root (M.children tree
        (lens.toFunB (M.head tree) direction)))
  rw [M.Vertex.pullMapLens_child,
    M.Vertex.cast_root (M.children_mapLens lens tree direction),
    M.Vertex.pullMapLens_root]
  rfl

/-! ## The outgoing category of the cofree comonoid -/

/-- The categorical identity of a cofree tree is its root vertex. -/
@[simp]
theorem comonoid_identity (tree : M P) :
    Comonoid.identity (comonoid P) tree = .root tree :=
  rfl

/-- The categorical target of a cofree vertex is its selected subtree. -/
@[simp]
theorem comonoid_target (tree : M P) (vertex : M.Vertex tree) :
    Comonoid.target (comonoid P) tree vertex =
      M.Vertex.subtree vertex :=
  rfl

/-- Categorical composition in the cofree comonoid is finite-vertex
concatenation, in outer-then-inner path order. -/
@[simp]
theorem comonoid_compose (tree : M P) (first : M.Vertex tree)
    (second : M.Vertex (M.Vertex.subtree first)) :
    Comonoid.compose (comonoid P) tree first second =
      M.Vertex.append first second :=
  rfl

variable (C : Comonoid.{uCA, uCB})

/-- The cofree tree generated from an object of `C` by repeatedly applying
the chosen generator lens. -/
def unfoldShape (lens : Lens C.carrier P) (object : C.carrier.A) : M P :=
  M.corec
    (fun current =>
      ⟨lens.toFunA current, fun direction =>
        Comonoid.target C current (lens.toFunB current direction)⟩)
    object

/-- One-step unfolding of the coiterated shape. -/
theorem dest_unfoldShape (lens : Lens C.carrier P)
    (object : C.carrier.A) :
    M.dest (unfoldShape C lens object) =
      ⟨lens.toFunA object, fun direction =>
        unfoldShape C lens
          (Comonoid.target C object
            (lens.toFunB object direction))⟩ := by
  simpa only [unfoldShape] using
    M.dest_corec_apply
      (fun current =>
        ⟨lens.toFunA current, fun direction =>
          Comonoid.target C current (lens.toFunB current direction)⟩)
      object

/-- The root position of a coiterated tree is the position exposed by the
generator lens. -/
theorem head_unfoldShape (lens : Lens C.carrier P) (object : C.carrier.A) :
    M.head (unfoldShape C lens object) = lens.toFunA object :=
  congrArg Sigma.fst (dest_unfoldShape C lens object)

/-- Pull a root direction of a coiterated tree back to the corresponding
outgoing arrow of `C`. -/
def unfoldRootDirection (lens : Lens C.carrier P)
    (object : C.carrier.A)
    (direction : P.B (M.head (unfoldShape C lens object))) :
    C.carrier.B object :=
  lens.toFunB object
    (cast (congrArg P.B (head_unfoldShape C lens object)) direction)

/-- Selecting a child of a coiterated tree continues coiteration from the
target of the pulled-back arrow. -/
theorem children_unfoldShape (lens : Lens C.carrier P)
    (object : C.carrier.A)
    (direction : P.B (M.head (unfoldShape C lens object))) :
    M.children (unfoldShape C lens object) direction =
      unfoldShape C lens
        (Comonoid.target C object
          (unfoldRootDirection C lens object direction)) := by
  have h := M.dest_corec_apply
    (fun current =>
      ⟨lens.toFunA current, fun currentDirection =>
        Comonoid.target C current
          (lens.toFunB current currentDirection)⟩)
    object
  have hA := congrArg Sigma.fst h
  have hB := (Sigma.ext_iff.mp h).2
  cases hA
  exact congrFun (eq_of_heq hB) direction

/-- Pull a finite vertex of a coiterated tree back to the composite outgoing
arrow of `C` represented by that path. -/
def unfoldDirection (lens : Lens C.carrier P) :
    (object : C.carrier.A) →
      M.Vertex (unfoldShape C lens object) → C.carrier.B object
  | object, .root _ => Comonoid.identity C object
  | object, .child direction next =>
      let first := unfoldRootDirection C lens object direction
      let childEq := children_unfoldShape C lens object direction
      Comonoid.compose C object first
        (unfoldDirection lens
          (Comonoid.target C object first)
          (M.Vertex.castEquiv childEq next))
termination_by _ vertex => M.Vertex.depth vertex
decreasing_by
  calc
    M.Vertex.depth (M.Vertex.castEquiv childEq next) =
        M.Vertex.depth next := M.Vertex.depth_cast childEq next
    _ < M.Vertex.depth (.child direction next) := Nat.lt_succ_self _

@[simp]
theorem unfoldDirection_root (lens : Lens C.carrier P)
    (object : C.carrier.A) :
    unfoldDirection C lens object (.root (unfoldShape C lens object)) =
      Comonoid.identity C object := by
  rw [unfoldDirection.eq_def]

/-- Pulling back a child vertex first selects the root arrow and then composes
it with the recursively pulled-back arrow in the selected subtree. -/
theorem unfoldDirection_child (lens : Lens C.carrier P)
    (object : C.carrier.A)
    (direction : P.B (M.head (unfoldShape C lens object)))
    (next : M.Vertex
      (M.children (unfoldShape C lens object) direction)) :
    unfoldDirection C lens object (.child direction next) =
      Comonoid.compose C object
        (unfoldRootDirection C lens object direction)
        (unfoldDirection C lens
          (Comonoid.target C object
            (unfoldRootDirection C lens object direction))
          (M.Vertex.castEquiv
            (children_unfoldShape C lens object direction) next)) := by
  rw [unfoldDirection.eq_def]

private theorem unfoldDirection_heq (lens : Lens C.carrier P)
    {object object' : C.carrier.A} (hobject : object = object')
    {vertex : M.Vertex (unfoldShape C lens object)}
    {vertex' : M.Vertex (unfoldShape C lens object')}
    (hvertex : vertex ≍ vertex') :
    unfoldDirection C lens object vertex ≍
      unfoldDirection C lens object' vertex' := by
  subst object'
  cases hvertex
  rfl

private theorem unfoldDirection_cast_object (lens : Lens C.carrier P)
    {object object' : C.carrier.A} (hobject : object = object')
    (vertex : M.Vertex (unfoldShape C lens object)) :
    unfoldDirection C lens object'
        (M.Vertex.castEquiv
          (congrArg (unfoldShape C lens) hobject) vertex) =
      cast (congrArg C.carrier.B hobject)
        (unfoldDirection C lens object vertex) := by
  subst object'
  rfl

/-- The subtree selected by a coiterated vertex is the coiteration started at
the target of the corresponding composite arrow. -/
theorem subtree_unfoldShape (lens : Lens C.carrier P) :
    (object : C.carrier.A) →
      (vertex : M.Vertex (unfoldShape C lens object)) →
      M.Vertex.subtree vertex =
        unfoldShape C lens
          (Comonoid.target C object
            (unfoldDirection C lens object vertex))
  | object, .root _ => by
      rw [unfoldDirection_root, Comonoid.target_identity]
      rfl
  | object, .child direction next => by
      let first := unfoldRootDirection C lens object direction
      let childEq := children_unfoldShape C lens object direction
      let next' := M.Vertex.castEquiv childEq next
      let rest := unfoldDirection C lens
        (Comonoid.target C object first) next'
      have ih := subtree_unfoldShape lens
        (Comonoid.target C object first) next'
      have hsub : M.Vertex.subtree next' = M.Vertex.subtree next :=
        M.Vertex.subtree_cast childEq next
      rw [unfoldDirection_child]
      change M.Vertex.subtree next =
        unfoldShape C lens
          (Comonoid.target C object
            (Comonoid.compose C object first rest))
      calc
        M.Vertex.subtree next = M.Vertex.subtree next' := hsub.symm
        _ = unfoldShape C lens
            (Comonoid.target C
              (Comonoid.target C object first) rest) := ih
        _ = unfoldShape C lens
            (Comonoid.target C object
              (Comonoid.compose C object first rest)) := by
          rw [Comonoid.target_compose]
termination_by _ vertex => M.Vertex.depth vertex
decreasing_by
  calc
    M.Vertex.depth next' = M.Vertex.depth next :=
      M.Vertex.depth_cast childEq next
    _ < M.Vertex.depth (.child direction next) := Nat.lt_succ_self _

private theorem vertex_cast_append {tree tree' : M P} (h : tree = tree')
    (initial : M.Vertex tree)
    (suffix : M.Vertex (M.Vertex.subtree initial)) :
    M.Vertex.castEquiv h (M.Vertex.append initial suffix) =
      M.Vertex.append (M.Vertex.castEquiv h initial)
        (M.Vertex.castEquiv
          (M.Vertex.subtree_cast h initial).symm suffix) := by
  subst tree'
  rfl

private theorem compose_heq (object : C.carrier.A)
    {first first' : C.carrier.B object} (hfirst : first ≍ first')
    {second : C.carrier.B (Comonoid.target C object first)}
    {second' : C.carrier.B (Comonoid.target C object first')}
    (hsecond : second ≍ second') :
    Comonoid.compose C object first second =
      Comonoid.compose C object first' second' := by
  cases hfirst
  cases hsecond
  rfl

/-- Pulling back a concatenated cofree vertex composes the arrows represented
by its prefix and suffix, in outer-then-inner path order. The suffix is
transported from the selected subtree to the propositionally equal coiterated
tree at the prefix target. -/
theorem unfoldDirection_append (lens : Lens C.carrier P) :
    (object : C.carrier.A) →
      (initial : M.Vertex (unfoldShape C lens object)) →
      (suffix : M.Vertex (M.Vertex.subtree initial)) →
      unfoldDirection C lens object (M.Vertex.append initial suffix) =
        Comonoid.compose C object
          (unfoldDirection C lens object initial)
          (unfoldDirection C lens
            (Comonoid.target C object
              (unfoldDirection C lens object initial))
            (M.Vertex.castEquiv
              (subtree_unfoldShape C lens object initial) suffix))
  | object, .root _, suffix => by
      let actualDirection := unfoldDirection C lens object
        (.root (unfoldShape C lens object))
      let actualTarget := Comonoid.target C object actualDirection
      let actualVertex := M.Vertex.castEquiv
        (subtree_unfoldShape C lens object
          (.root (unfoldShape C lens object))) suffix
      let identityTarget :=
        Comonoid.target C object (Comonoid.identity C object)
      let canonicalVertex := M.Vertex.castEquiv
        (congrArg (unfoldShape C lens)
          (Comonoid.target_identity C object).symm) suffix
      have hdirection : actualDirection = Comonoid.identity C object :=
        unfoldDirection_root C lens object
      have htarget : actualTarget = identityTarget :=
        congrArg (Comonoid.target C object) hdirection
      have hvertex : actualVertex ≍ canonicalVertex :=
        (cast_heq _ suffix).trans (cast_heq _ suffix).symm
      have htail :
          unfoldDirection C lens actualTarget actualVertex ≍
            unfoldDirection C lens identityTarget canonicalVertex :=
        unfoldDirection_heq C lens htarget hvertex
      have hcanonical :
          unfoldDirection C lens identityTarget canonicalVertex =
            cast (congrArg C.carrier.B
              (Comonoid.target_identity C object).symm)
              (unfoldDirection C lens object suffix) :=
        unfoldDirection_cast_object C lens
          (Comonoid.target_identity C object).symm suffix
      have hcompose :
          Comonoid.compose C object actualDirection
              (unfoldDirection C lens actualTarget actualVertex) =
            Comonoid.compose C object (Comonoid.identity C object)
              (unfoldDirection C lens identityTarget canonicalVertex) :=
        compose_heq C object (heq_of_eq hdirection) htail
      simp only [M.Vertex.append_root]
      exact (hcompose.trans (by
        rw [hcanonical]
        exact Comonoid.identity_compose C object
          (unfoldDirection C lens object suffix))).symm
  | object, .child direction next, suffix => by
      let first := unfoldRootDirection C lens object direction
      let childEq :
          M.children (unfoldShape C lens object) direction =
            unfoldShape C lens (Comonoid.target C object first) := by
        simpa only [first] using
          children_unfoldShape C lens object direction
      let next' := M.Vertex.castEquiv childEq next
      let subtreeEq := M.Vertex.subtree_cast childEq next
      let suffix' := M.Vertex.castEquiv subtreeEq.symm suffix
      let rest := unfoldDirection C lens
        (Comonoid.target C object first) next'
      let final := Comonoid.target C
        (Comonoid.target C object first) rest
      let finalVertex := M.Vertex.castEquiv
        (subtree_unfoldShape C lens
          (Comonoid.target C object first) next') suffix'
      have ih := unfoldDirection_append lens
        (Comonoid.target C object first) next' suffix'
      let compositeTarget :=
        Comonoid.target C object (Comonoid.compose C object first rest)
      let compositeSubtreeEq :
          M.Vertex.subtree (.child direction next) =
            unfoldShape C lens compositeTarget := by
        simpa only [unfoldDirection_child] using
          subtree_unfoldShape C lens object (.child direction next)
      let compositeVertex := M.Vertex.castEquiv compositeSubtreeEq suffix
      have htarget : compositeTarget = final :=
        Comonoid.target_compose C object first rest
      have hvertices : compositeVertex ≍ finalVertex := by
        have hcomposite : compositeVertex ≍ suffix :=
          by
            unfold compositeVertex M.Vertex.castEquiv
            exact cast_heq (congrArg M.Vertex compositeSubtreeEq) suffix
        have hfinal : finalVertex ≍ suffix' :=
          by
            unfold finalVertex M.Vertex.castEquiv
            exact cast_heq (congrArg M.Vertex
              (subtree_unfoldShape C lens
                (Comonoid.target C object first) next')) suffix'
        have hsuffix : suffix' ≍ suffix :=
          by
            unfold suffix' M.Vertex.castEquiv
            exact cast_heq (congrArg M.Vertex subtreeEq.symm) suffix
        exact hcomposite.trans (hfinal.trans hsuffix).symm
      have harrows :
          unfoldDirection C lens compositeTarget compositeVertex ≍
            unfoldDirection C lens final finalVertex :=
        unfoldDirection_heq C lens htarget hvertices
      have htail :
          unfoldDirection C lens compositeTarget compositeVertex =
            cast (congrArg C.carrier.B htarget.symm)
              (unfoldDirection C lens final finalVertex) := by
        apply eq_of_heq
        exact harrows.trans
          (cast_heq (congrArg C.carrier.B htarget.symm)
            (unfoldDirection C lens final finalVertex)).symm
      have hnormalized :
          unfoldDirection C lens object
              (M.Vertex.append (.child direction next) suffix) =
            Comonoid.compose C object
              (Comonoid.compose C object first rest)
              (unfoldDirection C lens compositeTarget compositeVertex) := by
        calc
          unfoldDirection C lens object
              (M.Vertex.append (.child direction next) suffix) =
              Comonoid.compose C object first
                (unfoldDirection C lens
                  (Comonoid.target C object first)
                  (M.Vertex.castEquiv childEq
                    (M.Vertex.append next suffix))) := by
            rw [M.Vertex.append_child, unfoldDirection_child]
          _ = Comonoid.compose C object first
                (Comonoid.compose C (Comonoid.target C object first) rest
                  (unfoldDirection C lens final finalVertex)) := by
            rw [vertex_cast_append childEq next suffix, ih]
          _ = Comonoid.compose C object
                (Comonoid.compose C object first rest)
                (cast (congrArg C.carrier.B htarget.symm)
                  (unfoldDirection C lens final finalVertex)) :=
            (Comonoid.compose_assoc C object first rest
              (unfoldDirection C lens final finalVertex)).symm
          _ = Comonoid.compose C object
                (Comonoid.compose C object first rest)
                (unfoldDirection C lens compositeTarget compositeVertex) := by
            rw [htail]
      let actualDirection :=
        unfoldDirection C lens object (.child direction next)
      let actualTarget := Comonoid.target C object actualDirection
      let actualVertex := M.Vertex.castEquiv
        (subtree_unfoldShape C lens object (.child direction next)) suffix
      have hdirection :
          actualDirection = Comonoid.compose C object first rest := by
        simpa only [actualDirection, first, rest, next', childEq] using
          unfoldDirection_child C lens object direction next
      have hactualTarget : actualTarget = compositeTarget :=
        congrArg (Comonoid.target C object) hdirection
      have hactualVertex : actualVertex ≍ compositeVertex := by
        exact (cast_heq _ suffix).trans (cast_heq _ suffix).symm
      have hactualTail :
          unfoldDirection C lens actualTarget actualVertex ≍
            unfoldDirection C lens compositeTarget compositeVertex :=
        unfoldDirection_heq C lens hactualTarget hactualVertex
      calc
        unfoldDirection C lens object
            (M.Vertex.append (.child direction next) suffix) =
            Comonoid.compose C object
              (Comonoid.compose C object first rest)
              (unfoldDirection C lens compositeTarget compositeVertex) :=
          hnormalized
        _ = Comonoid.compose C object actualDirection
              (unfoldDirection C lens actualTarget actualVertex) :=
          compose_heq C object (heq_of_eq hdirection.symm) hactualTail.symm
  termination_by _ initial _ => M.Vertex.depth initial
  decreasing_by
    calc
      M.Vertex.depth next' = M.Vertex.depth next :=
        M.Vertex.depth_cast childEq next
      _ < M.Vertex.depth (.child direction next) := Nat.lt_succ_self _

/-- The carrier lens obtained by coiteration. -/
def unfoldLens (lens : Lens C.carrier P) :
    Lens C.carrier (CofreeP P) where
  toFunA := unfoldShape C lens
  toFunB := unfoldDirection C lens

@[simp]
theorem unfoldLens_toFunA (lens : Lens C.carrier P)
    (object : C.carrier.A) :
    (unfoldLens C lens).toFunA object = unfoldShape C lens object :=
  rfl

@[simp]
theorem unfoldLens_toFunB (lens : Lens C.carrier P)
    (object : C.carrier.A)
    (vertex : M.Vertex ((unfoldLens C lens).toFunA object)) :
    (unfoldLens C lens).toFunB object vertex =
      unfoldDirection C lens object vertex :=
  rfl

/-! ## Universal extension and restriction -/

/-- Restrict a retrofunctor into the cofree comonoid to its one-layer
generator lens. -/
def restrict
    (C : Comonoid.{max uA uB, max uA uB})
    (hom : Comonoid.Hom C (comonoid P)) : Lens C.carrier P :=
  cogenerator P ∘ₗ hom.toLens

/-- Extend a generator lens uniquely along the cofree polynomial comonoid at
the level of retrofunctor data. -/
def extend
    (C : Comonoid.{max uA uB, max uA uB})
    (lens : Lens C.carrier P) : Comonoid.Hom C (comonoid P) :=
  Comonoid.Hom.ofCategoryLaws (unfoldLens C lens)
    (fun object => by
      change unfoldDirection C lens object
          (.root (unfoldShape C lens object)) =
        Comonoid.identity C object
      exact unfoldDirection_root C lens object)
    (fun object vertex => by
      change unfoldShape C lens
          (Comonoid.target C object
            (unfoldDirection C lens object vertex)) =
        M.Vertex.subtree vertex
      exact (subtree_unfoldShape C lens object vertex).symm)
    (fun object initial suffix => by
      change unfoldDirection C lens object
          (M.Vertex.append initial suffix) =
        Comonoid.compose C object
          (unfoldDirection C lens object initial)
          (unfoldDirection C lens
            (Comonoid.target C object
              (unfoldDirection C lens object initial))
            (M.Vertex.castEquiv
              (subtree_unfoldShape C lens object initial) suffix))
      exact unfoldDirection_append C lens object initial suffix)

@[simp]
theorem extend_toLens
    (C : Comonoid.{max uA uB, max uA uB})
    (lens : Lens C.carrier P) :
    (extend C lens).toLens = unfoldLens C lens :=
  rfl

/-- Coiteration is split by the one-layer cogenerator. -/
@[simp]
theorem cogenerator_comp_unfoldLens (lens : Lens C.carrier P) :
    cogenerator P ∘ₗ unfoldLens C lens = lens := by
  let hA : ∀ object,
      (cogenerator P ∘ₗ unfoldLens C lens).toFunA object =
        lens.toFunA object :=
    head_unfoldShape C lens
  refine Lens.ext _ _ hA ?_
  intro object
  have hhead := head_unfoldShape C lens object
  cases hhead
  have hproof : hA object = rfl := Subsingleton.elim _ _
  rw [hproof]
  funext direction
  dsimp only [Lens.comp, unfoldLens, cogenerator]
  change unfoldDirection C lens object
      (.child direction
        (.root (M.children (unfoldShape C lens object) direction))) =
    lens.toFunB object direction
  rw [unfoldDirection_child,
    M.Vertex.cast_root (children_unfoldShape C lens object direction),
    unfoldDirection_root,
    Comonoid.compose_identity_right]
  rfl

/-- Restricting a cofree extension recovers its generator lens. -/
@[simp]
theorem restrict_extend
    (C : Comonoid.{max uA uB, max uA uB})
    (lens : Lens C.carrier P) :
    restrict C (extend C lens) = lens :=
  cogenerator_comp_unfoldLens C lens

private theorem hom_target_oneLayer
    (C : Comonoid.{max uA uB, max uA uB})
    (hom : Comonoid.Hom C (comonoid P))
    (object : C.carrier.A)
    (direction : P.B (M.head (hom.toLens.toFunA object))) :
    hom.toLens.toFunA
        (Comonoid.target C object
          (hom.toLens.toFunB object
            (.child direction
              (.root (M.children
                (hom.toLens.toFunA object) direction))))) =
      M.children (hom.toLens.toFunA object) direction := by
  simpa only [comonoid_target, M.Vertex.subtree_child,
    M.Vertex.subtree_root] using
    hom.map_target object
      (.child direction
        (.root (M.children (hom.toLens.toFunA object) direction)))

/-- The object map of a retrofunctor into the cofree comonoid is the
coiteration of its restriction to one-layer generators. -/
theorem unfoldShape_restrict
    (C : Comonoid.{max uA uB, max uA uB})
    (hom : Comonoid.Hom C (comonoid P))
    (object : C.carrier.A) :
    unfoldShape C (restrict C hom) object = hom.toLens.toFunA object := by
  conv_rhs => rw [← M.corec_dest (hom.toLens.toFunA object)]
  refine M.corec_eq_corec
    (fun current =>
      ⟨(restrict C hom).toFunA current, fun direction =>
        Comonoid.target C current
          ((restrict C hom).toFunB current direction)⟩)
    M.dest
    (fun source tree => hom.toLens.toFunA source = tree)
    object (hom.toLens.toFunA object) rfl ?_
  rintro source _ rfl
  let tree := hom.toLens.toFunA source
  refine ⟨M.head tree,
    fun direction =>
      Comonoid.target C source
        ((restrict C hom).toFunB source direction),
    fun direction => M.children tree direction, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro direction
    exact hom_target_oneLayer C hom source direction

private theorem homDirection_heq
    (C : Comonoid.{max uA uB, max uA uB})
    (hom : Comonoid.Hom C (comonoid P))
    {object object' : C.carrier.A} (hobject : object = object')
    {vertex : M.Vertex (hom.toLens.toFunA object)}
    {vertex' : M.Vertex (hom.toLens.toFunA object')}
    (hvertex : vertex ≍ vertex') :
    hom.toLens.toFunB object vertex ≍
      hom.toLens.toFunB object' vertex' := by
  subst object'
  cases hvertex
  rfl

/-- Pulling a coiterated vertex back through the restricted generator lens
recovers the original retrofunctor's pullback of the corresponding vertex. -/
private theorem unfoldDirection_restrict
    (C : Comonoid.{max uA uB, max uA uB})
    (hom : Comonoid.Hom C (comonoid P)) :
    (object : C.carrier.A) →
      (vertex : M.Vertex (unfoldShape C (restrict C hom) object)) →
      unfoldDirection C (restrict C hom) object vertex =
        hom.toLens.toFunB object
          (M.Vertex.castEquiv
            (unfoldShape_restrict C hom object) vertex)
  | object, .root _ => by
      have hcast :
          M.Vertex.castEquiv
            (unfoldShape_restrict C hom object)
              (.root (unfoldShape C (restrict C hom) object)) =
            .root (hom.toLens.toFunA object) :=
        M.Vertex.cast_root (unfoldShape_restrict C hom object)
      calc
        unfoldDirection C (restrict C hom) object
            (.root (unfoldShape C (restrict C hom) object)) =
            Comonoid.identity C object :=
          unfoldDirection_root C (restrict C hom) object
        _ = hom.toLens.toFunB object
              (.root (hom.toLens.toFunA object)) := by
          simpa only [comonoid_identity] using
            (hom.map_identity object).symm
        _ = hom.toLens.toFunB object
              (M.Vertex.castEquiv
                (unfoldShape_restrict C hom object)
                (.root (unfoldShape C (restrict C hom) object))) :=
          congrArg (hom.toLens.toFunB object) hcast.symm
  | object, .child direction next => by
      let shapeEq := unfoldShape_restrict C hom object
      let mappedDirection := M.castDirection shapeEq direction
      let mappedNext := M.Vertex.castEquiv
        (M.children_castDirection shapeEq direction) next
      let firstVertex : M.Vertex (hom.toLens.toFunA object) :=
        .child mappedDirection
          (.root (M.children (hom.toLens.toFunA object) mappedDirection))
      let rootDirection :=
        unfoldRootDirection C (restrict C hom) object direction
      let first := hom.toLens.toFunB object firstVertex
      have hfirst : rootDirection = first := by
        rfl
      let childEq := children_unfoldShape C (restrict C hom) object direction
      let nativeNext := M.Vertex.castEquiv childEq next
      let nextObject := Comonoid.target C object rootDirection
      let rest := unfoldDirection C (restrict C hom) nextObject nativeNext
      have ih := unfoldDirection_restrict
        (C := C) hom nextObject nativeNext
      let ihVertex := M.Vertex.castEquiv
        (unfoldShape_restrict C hom nextObject) nativeNext
      let homNext := M.Vertex.castEquiv
        (hom.map_target object firstVertex).symm mappedNext
      let homNextObject := Comonoid.target C object first
      have hnextObject : nextObject = homNextObject :=
        congrArg (Comonoid.target C object) hfirst
      have hvertices : ihVertex ≍ homNext := by
        have hih : ihVertex ≍ nativeNext := by
          unfold ihVertex M.Vertex.castEquiv
          exact cast_heq (congrArg M.Vertex
            (unfoldShape_restrict C hom nextObject)) nativeNext
        have hnative : nativeNext ≍ next := by
          unfold nativeNext M.Vertex.castEquiv
          exact cast_heq (congrArg M.Vertex childEq) next
        have hmapped : mappedNext ≍ next := by
          unfold mappedNext M.Vertex.castEquiv
          exact cast_heq (congrArg M.Vertex
            (M.children_castDirection shapeEq direction)) next
        have hhom : homNext ≍ mappedNext := by
          unfold homNext M.Vertex.castEquiv
          exact cast_heq (congrArg M.Vertex
            (hom.map_target object firstVertex).symm) mappedNext
        exact (hih.trans hnative).trans (hhom.trans hmapped).symm
      have hhomDirections :
          hom.toLens.toFunB nextObject ihVertex ≍
            hom.toLens.toFunB homNextObject homNext :=
        homDirection_heq C hom hnextObject hvertices
      have hrest : rest ≍ hom.toLens.toFunB homNextObject homNext :=
        (heq_of_eq ih).trans hhomDirections
      have hcompose :
          Comonoid.compose C object rootDirection rest =
            Comonoid.compose C object first
              (hom.toLens.toFunB homNextObject homNext) :=
        compose_heq C object (heq_of_eq hfirst) hrest
      have hmap :
          hom.toLens.toFunB object
              (M.Vertex.append firstVertex mappedNext) =
            Comonoid.compose C object first
              (hom.toLens.toFunB homNextObject homNext) := by
        let rawNext := cast (congrArg (comonoid P).carrier.B
          (hom.map_target object firstVertex).symm) mappedNext
        have hraw :
            hom.toLens.toFunB object
                (M.Vertex.append firstVertex mappedNext) =
              Comonoid.compose C object
                (hom.toLens.toFunB object firstVertex)
                (hom.toLens.toFunB
                  (Comonoid.target C object
                    (hom.toLens.toFunB object firstVertex)) rawNext) := by
          simpa only [comonoid_compose, rawNext] using
            hom.map_compose object firstVertex mappedNext
        have hrawVertices : rawNext ≍ homNext :=
          (cast_heq _ mappedNext).trans (cast_heq _ mappedNext).symm
        have hrawDirections :
            hom.toLens.toFunB
                (Comonoid.target C object
                  (hom.toLens.toFunB object firstVertex)) rawNext ≍
              hom.toLens.toFunB homNextObject homNext :=
          homDirection_heq C hom rfl hrawVertices
        exact hraw.trans
          (compose_heq C object (heq_of_eq rfl) hrawDirections)
      have hmappedVertex :
          M.Vertex.castEquiv shapeEq (.child direction next) =
            M.Vertex.append firstVertex mappedNext := by
        rw [M.Vertex.cast_child]
        rfl
      calc
        unfoldDirection C (restrict C hom) object
            (.child direction next) =
            Comonoid.compose C object rootDirection rest := by
          rw [unfoldDirection_child]
        _ = Comonoid.compose C object first
              (hom.toLens.toFunB homNextObject homNext) := hcompose
        _ = hom.toLens.toFunB object
              (M.Vertex.append firstVertex mappedNext) := hmap.symm
        _ = hom.toLens.toFunB object
              (M.Vertex.castEquiv shapeEq (.child direction next)) := by
          exact congrArg (hom.toLens.toFunB object) hmappedVertex.symm
  termination_by _ vertex => M.Vertex.depth vertex
  decreasing_by
    calc
      M.Vertex.depth nativeNext = M.Vertex.depth next :=
        M.Vertex.depth_cast childEq next
      _ < M.Vertex.depth (.child direction next) := Nat.lt_succ_self _

/-- Extending the restriction of a retrofunctor into the cofree polynomial
comonoid recovers the original retrofunctor. -/
@[simp]
theorem extend_restrict
    (C : Comonoid.{max uA uB, max uA uB})
    (hom : Comonoid.Hom C (comonoid P)) :
    extend C (restrict C hom) = hom := by
  apply Comonoid.Hom.ext
  let hA : ∀ object,
      (extend C (restrict C hom)).toLens.toFunA object =
        hom.toLens.toFunA object :=
    unfoldShape_restrict C hom
  refine Lens.ext _ _ hA ?_
  intro object
  apply eq_of_heq
  have hraw :
      (extend C (restrict C hom)).toLens.toFunB object ≍
        hom.toLens.toFunB object := by
    apply Function.hfunext (congrArg M.Vertex (hA object))
    intro vertex vertex' hvertex
    have hcast :
        M.Vertex.castEquiv (hA object) vertex = vertex' :=
      (cast_eq_iff_heq).2 hvertex
    subst vertex'
    apply heq_of_eq
    exact unfoldDirection_restrict C hom object vertex
  have htransport :
      (hA object ▸ hom.toLens.toFunB object) ≍
        hom.toLens.toFunB object :=
    eqRec_heq_self _ _
  exact hraw.trans htransport.symm

/-- The cofree polynomial comonoid's universal property as an equivalence
between retrofunctors into it and lenses into its generator polynomial. -/
def homEquiv
    (C : Comonoid.{max uA uB, max uA uB}) :
    Comonoid.Hom C (comonoid P) ≃ Lens C.carrier P where
  toFun := restrict C
  invFun := extend C
  left_inv := extend_restrict C
  right_inv := restrict_extend C

/-- The cofree hom-set equivalence is natural in its source comonoid. -/
theorem homEquiv_naturality_left
    {C₁ C₂ : Comonoid.{max uA uB, max uA uB}}
    (pre : Comonoid.Hom C₁ C₂)
    (hom : Comonoid.Hom C₂ (comonoid P)) :
    homEquiv (P := P) C₁ (pre.comp hom) =
      homEquiv (P := P) C₂ hom ∘ₗ pre.toLens := by
  change cogenerator P ∘ₗ (hom.toLens ∘ₗ pre.toLens) =
    (cogenerator P ∘ₗ hom.toLens) ∘ₗ pre.toLens
  exact (Lens.comp_assoc (cogenerator P) hom.toLens pre.toLens).symm

/-- The cofree hom-set equivalence is natural in its generator polynomial. -/
theorem homEquiv_naturality_right
    {Q : PFunctor.{uA, uB}}
    (C : Comonoid.{max uA uB, max uA uB})
    (lens : Lens P Q)
    (hom : Comonoid.Hom C (comonoid P)) :
    homEquiv (P := Q) C (hom.comp (mapHom lens)) =
      lens ∘ₗ homEquiv (P := P) C hom := by
  change cogenerator Q ∘ₗ (map lens ∘ₗ hom.toLens) =
    lens ∘ₗ (cogenerator P ∘ₗ hom.toLens)
  rw [← Lens.comp_assoc, cogenerator_comp_map, Lens.comp_assoc]

end CofreeP
end PFunctor
