/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.Polynomial
public import PolyFun.PFunctor.Free.Polynomial

/-!
# Executing free patterns on cofree matter

This file defines the executable core of the Libkind--Spivak
pattern-runs-on-matter interaction. A finite `P`-pattern runs synchronously
against a potentially infinite `Q`-behavior:

* a pattern leaf terminates without advancing the behavior;
* a pattern node and the current behavior root produce a `P ⊗ Q` node;
* a joint direction selects both the next pattern branch and the next
  behavior subtree.

`runObj` packages the output shape together with its complete backward map.
Consequently, the output path recovers both the complete source-pattern path
and the finite source-matter vertex followed during execution. This packaged
definition keeps all dependent indices aligned and gives `runOn` as a lens.

The executable construction retains four independent generator universes.
Its identification with the paper's internal-hom/convolution construction and
the fixed-universe categorical module laws live in downstream modules.

## Reference

* Libkind and Spivak, *Pattern Runs on Matter: The Free Monad Monad as a
  Module over the Cofree Comonad Comonad*, Equation (1) and Section 3.2.
-/

@[expose] public section

universe pA pB pA' pB' qA qB qA' qB' v

namespace PFunctor
namespace FreeP

variable {P : PFunctor.{pA, pB}} {Q : PFunctor.{qA, qB}}

/-- Execute a finite pattern shape against a potentially infinite matter
behavior, packaging the output shape with the exact source pattern path and
matter vertex selected by every output path. -/
def runObj : (pattern : (FreeP P).A) → (matter : (CofreeP Q).A) →
    (FreeP (P ⊗ Q)).Obj (FreeM.Path pattern × M.Vertex matter)
  | .pure _, tree =>
      ⟨.pure PUnit.unit, fun _ => ⟨PUnit.unit, .root tree⟩⟩
  | .liftBind a rest, tree =>
      FreeP.node (a, M.head tree) fun direction =>
        FreeP.relabel
          (fun pulled =>
            ⟨FreeM.Path.cons a rest direction.1 pulled.1,
              M.Vertex.child direction.2 pulled.2⟩)
          (runObj (rest direction.1) (M.children tree direction.2))

theorem runObj_pure (value : PUnit.{pB + 1})
    (matter : (CofreeP Q).A) :
    runObj (P := P) (FreeM.pure value) matter =
      ⟨FreeM.pure PUnit.unit,
        fun _ => ⟨PUnit.unit, M.Vertex.root matter⟩⟩ :=
  rfl

theorem runObj_liftBind (a : P.A)
    (rest : P.B a → FreeM P PUnit.{pB + 1})
    (matter : (CofreeP Q).A) :
    runObj (FreeM.liftBind a rest) matter =
      FreeP.node (P := P ⊗ Q) (a, M.head matter) (fun direction =>
        FreeP.relabel
          (fun pulled =>
            ⟨FreeM.Path.cons a rest direction.1 pulled.1,
              M.Vertex.child direction.2 pulled.2⟩)
          (runObj (rest direction.1)
            (M.children matter direction.2))) :=
  rfl

/-- Run a pattern against a cofree object whose finite vertices carry
payloads, returning each output path together with the payload at the matter
vertex reached by that path. Packaging the matter shape and its dependent
labelling together is also the stable rewriting boundary for mapped and
synchronized child subtrees. -/
def runLabeled {α : Type v} (pattern : (FreeP P).A)
    (matter : (CofreeP Q).Obj α) :
    (FreeP (P ⊗ Q)).Obj (FreeM.Path pattern × α) :=
  FreeP.relabel
    (fun pulled => ⟨pulled.1, matter.2 pulled.2⟩)
    (runObj pattern matter.1)

/-- A terminated pattern returns its leaf together with the label at the root
of the matter object. -/
theorem runLabeled_pure {α : Type v} (value : PUnit.{pB + 1})
    (matter : (CofreeP Q).Obj α) :
    runLabeled (P := P) (FreeM.pure value) matter =
      ⟨FreeM.pure PUnit.unit, fun _ => (PUnit.unit, matter.2 (.root _))⟩ :=
  rfl

/-- Recursive equation for running a labelled matter object through one
pattern node. -/
theorem runLabeled_liftBind {α : Type v} (a : P.A)
    (rest : P.B a → (FreeP P).A) (matter : (CofreeP Q).Obj α) :
    runLabeled (FreeM.liftBind a rest) matter =
      FreeP.node (P := P ⊗ Q) (a, M.head matter.1) (fun direction =>
        FreeP.relabel
          (fun pulled =>
            (FreeM.Path.cons a rest direction.1 pulled.1, pulled.2))
          (runLabeled (rest direction.1)
            (⟨M.children matter.1 direction.2, fun next =>
              matter.2 (.child direction.2 next)⟩ :
              (CofreeP Q).Obj α))) :=
  rfl

/-- Running the shape of a labelled free node ignores its leaf labels and
recurses on the child shapes. -/
@[simp]
theorem runObj_node {α : Type v} (a : P.A)
    (children : P.B a → (FreeP P).Obj α)
    (matter : (CofreeP Q).A) :
    runObj (FreeP.node a children).1 matter =
      FreeP.node (P := P ⊗ Q) (a, M.head matter) (fun direction =>
        FreeP.relabel
          (fun pulled =>
            (FreeM.Path.cons a (fun d => (children d).1)
                direction.1 pulled.1,
              M.Vertex.child direction.2 pulled.2))
          (runObj (children direction.1).1
            (M.children matter direction.2))) :=
  rfl

/-- A finite pattern runs on a cofree behavior by synchronizing their nodes.
The backward lens map splits an output path into the complete pattern path and
the finite matter vertex visited during the run. -/
def runOn (P : PFunctor.{pA, pB}) (Q : PFunctor.{qA, qB}) :
    Lens (FreeP P ⊗ CofreeP Q) (FreeP (P ⊗ Q)) where
  toFunA input := (runObj input.1 input.2).1
  toFunB input := (runObj input.1 input.2).2

@[simp]
theorem runOn_toFunA (pattern : (FreeP P).A) (matter : (CofreeP Q).A) :
    (runOn P Q).toFunA (pattern, matter) = (runObj pattern matter).1 :=
  rfl

@[simp]
theorem runOn_toFunB (pattern : (FreeP P).A) (matter : (CofreeP Q).A)
    (path : (FreeP (P ⊗ Q)).B ((runOn P Q).toFunA (pattern, matter))) :
    (runOn P Q).toFunB (pattern, matter) path =
      (runObj pattern matter).2 path :=
  rfl

/-! ## Naturality -/

/-- Packaged operational naturality, including the complete dependent
backward map. Mapping both generators before execution agrees with executing
first and mapping the synchronized output. -/
theorem runObj_natural
    {P' : PFunctor.{pA', pB'}} {Q' : PFunctor.{qA', qB'}}
    (f : Lens P P') (g : Lens Q Q')
    (pattern : (FreeP P).A) (matter : (CofreeP Q).A) :
    FreeP.relabel
        (fun pulled =>
          ⟨(FreeP.map f).toFunB pattern pulled.1,
            (CofreeP.map g).toFunB matter pulled.2⟩)
        (runObj ((FreeP.map f).toFunA pattern)
          ((CofreeP.map g).toFunA matter)) =
      Lens.mapObj (FreeP.map (f ⊗ₗ g)) (runObj pattern matter) := by
  induction pattern generalizing matter with
  | pure value =>
      cases value
      change
        (⟨FreeM.pure PUnit.unit,
          fun _ =>
            ⟨PUnit.unit,
              M.Vertex.pullMapLens g matter
                (.root (M.mapLens g matter))⟩⟩ :
          (FreeP (P' ⊗ Q')).Obj
            (FreeM.Path (FreeM.pure PUnit.unit : FreeM P PUnit) ×
              M.Vertex matter)) =
        (⟨FreeM.pure PUnit.unit,
          fun _ => ⟨PUnit.unit, .root matter⟩⟩ :
          (FreeP (P' ⊗ Q')).Obj
            (FreeM.Path (FreeM.pure PUnit.unit : FreeM P PUnit) ×
              M.Vertex matter))
      rw [M.Vertex.pullMapLens_root]
  | liftBind a rest ih =>
      have hhead := M.head_mapLens g matter
      cases hhead
      simp only [FreeP.map_toFunA, FreeP.mapShape, CofreeP.map_toFunA,
        FreeM.mapLens, FreeM.map, runObj, FreeP.relabel_node,
        FreeP.mapObj_node]
      congr 1
      funext direction
      rcases direction with ⟨pDirection, qDirection⟩
      let sourceQ := M.pullDirection g matter qDirection
      have hSourceQ :
          sourceQ = g.toFunB (M.head matter) qDirection := by
        dsimp only [sourceQ, M.pullDirection]
        apply congrArg (g.toFunB (M.head matter))
        exact eq_of_heq (cast_heq _ qDirection)
      have hchild := M.children_mapLens g matter qDirection
      simp only [Lens.tensorMap, Prod.map]
      let sourceChild := M.children matter sourceQ
      let mappedPattern := (FreeP.map f).toFunA
        (rest (f.toFunB a pDirection))
      let runMatterObj (x : (CofreeP Q').Obj (M.Vertex sourceChild)) :=
        FreeP.relabel
          (fun pulled =>
            (⟨(FreeP.map f).toFunB
                (rest (f.toFunB a pDirection)) pulled.1,
              pulled.2⟩ :
              FreeM.Path (rest (f.toFunB a pDirection)) ×
                M.Vertex sourceChild))
          (runLabeled mappedPattern x)
      have hMatter := congrArg runMatterObj
        (CofreeP.mapChildObj g matter qDirection)
      have hMatterNormalized :
          runMatterObj
              ⟨M.children (M.mapLens g matter) qDirection,
                fun vertex => M.Vertex.pullMapLens g sourceChild
                  (cast (congrArg M.Vertex hchild) vertex)⟩ =
            FreeP.relabel
              (fun pulled =>
                (⟨(FreeP.map f).toFunB
                    (rest (f.toFunB a pDirection)) pulled.1,
                  (CofreeP.map g).toFunB sourceChild pulled.2⟩ :
                  FreeM.Path (rest (f.toFunB a pDirection)) ×
                    M.Vertex sourceChild))
              (runObj mappedPattern
                ((CofreeP.map g).toFunA sourceChild)) := by
        simpa only [runMatterObj, runLabeled, FreeP.relabel_relabel,
          Function.comp_def, CofreeP.map_toFunA,
          CofreeP.map_toFunB] using hMatter
      have hCore := hMatterNormalized.trans
        (ih (f.toFunB a pDirection) sourceChild)
      have h := congrArg
        (FreeP.relabel (fun pulled :
            FreeM.Path (rest (f.toFunB a pDirection)) ×
              M.Vertex sourceChild =>
          (⟨FreeM.Path.cons a rest (f.toFunB a pDirection) pulled.1,
              M.Vertex.child sourceQ pulled.2⟩ :
            FreeM.Path (FreeM.liftBind a rest) × M.Vertex matter)))
        hCore
      let rhsAt (q : Q.B (M.head matter)) :=
        FreeP.relabel
          (fun pulled :
              FreeM.Path (rest (f.toFunB a pDirection)) ×
                M.Vertex (M.children matter q) =>
            (⟨FreeM.Path.cons a rest (f.toFunB a pDirection) pulled.1,
                M.Vertex.child q pulled.2⟩ :
              FreeM.Path (FreeM.liftBind a rest) × M.Vertex matter))
          (Lens.mapObj (FreeP.map (f ⊗ₗ g))
            (runObj (rest (f.toFunB a pDirection))
              (M.children matter q)))
      have hRhs : rhsAt sourceQ =
          rhsAt (g.toFunB (M.head matter) qDirection) :=
        congrArg rhsAt hSourceQ
      have hFinal := h.trans hRhs
      simpa only [FreeP.relabel_relabel, FreeP.mapObj_relabel,
        Function.comp_def, FreeP.map_toFunB_cons,
        CofreeP.map_toFunB, M.Vertex.pullMapLens_child,
        FreeP.map_toFunA, FreeP.mapShape, CofreeP.map_toFunA,
        FreeM.mapLens_lift_bind, FreeM.Path.pullMap_lift_bind,
        FreeM.Path.pullMapLens_lift_bind, sourceQ, sourceChild,
        mappedPattern, runMatterObj, runLabeled, rhsAt, hchild,
        Lens.tensorMap, Prod.map] using hFinal

/-- The Libkind--Spivak interaction is covariant in both the pattern and
matter generators. All eight source and target universes remain independent. -/
theorem runOn_natural
    {P' : PFunctor.{pA', pB'}} {Q' : PFunctor.{qA', qB'}}
    (f : Lens P P') (g : Lens Q Q') :
    runOn P' Q' ∘ₗ (FreeP.map f ⊗ₗ CofreeP.map g) =
      FreeP.map (f ⊗ₗ g) ∘ₗ runOn P Q := by
  let lhs := runOn P' Q' ∘ₗ (FreeP.map f ⊗ₗ CofreeP.map g)
  let rhs := FreeP.map (f ⊗ₗ g) ∘ₗ runOn P Q
  have hobj : ∀ input : (FreeP P ⊗ CofreeP Q).A,
      Lens.mapObj lhs
          (⟨input, id⟩ : (FreeP P ⊗ CofreeP Q).Obj
            ((FreeP P ⊗ CofreeP Q).B input)) =
        Lens.mapObj rhs
          (⟨input, id⟩ : (FreeP P ⊗ CofreeP Q).Obj
            ((FreeP P ⊗ CofreeP Q).B input)) := by
    rintro ⟨pattern, matter⟩
    exact runObj_natural f g pattern matter
  let hA : ∀ input, lhs.toFunA input = rhs.toFunA input :=
    fun input => congrArg Sigma.fst (hobj input)
  refine Lens.ext lhs rhs hA ?_
  intro input
  apply eq_of_heq
  have hraw : lhs.toFunB input ≍ rhs.toFunB input :=
    (Sigma.ext_iff.mp (hobj input)).2
  have hcast : (hA input ▸ rhs.toFunB input) ≍ rhs.toFunB input :=
    eqRec_heq_self _ _
  exact hraw.trans hcast.symm

end FreeP
end PFunctor
