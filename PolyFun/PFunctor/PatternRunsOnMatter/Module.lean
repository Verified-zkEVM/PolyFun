/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.PatternRunsOnMatter.Universal
public import PolyFun.PFunctor.Cofree.LaxMonoidal

/-!
# The pattern-runs-on-matter module laws

This file proves the unit and associativity equations of Libkind--Spivak,
*Pattern Runs on Matter*, Theorem 3.4. We use the right-action orientation of
the paper's Equation (1), `FreeP P ⊗ CofreeP Q ⇆ FreeP (P ⊗ Q)`.
Appendix D draws symmetry-equivalent left-action diagrams; no unmentioned
symmetry is inserted here.

The laws are stated in one square universe because they compare the universal
`xi` construction and the cofree lax-monoidal structure inside a fixed
polynomial category. The executable `runOn` and its naturality remain fully
heterogeneous in `Basic`.
-/

@[expose] public section

universe u

namespace PFunctor
namespace FreeP

private theorem runObj_unit (P : PFunctor.{u, u})
    (pattern : (FreeP P).A) :
    Lens.mapObj (FreeP.map (Lens.Equiv.tensorX (P := P)).toLens)
        (FreeP.relabel
          (fun pulled => (pulled.1, PUnit.unit))
          (runObj pattern
            ((CofreeP.laxUnit.{u, u}).toFunA
              (PUnit.unit : X.{u, u}.A)))) =
      (⟨pattern, fun path => (path, PUnit.unit)⟩ :
        (FreeP P).Obj (FreeM.Path pattern × PUnit.{u + 1})) := by
  induction pattern with
  | pure value =>
      cases value
      rfl
  | liftBind a rest ih =>
      rw [runObj_liftBind, FreeP.relabel_node, FreeP.mapObj_node]
      rw [← FreeP.node_paths a rest (fun path => (path, PUnit.unit))]
      congr 1
      funext direction
      change P.B a at direction
      change Lens.mapObj (FreeP.map
          (Lens.Equiv.tensorX (P := P)).toLens)
          (FreeP.relabel (fun pulled => (pulled.1, PUnit.unit))
            (FreeP.relabel
              (fun pulled =>
                (FreeM.Path.cons a rest direction pulled.1,
                  M.Vertex.child
                    (t := (CofreeP.laxUnit.{u, u}).toFunA
                      (PUnit.unit : X.{u, u}.A))
                    PUnit.unit pulled.2))
              (runObj (rest direction)
                (M.children
                  ((CofreeP.laxUnit.{u, u}).toFunA
                    (PUnit.unit : X.{u, u}.A)) PUnit.unit)))) = _
      rw [FreeP.relabel_relabel, FreeP.mapObj_relabel]
      change FreeP.relabel
          (fun pulled =>
            (FreeM.Path.cons a rest direction pulled.1, PUnit.unit))
          (Lens.mapObj (FreeP.map
              (Lens.Equiv.tensorX (P := P)).toLens)
            (runObj (rest direction)
              (M.children
                ((CofreeP.laxUnit.{u, u}).toFunA
                  (PUnit.unit : X.{u, u}.A)) PUnit.unit))) = _
      rw [CofreeP.laxUnit_children]
      have ih' :
          FreeP.relabel (fun pulled => (pulled.1, PUnit.unit))
              (Lens.mapObj (FreeP.map
                (Lens.Equiv.tensorX (P := P)).toLens)
                (runObj (rest direction)
                  ((CofreeP.laxUnit.{u, u}).toFunA
                    (PUnit.unit : X.{u, u}.A)))) =
            (⟨rest direction, fun path => (path, PUnit.unit)⟩ :
              (FreeP P).Obj
                (FreeM.Path (rest direction) × PUnit.{u + 1})) := by
        rw [← FreeP.mapObj_relabel]
        exact ih direction
      have hi := congrArg
        (FreeP.relabel (P := P)
          (fun pulled : FreeM.Path (rest direction) × PUnit.{u + 1} =>
            (FreeM.Path.cons a rest direction pulled.1, pulled.2)))
        ih'
      simpa only [FreeP.relabel_relabel, FreeP.mapObj_relabel,
        FreeP.relabel, Function.comp_def] using hi

private def unitLhs (P : PFunctor.{u, u}) :
    Lens (FreeP P ⊗ X.{u, u}) (FreeP P) :=
  (FreeP.map (Lens.Equiv.tensorX (P := P)).toLens ∘ₗ
      runOn P X.{u, u}) ∘ₗ
    (Lens.id (FreeP P) ⊗ₗ CofreeP.laxUnit.{u, u})

private theorem unitObj (P : PFunctor.{u, u})
    (pattern : (FreeP P).A) :
    Lens.mapObj (unitLhs P)
        (⟨(pattern, (PUnit.unit : X.{u, u}.A)), id⟩ :
          (FreeP P ⊗ X.{u, u}).Obj
            (FreeM.Path pattern × PUnit.{u + 1})) =
      Lens.mapObj (Lens.Equiv.tensorX (P := FreeP P)).toLens
        (⟨(pattern, (PUnit.unit : X.{u, u}.A)), id⟩ :
          (FreeP P ⊗ X.{u, u}).Obj
            (FreeM.Path pattern × PUnit.{u + 1})) := by
  change Lens.mapObj (FreeP.map
      (Lens.Equiv.tensorX (P := P)).toLens)
      (FreeP.relabel
        (fun pulled =>
          (pulled.1,
            (CofreeP.laxUnit.{u, u}).toFunB
              (PUnit.unit : X.{u, u}.A) pulled.2))
        (runObj pattern
          ((CofreeP.laxUnit.{u, u}).toFunA
            (PUnit.unit : X.{u, u}.A)))) =
    (⟨pattern, fun path => (path, PUnit.unit)⟩ :
      (FreeP P).Obj (FreeM.Path pattern × PUnit.{u + 1}))
  have hlabel :
      (fun pulled : FreeM.Path pattern ×
          M.Vertex ((CofreeP.laxUnit.{u, u}).toFunA
            (PUnit.unit : X.{u, u}.A)) =>
        (pulled.1,
          (CofreeP.laxUnit.{u, u}).toFunB
            (PUnit.unit : X.{u, u}.A) pulled.2)) =
      (fun pulled => (pulled.1, PUnit.unit)) := by
    funext pulled
    apply Prod.ext
    · rfl
    · exact CofreeP.laxUnit_toFunB pulled.2
  rw [hlabel]
  exact runObj_unit P pattern

/-- Right-unit coherence for the executable pattern action. -/
theorem runOn_unit (P : PFunctor.{u, u}) :
    (FreeP.map (Lens.Equiv.tensorX (P := P)).toLens ∘ₗ
        runOn P X.{u, u}) ∘ₗ
        (Lens.id (FreeP P) ⊗ₗ CofreeP.laxUnit.{u, u}) =
      (Lens.Equiv.tensorX (P := FreeP P)).toLens := by
  let lhs := unitLhs P
  let rhs := (Lens.Equiv.tensorX (P := FreeP P)).toLens
  have hobj : ∀ input : (FreeP P ⊗ X.{u, u}).A,
      Lens.mapObj lhs
          (⟨input, id⟩ : (FreeP P ⊗ X.{u, u}).Obj
            ((FreeP P ⊗ X.{u, u}).B input)) =
        Lens.mapObj rhs
          (⟨input, id⟩ : (FreeP P ⊗ X.{u, u}).Obj
            ((FreeP P ⊗ X.{u, u}).B input)) := by
    rintro ⟨pattern, xPosition⟩
    cases xPosition
    exact unitObj P pattern
  exact Lens.ext_mapObj lhs rhs hobj

/-- Right-unit coherence for the universal interaction. -/
theorem xi_unit (P : PFunctor.{u, u}) :
    (FreeP.map (Lens.Equiv.tensorX (P := P)).toLens ∘ₗ
        xi P X.{u, u}) ∘ₗ
        (Lens.id (FreeP P) ⊗ₗ CofreeP.laxUnit.{u, u}) =
      (Lens.Equiv.tensorX (P := FreeP P)).toLens := by
  rw [← runOn_eq_xi P X.{u, u}]
  exact runOn_unit P

/-! ## Associativity -/

private def vertexPairObj {Q R : PFunctor.{u, u}}
    (matterQ : (CofreeP Q).A) (matterR : (CofreeP R).A) :
    (CofreeP Q ⊗ CofreeP R).Obj
      (M.Vertex matterQ × M.Vertex matterR) :=
  ⟨(matterQ, matterR), id⟩

private def laxTensorVertexObj {Q R : PFunctor.{u, u}}
    (matterQ : (CofreeP Q).A) (matterR : (CofreeP R).A) :
    (CofreeP (Q ⊗ R)).Obj (M.Vertex matterQ × M.Vertex matterR) :=
  Lens.mapObj (CofreeP.laxTensor Q R) (vertexPairObj matterQ matterR)

private theorem laxTensorVertexObj_child (Q R : PFunctor.{u, u})
    (matterQ : (CofreeP Q).A) (matterR : (CofreeP R).A)
    (direction : Q.B (M.head matterQ) × R.B (M.head matterR)) :
    (⟨M.children (laxTensorVertexObj matterQ matterR).1 direction,
        fun next => (laxTensorVertexObj matterQ matterR).2
          (.child direction next)⟩ :
      (CofreeP (Q ⊗ R)).Obj (M.Vertex matterQ × M.Vertex matterR)) =
    let mappedChild := Lens.mapObj (CofreeP.laxTensor Q R)
      (⟨(M.children matterQ direction.1,
          M.children matterR direction.2), id⟩ :
        (CofreeP Q ⊗ CofreeP R).Obj
          (M.Vertex (M.children matterQ direction.1) ×
            M.Vertex (M.children matterR direction.2)))
    ⟨mappedChild.1, fun next =>
      let pulled := mappedChild.2 next
      (.child direction.1 pulled.1, .child direction.2 pulled.2)⟩ := by
  simpa only [laxTensorVertexObj, vertexPairObj, Lens.mapObj,
    Function.comp_apply, id_eq] using
    CofreeP.laxTensor_childObj Q R matterQ matterR direction

private theorem runObj_assoc (P Q R : PFunctor.{u, u})
    (pattern : (FreeP P).A) (matterQ : (CofreeP Q).A)
    (matterR : (CofreeP R).A) :
    FreeP.relabel (fun pulled => ((pulled.1, pulled.2.1), pulled.2.2))
      (runLabeled pattern (laxTensorVertexObj matterQ matterR)) =
      Lens.mapObj (FreeP.map
          (Lens.Equiv.tensorAssoc
            (P := P) (Q := Q) (R := R)).toLens)
        (FreeP.relabel
          (fun pulled => ((runObj pattern matterQ).2 pulled.1, pulled.2))
          (runObj (runObj pattern matterQ).1 matterR)) := by
  induction pattern generalizing matterQ matterR with
  | pure value =>
      cases value
      change (⟨FreeM.pure PUnit.unit, fun _ =>
        ((PUnit.unit,
          ((CofreeP.laxTensor Q R).toFunB (matterQ, matterR)
            (.root ((CofreeP.laxTensor Q R).toFunA
              (matterQ, matterR)))).1),
          ((CofreeP.laxTensor Q R).toFunB (matterQ, matterR)
            (.root ((CofreeP.laxTensor Q R).toFunA
              (matterQ, matterR)))).2)⟩ :
        (FreeP (P ⊗ (Q ⊗ R))).Obj
          ((FreeM.Path (FreeM.pure PUnit.unit) × M.Vertex matterQ) ×
            M.Vertex matterR)) = _
      rw [CofreeP.laxTensor_toFunB_root]
      rfl
  | liftBind a rest ih =>
      rw [FreeP.runLabeled_liftBind, FreeP.relabel_node]
      simp only [runObj_liftBind, FreeP.relabel_relabel]
      rw [FreeP.runObj_node]
      simp only [FreeP.mapObj_relabel]
      let rightChildren := fun direction :
          (P.B a × Q.B (M.head matterQ)) × R.B (M.head matterR) =>
        FreeP.relabel
          (fun pulled =>
            (FreeM.Path.cons (P := P ⊗ Q) (a, M.head matterQ)
                (fun d : P.B a × Q.B (M.head matterQ) =>
                  (FreeP.relabel
                    (fun pulled =>
                      (FreeM.Path.cons a rest d.1 pulled.1,
                        M.Vertex.child d.2 pulled.2))
                    (runObj (rest d.1)
                      (M.children matterQ d.2))).1)
                direction.1 pulled.1,
              M.Vertex.child direction.2 pulled.2))
          (runObj
            (FreeP.relabel
              (fun pulled =>
                (FreeM.Path.cons a rest direction.1.1 pulled.1,
                  M.Vertex.child direction.1.2 pulled.2))
              (runObj (rest direction.1.1)
                (M.children matterQ direction.1.2))).1
            (M.children matterR direction.2))
      have hmap := FreeP.mapObj_node
        (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens
        ((a, M.head matterQ), M.head matterR) rightChildren
      conv_rhs =>
        change FreeP.relabel _
          (Lens.mapObj (FreeP.map
              (Lens.Equiv.tensorAssoc
                (P := P) (Q := Q) (R := R)).toLens)
            (FreeP.node ((a, M.head matterQ), M.head matterR)
              rightChildren))
      rw [hmap]
      rw [FreeP.relabel_node]
      congr 1
      funext direction
      let patternDirection := direction.1
      let matterQDirection := direction.2.1
      let matterRDirection := direction.2.2
      have hchild := laxTensorVertexObj_child Q R matterQ matterR
        (matterQDirection, matterRDirection)
      have hrun := congrArg (runLabeled (rest patternDirection)) hchild
      dsimp only [patternDirection, matterQDirection,
        matterRDirection] at hrun
      simp only [Prod.eta] at hrun ⊢
      rw [hrun]
      simp only [runLabeled, FreeP.relabel_relabel, Function.comp_def]
      have ihChild := ih direction.1
        (M.children matterQ direction.2.1)
        (M.children matterR direction.2.2)
      have wrapped := congrArg
        (FreeP.relabel (P := P ⊗ (Q ⊗ R))
          (fun pulled =>
            ((FreeM.Path.cons a rest direction.1 pulled.1.1,
                M.Vertex.child direction.2.1 pulled.1.2),
              M.Vertex.child direction.2.2 pulled.2)))
        ihChild
      simpa only [runLabeled, FreeP.relabel_relabel,
        FreeP.mapObj_relabel, FreeP.relabel,
        Function.comp_def, laxTensorVertexObj, vertexPairObj,
        rightChildren, Lens.mapObj, Function.comp_apply, id_eq,
        Lens.Equiv.tensorAssoc_toFunA, Lens.Equiv.tensorAssoc_toFunB,
        FreeP.node, FreeM.Path.cons, FreeM.Path.head,
        FreeM.Path.tail] using wrapped

/-- Associativity coherence for the executable pattern action. -/
theorem runOn_assoc (P Q R : PFunctor.{u, u}) :
    (runOn P (Q ⊗ R) ∘ₗ
        (Lens.id (FreeP P) ⊗ₗ CofreeP.laxTensor Q R)) ∘ₗ
        (Lens.Equiv.tensorAssoc
          (P := FreeP P) (Q := CofreeP Q)
          (R := CofreeP R)).toLens =
      (FreeP.map
          (Lens.Equiv.tensorAssoc
            (P := P) (Q := Q) (R := R)).toLens ∘ₗ
        runOn (P ⊗ Q) R) ∘ₗ
        (runOn P Q ⊗ₗ Lens.id (CofreeP R)) := by
  let lhs :=
    (runOn P (Q ⊗ R) ∘ₗ
        (Lens.id (FreeP P) ⊗ₗ CofreeP.laxTensor Q R)) ∘ₗ
      (Lens.Equiv.tensorAssoc
        (P := FreeP P) (Q := CofreeP Q)
        (R := CofreeP R)).toLens
  let rhs :=
    (FreeP.map
        (Lens.Equiv.tensorAssoc
          (P := P) (Q := Q) (R := R)).toLens ∘ₗ
      runOn (P ⊗ Q) R) ∘ₗ
      (runOn P Q ⊗ₗ Lens.id (CofreeP R))
  have hobj : ∀ input : ((FreeP P ⊗ CofreeP Q) ⊗ CofreeP R).A,
      Lens.mapObj lhs
          (⟨input, id⟩ : ((FreeP P ⊗ CofreeP Q) ⊗ CofreeP R).Obj
            (((FreeP P ⊗ CofreeP Q) ⊗ CofreeP R).B input)) =
        Lens.mapObj rhs
          (⟨input, id⟩ : ((FreeP P ⊗ CofreeP Q) ⊗ CofreeP R).Obj
            (((FreeP P ⊗ CofreeP Q) ⊗ CofreeP R).B input)) := by
    rintro ⟨⟨pattern, matterQ⟩, matterR⟩
    change FreeP.relabel
        (fun pulled => ((pulled.1, pulled.2.1), pulled.2.2))
        (runLabeled pattern (laxTensorVertexObj matterQ matterR)) =
      Lens.mapObj (FreeP.map
          (Lens.Equiv.tensorAssoc
            (P := P) (Q := Q) (R := R)).toLens)
        (FreeP.relabel
          (fun pulled => ((runObj pattern matterQ).2 pulled.1, pulled.2))
          (runObj (runObj pattern matterQ).1 matterR))
    exact runObj_assoc P Q R pattern matterQ matterR
  exact Lens.ext_mapObj lhs rhs hobj

/-- Associativity coherence for the universal interaction. -/
theorem xi_assoc (P Q R : PFunctor.{u, u}) :
    (xi P (Q ⊗ R) ∘ₗ
        (Lens.id (FreeP P) ⊗ₗ CofreeP.laxTensor Q R)) ∘ₗ
        (Lens.Equiv.tensorAssoc
          (P := FreeP P) (Q := CofreeP Q)
          (R := CofreeP R)).toLens =
      (FreeP.map
          (Lens.Equiv.tensorAssoc
            (P := P) (Q := Q) (R := R)).toLens ∘ₗ
        xi (P ⊗ Q) R) ∘ₗ
        (xi P Q ⊗ₗ Lens.id (CofreeP R)) := by
  rw [← runOn_eq_xi P (Q ⊗ R), ← runOn_eq_xi (P ⊗ Q) R,
    ← runOn_eq_xi P Q]
  exact runOn_assoc P Q R

end FreeP
end PFunctor
