/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Resumption
public import PolyFun.PFunctor.M.Vertex

/-!
# Interaction trees as resumptions with an explicit tau event

An ITree over `P` is an M-type for visible queries, returns, and unary silent
steps. A resumption over `P + y` has exactly the same three cases, with the
`y` summand serving as the silent event. This file packages the reassociation
of those implementation polynomials as an exact equivalence.
-/

@[expose] public section

universe uA uB uα

namespace ITree

variable {P : PFunctor.{uA, uB}} {α : Type uα}

attribute [local implicit_reducible] PFunctor.Obj

/-- Reassociate the raw ITree polynomial `(P + C α) + y` as the raw
resumption polynomial `(P + y) + C α`. -/
def resumptionWithTauPolyEquiv :
    PFunctor.Lens.Equiv.{max uA uα, uB, max uA uα, uB}
      (Poly P α) ((P + PFunctor.y.{uA, uB}) + PFunctor.C α) where
  toLens :=
    { toFunA := fun
        | Sum.inl (Sum.inl position) => Sum.inl (Sum.inl position)
        | Sum.inl (Sum.inr value) => Sum.inr value
        | Sum.inr _ => Sum.inl (Sum.inr PUnit.unit)
      toFunB := fun shape =>
        match shape with
        | Sum.inl (Sum.inl _) => id
        | Sum.inl (Sum.inr _) => id
        | Sum.inr _ => id }
  invLens :=
    { toFunA := fun
        | Sum.inl (Sum.inl position) => Sum.inl (Sum.inl position)
        | Sum.inl (Sum.inr _) => Sum.inr PUnit.unit
        | Sum.inr value => Sum.inl (Sum.inr value)
      toFunB := fun shape =>
        match shape with
        | Sum.inl (Sum.inl _) => id
        | Sum.inl (Sum.inr _) => id
        | Sum.inr _ => id }
  left_inv := by
    ext shape direction
    · rcases shape with (position | value) | stepPosition <;> rfl
    · rcases shape with (position | value) | stepPosition <;> rfl
  right_inv := by
    ext shape direction
    · rcases shape with (position | stepPosition) | value <;> rfl
    · rcases shape with (position | stepPosition) | value <;> rfl

/-- Regard an arbitrary ITree as a resumption whose extra `y` event records
silent steps. -/
def toResumptionWithTau (tree : _root_.ITree P α) :
    PFunctor.Resumption (P + PFunctor.y.{uA, uB}) α :=
  PFunctor.M.mapLens
    (resumptionWithTauPolyEquiv (P := P) (α := α)).toLens tree.toM

/-- One-step computational view of the resumption-with-tau encoding. -/
theorem dest_toResumptionWithTau (tree : _root_.ITree P α) :
    PFunctor.Resumption.dest (toResumptionWithTau tree) =
      match ITree.shape' tree with
      | ⟨.pure value, _⟩ => Sum.inl value
      | ⟨.step, next⟩ => Sum.inr
          ⟨Sum.inr PUnit.unit, fun direction =>
            toResumptionWithTau (next direction)⟩
      | ⟨.query position, next⟩ => Sum.inr
          ⟨Sum.inl position, fun direction =>
            toResumptionWithTau (next direction)⟩ := by
  unfold toResumptionWithTau PFunctor.Resumption.dest
  unfold PFunctor.M.mapLens
  rw [PFunctor.M.dest_corec]
  rw [← ITree.pack_shape' tree]
  rcases hshape : ITree.shape' tree with ⟨shape, next⟩
  cases shape with
  | pure value => rfl
  | step => rfl
  | query position => rfl

@[simp] theorem toResumptionWithTau_pure (value : α) :
    toResumptionWithTau (ITree.pure (F := P) value) =
      PFunctor.Resumption.pure value := by
  apply PFunctor.Resumption.eq_of_dest_eq
  rw [dest_toResumptionWithTau, ITree.shape'_pure,
    PFunctor.Resumption.dest_pure]

@[simp] theorem toResumptionWithTau_step (tree : _root_.ITree P α) :
    toResumptionWithTau (ITree.step tree) =
      PFunctor.Resumption.query
        (p := P + PFunctor.y.{uA, uB}) (Sum.inr PUnit.unit)
        (fun _ => toResumptionWithTau tree) := by
  apply PFunctor.Resumption.eq_of_dest_eq
  rw [dest_toResumptionWithTau, ITree.shape'_step,
    PFunctor.Resumption.dest_query]

@[simp] theorem toResumptionWithTau_query (position : P.A)
    (next : P.B position → _root_.ITree P α) :
    toResumptionWithTau (ITree.query position next) =
      PFunctor.Resumption.query
        (p := P + PFunctor.y.{uA, uB}) (Sum.inl position)
        (fun direction => toResumptionWithTau (next direction)) := by
  apply PFunctor.Resumption.eq_of_dest_eq
  rw [dest_toResumptionWithTau, ITree.shape'_query,
    PFunctor.Resumption.dest_query]

/-- Decode a resumption over `P + y`, interpreting the `y` event as a silent
ITree step. -/
def ofResumptionWithTau
    (computation : PFunctor.Resumption (P + PFunctor.y.{uA, uB}) α) :
    _root_.ITree P α :=
  ITree.ofM
    (PFunctor.M.mapLens
      (resumptionWithTauPolyEquiv (P := P) (α := α)).invLens computation)

@[simp] theorem ofResumptionWithTau_toResumptionWithTau
    (tree : _root_.ITree P α) :
    ofResumptionWithTau (toResumptionWithTau tree) = tree := by
  apply ITree.ext
  change PFunctor.M.mapLens
      (resumptionWithTauPolyEquiv (P := P) (α := α)).invLens
      (PFunctor.M.mapLens
        (resumptionWithTauPolyEquiv (P := P) (α := α)).toLens tree.toM) =
    tree.toM
  rw [← PFunctor.M.mapLens_comp,
    (resumptionWithTauPolyEquiv (P := P) (α := α)).left_inv,
    PFunctor.M.mapLens_id]

@[simp] theorem toResumptionWithTau_ofResumptionWithTau
    (computation : PFunctor.Resumption (P + PFunctor.y.{uA, uB}) α) :
    toResumptionWithTau (ofResumptionWithTau computation) = computation := by
  change PFunctor.M.mapLens
      (resumptionWithTauPolyEquiv (P := P) (α := α)).toLens
      (PFunctor.M.mapLens
        (resumptionWithTauPolyEquiv (P := P) (α := α)).invLens computation) =
    computation
  rw [← PFunctor.M.mapLens_comp,
    (resumptionWithTauPolyEquiv (P := P) (α := α)).right_inv,
    PFunctor.M.mapLens_id]

/-- Exact equivalence between interaction trees and resumptions with an
explicit unary tau event. -/
def equivResumptionWithTau :
    _root_.ITree P α ≃
      PFunctor.Resumption (P + PFunctor.y.{uA, uB}) α where
  toFun := toResumptionWithTau
  invFun := ofResumptionWithTau
  left_inv := ofResumptionWithTau_toResumptionWithTau
  right_inv := toResumptionWithTau_ofResumptionWithTau

end ITree
