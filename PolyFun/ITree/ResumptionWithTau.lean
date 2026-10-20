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

universe uA uB uα uβ

namespace ITree

variable {P : PFunctor.{uA, uB}} {α : Type uα}

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
      | .mk (.pure value) _ => Sum.inl value
      | .mk .step next => Sum.inr
          (.mk (Sum.inr PUnit.unit) fun direction =>
            toResumptionWithTau (next direction))
      | .mk (.query position) next => Sum.inr
          (.mk (Sum.inl position) fun direction =>
            toResumptionWithTau (next direction)) := by
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

/-- The exact encoding preserves substitution, including silent steps. -/
@[simp] theorem toResumptionWithTau_bind {β : Type uβ} (tree : _root_.ITree P α)
    (next : α → _root_.ITree P β) :
    toResumptionWithTau (bind tree next) =
      PFunctor.Resumption.bind (toResumptionWithTau tree)
        (fun value => toResumptionWithTau (next value)) := by
  apply PFunctor.Resumption.bisim
    (fun left right => left = right ∨ ∃ source : _root_.ITree P α,
      left = toResumptionWithTau (bind source next) ∧
      right = PFunctor.Resumption.bind (toResumptionWithTau source)
        (fun value => toResumptionWithTau (next value)))
  · rintro left right (heq | ⟨source, rfl, rfl⟩)
    · subst left
      rcases h : PFunctor.Resumption.dest right with value | ⟨a, rest⟩
      · exact .pure value h h
      · exact .query a rest rest h h (fun _ => Or.inl rfl)
    · rcases h : shape' source with ⟨head, rest⟩
      cases head with
      | pure value =>
          have heq := eq_pure_of_dest h
          subst source
          simp only [bind_pure_left, toResumptionWithTau_pure,
            PFunctor.Resumption.pure_bind]
          rcases hn : PFunctor.Resumption.dest (toResumptionWithTau (next value)) with
            result | ⟨a, children⟩
          · exact .pure result hn hn
          · exact .query a children children hn hn (fun _ => Or.inl rfl)
      | step =>
          have heq := eq_step_of_dest h
          subst source
          simp only [bind_step, toResumptionWithTau_step, PFunctor.Resumption.bind_query]
          exact .query (.inr PUnit.unit) _ _ (PFunctor.Resumption.dest_query _ _)
            (PFunctor.Resumption.dest_query _ _) (fun _ => Or.inr ⟨_, rfl, rfl⟩)
      | query a =>
          have heq := eq_query_of_dest h
          subst source
          simp only [bind_query, toResumptionWithTau_query, PFunctor.Resumption.bind_query]
          exact .query (.inl a) _ _ (PFunctor.Resumption.dest_query _ _)
            (PFunctor.Resumption.dest_query _ _) (fun answer => Or.inr ⟨rest answer, rfl, rfl⟩)
  · exact Or.inr ⟨tree, rfl, rfl⟩

/-- Encoding the tau-free ITree associated to a resumption agrees with
injecting its visible interface into the resumption-with-tau signature. This is
the commuting square between the tau-free and unrestricted resumption views of
an ITree. -/
theorem toResumptionWithTau_toITree
    (computation : PFunctor.Resumption P α) :
    toResumptionWithTau (PFunctor.Resumption.toITree computation) =
      PFunctor.Resumption.mapLens
        (PFunctor.Lens.inl (P := P) (Q := PFunctor.y.{uA, uB}))
        computation := by
  apply PFunctor.Resumption.bisim
    (fun left right => ∃ source : PFunctor.Resumption P α,
      left = toResumptionWithTau (PFunctor.Resumption.toITree source) ∧
      right = PFunctor.Resumption.mapLens
        (PFunctor.Lens.inl (P := P) (Q := PFunctor.y.{uA, uB})) source)
  · rintro left right ⟨source, rfl, rfl⟩
    rcases hsource : PFunctor.Resumption.dest source with value | ⟨position, next⟩
    · exact .pure value
        (by rw [dest_toResumptionWithTau,
          PFunctor.Resumption.shape'_toITree, hsource])
        (by rw [PFunctor.Resumption.dest_mapLens, hsource])
    · exact .query (Sum.inl position)
        (fun direction => toResumptionWithTau
          (PFunctor.Resumption.toITree (next direction)))
        (fun direction => PFunctor.Resumption.mapLens
          (PFunctor.Lens.inl (P := P) (Q := PFunctor.y.{uA, uB}))
          (next direction))
        (by rw [dest_toResumptionWithTau,
          PFunctor.Resumption.shape'_toITree, hsource])
        (by rw [PFunctor.Resumption.dest_mapLens, hsource]; rfl)
        (fun direction => ⟨next direction, rfl, rfl⟩)
  · exact ⟨computation, rfl, rfl⟩

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

open PFunctor

/-- Encoding silent steps explicitly preserves distinct trees. -/
theorem toResumptionWithTau_injective :
    Function.Injective (toResumptionWithTau (P := P) (α := α)) :=
  Function.LeftInverse.injective ofResumptionWithTau_toResumptionWithTau

@[simp] theorem ofResumptionWithTau_pure (a : α) :
    ofResumptionWithTau (Resumption.pure a : Resumption (P + y.{uA, uB}) α) = pure a := by
  apply toResumptionWithTau_injective
  simp

/-- Decoding a visible query preserves its dependent continuation. -/
theorem ofResumptionWithTau_query (p : P.A) (k : P.B p → Resumption (P + y.{uA, uB}) α) :
    ofResumptionWithTau (Resumption.query (p := P + y.{uA, uB}) (.inl p) k) =
      query p (fun b => ofResumptionWithTau (k b)) := by
  apply toResumptionWithTau_injective
  simp

/-- Decoding a unary administrative event produces one silent step. -/
theorem ofResumptionWithTau_step (k : PUnit.{uB + 1} → Resumption (P + y.{uA, uB}) α) :
    ofResumptionWithTau (Resumption.query (p := P + y.{uA, uB}) (.inr PUnit.unit) k) =
      step (ofResumptionWithTau (k PUnit.unit)) := by
  apply toResumptionWithTau_injective
  simp

/-- The computational view of an explicitly encoded silent-step resumption. -/
theorem shape'_ofResumptionWithTau (t : Resumption (P + y.{uA, uB}) α) :
    shape' (ofResumptionWithTau t) = match Resumption.dest t with
    | .inl a => .mk (.pure a) PEmpty.elim
    | .inr ⟨.inl p, k⟩ => .mk (.query p) (fun b => ofResumptionWithTau (k b))
    | .inr ⟨.inr _, k⟩ => .mk .step (fun b => ofResumptionWithTau (k b)) := by
  rcases ht : Resumption.dest t with a | ⟨p, k⟩
  · have he : t = Resumption.pure a :=
      Resumption.eq_of_dest_eq (ht.trans (Resumption.dest_pure a).symm)
    simp [he, ofResumptionWithTau_pure]
  · have he : t = Resumption.query p k :=
      Resumption.eq_of_dest_eq (ht.trans (Resumption.dest_query p k).symm)
    rcases p with p | tick
    · rw [he, ofResumptionWithTau_query, shape'_query]
    · cases tick
      rw [he, ofResumptionWithTau_step, shape'_step]

end ITree
