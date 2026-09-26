/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Interp.Defs
public import PolyFun.ITree.Bisim.Bind

/-!
# Laws of interpretation

The computation rules of `interp` in a lawful iterative monad, stated up to the monad's
iteration equivalence `LawfulMonadIter.Eqv`: leaves return, silent steps vanish, a query asks
the handler and continues with the chosen branch, and a single event is answered by the
handler. The statements use `Eqv` rather than equality because `iterM` may insert guards that
the equivalence hides, as it does for interaction trees.
-/

@[expose] public section

universe u v

namespace ITree

open LawfulMonadIter

variable {E : PFunctor.{u, u}} {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadIter m]
  [LawfulMonadIter m] {α : Type u}

theorem interp_pure (h : PFunctor.Handler m E) (r : α) :
    Eqv (interp h (pure r)) (Pure.pure r) :=
  eqv_trans (LawfulMonadIter.iter_unfold _ _) (eqv_of_eq (by simp))

theorem interp_step (h : PFunctor.Handler m E) (t : ITree E α) :
    Eqv (interp h (step t)) (interp h t) :=
  eqv_trans (LawfulMonadIter.iter_unfold _ _) (eqv_of_eq (by simp [interp]))

theorem interp_query (h : PFunctor.Handler m E) (a : E.A) (k : E.B a → ITree E α) :
    Eqv (interp h (query a k)) (h a >>= fun b => interp h (k b)) :=
  eqv_trans (LawfulMonadIter.iter_unfold _ _) (eqv_of_eq (by simp [interp, bind_map_left]))

theorem interp_lift (h : PFunctor.Handler m E) (a : E.A) :
    Eqv (interp h (lift a)) (h a) :=
  eqv_trans (interp_query h a pure)
    (eqv_trans (bind_eqv (eqv_refl _) fun b => interp_pure h b) (eqv_of_eq (bind_pure _)))

/-! ### Sequencing

`interp` distributes over `bind` up to the target's equivalence. The proof runs the interpreted
loop of `bind t k` as a two-phase loop whose state is either a residual of `t` or a residual of
some `k a`: uniformity identifies the two loops, the codiagonal law splits the two-phase loop
into an outer loop over an inner one, and naturality plus uniformity identify the inner loops
with `interp h t` and `interp h (k a)`. -/

section Bind

variable {β : Type u} (h : PFunctor.Handler m E) (k : α → ITree E β)

/-- The two-phase loop body at a node of the first phase. -/
private def phaseView (v : (ViewPoly E α).Obj (ITree E α)) :
    m ((ITree E α ⊕ ITree E β) ⊕ β) :=
  match v with
  | .mk (.pure a) _ => Sum.map Sum.inr id <$> interpStep h (k a)
  | .mk .step c => Pure.pure (.inl (.inl (c PUnit.unit)))
  | .mk (.query e) c => (fun b => .inl (.inl (c b))) <$> h e

/-- The two-phase loop body: run `t`, and at its leaf continue with `k` in the second phase. -/
private def phaseBody : ITree E α ⊕ ITree E β → m ((ITree E α ⊕ ITree E β) ⊕ β)
  | .inl s => phaseView h k (shape' s)
  | .inr u => Sum.map Sum.inr id <$> interpStep h u

/-- The nested form of the two-phase body: the first phase is an inner loop that exits into
the outer loop when it reaches a leaf, and the second phase exits after every step. -/
private def nestedBody :
    ITree E α ⊕ ITree E β → m ((ITree E α ⊕ ITree E β) ⊕ ((ITree E α ⊕ ITree E β) ⊕ β))
  | .inl s =>
    match shape' s with
    | .mk (.pure a) _ => (fun y => .inr (Sum.map Sum.inr id y)) <$> interpStep h (k a)
    | .mk .step c => Pure.pure (.inl (.inl (c PUnit.unit)))
    | .mk (.query e) c => (fun b => .inl (.inl (c b))) <$> h e
  | .inr u => (fun y => .inr (Sum.map Sum.inr id y)) <$> interpStep h u

/-- The body of the first phase alone, exiting into the second phase at a leaf. -/
private def firstBody (s : ITree E α) : m (ITree E α ⊕ ((ITree E α ⊕ ITree E β) ⊕ β)) :=
  match shape' s with
  | .mk (.pure a) _ => (fun y => .inr (Sum.map Sum.inr id y)) <$> interpStep h (k a)
  | .mk .step c => Pure.pure (.inl (c PUnit.unit))
  | .mk (.query e) c => (fun b => .inl (c b)) <$> h e

private theorem map_elim_inr (y : ITree E β ⊕ β) :
    Sum.map (Sum.elim (fun s : ITree E α => bind s k) id) id (Sum.map Sum.inr id y) = y := by
  cases y <;> rfl

/-- The two-phase loop from the first phase is the interpretation of the sequenced tree. -/
private theorem iterM_phaseBody_inl (t : ITree E α) :
    Eqv (iterM (phaseBody h k) (.inl t)) (interp h (bind t k)) := by
  refine LawfulMonadIter.iter_uniform (Sum.elim (fun s => bind s k) id) (phaseBody h k)
    (interpStep h) (fun x => eqv_of_eq ?_) (.inl t)
  rcases x with s | u
  · rcases hs : shape' s with ⟨sh, c⟩
    cases sh with
    | pure a =>
      obtain rfl := eq_pure_of_dest hs
      simp [phaseBody, phaseView, bind_pure_left, Functor.map_map]
    | step =>
      obtain rfl := eq_step_of_dest hs
      simp [phaseBody, phaseView, bind_step]
    | query e =>
      obtain rfl := eq_query_of_dest hs
      simp [phaseBody, phaseView, bind_query, Functor.map_map]
  · simp [phaseBody, Functor.map_map]

omit [MonadIter m] [LawfulMonadIter m] in
/-- Flattening the nested body, through any continuation that turns both continue branches into
continue steps and the exit branch into an exit, gives the two-phase body. -/
private theorem nestedBody_flatten (x : ITree E α ⊕ ITree E β)
    (K : (ITree E α ⊕ ITree E β) ⊕ ((ITree E α ⊕ ITree E β) ⊕ β) →
      m ((ITree E α ⊕ ITree E β) ⊕ β))
    (hl : ∀ y, K (.inl y) = Pure.pure (.inl y))
    (hrl : ∀ y, K (.inr (.inl y)) = Pure.pure (.inl y))
    (hrr : ∀ r, K (.inr (.inr r)) = Pure.pure (.inr r)) :
    nestedBody h k x >>= K = phaseBody h k x := by
  rcases x with s | u
  · rcases hs : shape' s with ⟨sh, c⟩
    cases sh with
    | pure a =>
      obtain rfl := eq_pure_of_dest hs
      simp only [nestedBody, phaseBody, phaseView, shape'_pure, map_eq_pure_bind,
        LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
      exact bind_congr fun y => by cases y <;> simp [hrl, hrr]
    | step =>
      obtain rfl := eq_step_of_dest hs
      simp only [nestedBody, phaseBody, phaseView, shape'_step, LawfulMonad.pure_bind]
      exact hl _
    | query e =>
      obtain rfl := eq_query_of_dest hs
      simp only [nestedBody, phaseBody, phaseView, shape'_query, map_eq_pure_bind,
        LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
      exact bind_congr fun b => hl _
  · simp only [nestedBody, phaseBody, map_eq_pure_bind, LawfulMonad.bind_assoc,
      LawfulMonad.pure_bind]
    exact bind_congr fun y => by cases y <;> simp [hrl, hrr]

/-- The inner loop from the first phase is the interpretation of `t` followed by one step of the
second phase. -/
private theorem iterM_nestedBody_inl (t : ITree E α) :
    Eqv (iterM (nestedBody h k) (.inl t))
      (interp h t >>= fun a => (fun y => Sum.map Sum.inr id y) <$> interpStep h (k a)) := by
  refine eqv_trans (eqv_symm (LawfulMonadIter.iter_uniform Sum.inl (firstBody h k)
    (nestedBody h k) (fun s => eqv_of_eq ?_) t)) ?_
  · rcases hs : shape' s with ⟨sh, c⟩
    cases sh with
    | pure a =>
      obtain rfl := eq_pure_of_dest hs
      simp only [nestedBody, firstBody, shape'_pure, Functor.map_map, Sum.map_inr, id_eq]
    | step =>
      obtain rfl := eq_step_of_dest hs
      simp only [nestedBody, firstBody, shape'_step, map_pure, Sum.map_inl]
    | query e =>
      obtain rfl := eq_query_of_dest hs
      simp only [nestedBody, firstBody, shape'_query, Functor.map_map, Sum.map_inl]
  · refine eqv_trans ?_ (eqv_symm (LawfulMonadIter.iter_natural (interpStep h) _ t))
    refine LawfulMonadIter.iter_eqv (fun s => eqv_of_eq ?_) t
    rcases hs : shape' s with ⟨sh, c⟩
    cases sh with
    | pure a =>
      obtain rfl := eq_pure_of_dest hs
      simp only [firstBody, shape'_pure, interpStep_pure, map_eq_pure_bind, LawfulMonad.bind_assoc,
        LawfulMonad.pure_bind]
    | step =>
      obtain rfl := eq_step_of_dest hs
      simp only [firstBody, shape'_step, interpStep_step, LawfulMonad.pure_bind]
    | query e =>
      obtain rfl := eq_query_of_dest hs
      simp only [firstBody, shape'_query, interpStep_query, map_eq_pure_bind,
        LawfulMonad.bind_assoc, LawfulMonad.pure_bind]

/-- The nested loop from the second phase is the interpretation of the residual. -/
private theorem iterM_iterM_nestedBody_inr (u : ITree E β) :
    Eqv (iterM (iterM (nestedBody h k)) (.inr u)) (interp h u) := by
  refine eqv_symm (LawfulMonadIter.iter_uniform Sum.inr (interpStep h) (iterM (nestedBody h k))
    (fun u => ?_) u)
  refine eqv_trans (LawfulMonadIter.iter_unfold _ _) (eqv_of_eq ?_)
  simp only [nestedBody, map_eq_pure_bind, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]

theorem interp_bind (t : ITree E α) :
    Eqv (interp h (bind t k)) (interp h t >>= fun a => interp h (k a)) := by
  refine eqv_trans (eqv_symm (iterM_phaseBody_inl h k t)) ?_
  have hcod := LawfulMonadIter.iter_codiagonal (nestedBody h k) (.inl t)
  refine eqv_trans (LawfulMonadIter.iter_eqv (fun x => eqv_of_eq
    (nestedBody_flatten h k x _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).symm) (.inl t))
    (eqv_trans (eqv_symm hcod) ?_)
  refine eqv_trans (LawfulMonadIter.iter_unfold _ _) ?_
  refine eqv_trans (bind_eqv (iterM_nestedBody_inl h k t) fun _ => eqv_refl _) ?_
  rw [LawfulMonad.bind_assoc]
  refine bind_eqv (eqv_refl _) fun a => ?_
  refine eqv_trans (eqv_of_eq (bind_map_left _ _ _)) ?_
  refine eqv_trans (bind_eqv (eqv_refl _) fun y => ?_)
    (eqv_symm (LawfulMonadIter.iter_unfold (interpStep h) (k a)))
  rcases y with u | r
  · exact iterM_iterM_nestedBody_inr h k u
  · exact eqv_refl _

end Bind

end ITree
