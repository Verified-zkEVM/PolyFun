/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Rec
public import PolyFun.ITree.Sim.Facts

/-! # Laws for recursive ITree procedures

Characteristic equations for `ITree.interpMrec`, `ITree.mutualRec`, and
`ITree.fixRec`. The one-step equations are exact because `interpMrec` is a
direct `PFunctor.M.corec`; recursive calls are guarded by one silent step and
external events remain visible.

The algebraic laws follow `Interp/RecursionFacts.v` from the Rocq ITree
library, adapted to PolyFun's polynomial event signatures and M-type
implementation.
-/

@[expose] public section

universe uDA uEA uGA uB uα uβ uCallA

namespace ITree

variable {D : PFunctor.{uDA, uB}} {E : PFunctor.{uEA, uB}}
  {α : Type uα} {β : Type uβ}

variable (body : ∀ a : D.A,
  ITree (D + E : PFunctor.{max uDA uEA, uB}) (D.B a))

@[simp] theorem interpMrec_pure (r : α) :
    interpMrec body
      (pure (F := (D + E : PFunctor.{max uDA uEA, uB})) r) = pure r := by
  have hstep :
      mutualRecStep body
          (pure (F := (D + E : PFunctor.{max uDA uEA, uB})) r) =
        ⟨.pure r, PEmpty.elim⟩ := by
    simp [mutualRecStep]
  apply PFunctor.M.eq_of_dest_eq
  rw [interpMrec, PFunctor.M.dest_corec_eq _ _ hstep]
  unfold ITree.pure
  rw [PFunctor.M.dest_mk]
  congr 1
  funext b
  exact b.elim

@[simp] theorem interpMrec_step
    (t : ITree (D + E : PFunctor.{max uDA uEA, uB}) α) :
    interpMrec body (step t) = step (interpMrec body t) := by
  have hstep : mutualRecStep body (step t) =
      ⟨.step, fun _ => t⟩ := by
    simp [mutualRecStep]
  apply PFunctor.M.eq_of_dest_eq
  rw [interpMrec, PFunctor.M.dest_corec_eq _ _ hstep]
  unfold ITree.step
  rw [PFunctor.M.dest_mk]
  rfl

@[simp] theorem interpMrec_query_recursive (d : D.A)
    (k : D.B d → ITree (D + E : PFunctor.{max uDA uEA, uB}) α) :
    interpMrec body (query (.inl d) k) =
      step (interpMrec body (bind (body d) k)) := by
  have hstep : mutualRecStep body (query (.inl d) k) =
      ⟨.step, fun _ => bind (body d) k⟩ := by
    simp [mutualRecStep]
  apply PFunctor.M.eq_of_dest_eq
  rw [interpMrec, PFunctor.M.dest_corec_eq _ _ hstep]
  unfold ITree.step
  rw [PFunctor.M.dest_mk]
  rfl

@[simp] theorem interpMrec_query_external (e : E.A)
    (k : E.B e → ITree (D + E : PFunctor.{max uDA uEA, uB}) α) :
    interpMrec body (query (.inr e) k) =
      query e (fun b => interpMrec body (k b)) := by
  have hstep : mutualRecStep body (query (.inr e) k) =
      ⟨.query e, k⟩ := by
    simp [mutualRecStep]
  apply PFunctor.M.eq_of_dest_eq
  rw [interpMrec, PFunctor.M.dest_corec_eq _ _ hstep]
  unfold ITree.query
  rw [PFunctor.M.dest_mk]
  rfl

/-- Recursive interpretation is a monad morphism: it commutes with bind
exactly, including across recursive calls. -/
theorem interpMrec_bind
    (t : ITree (D + E : PFunctor.{max uDA uEA, uB}) α)
    (k : α → ITree (D + E : PFunctor.{max uDA uEA, uB}) β) :
    interpMrec body (bind t k) =
      bind (interpMrec body t) (fun a => interpMrec body (k a)) := by
  let next : α → ITree E β := fun a => interpMrec body (k a)
  refine PFunctor.M.bisim
    (fun (u v : ITree E β) =>
      u = v ∨ ∃ t : ITree (D + E : PFunctor.{max uDA uEA, uB}) α,
        u = interpMrec body (bind t k) ∧
        v = bind (interpMrec body t) next)
    ?_ _ _ (Or.inr ⟨t, rfl, rfl⟩)
  rintro u v (rfl | ⟨t, rfl, rfl⟩)
  · rcases h : PFunctor.M.dest u with ⟨sh, c⟩
    exact ⟨sh, c, c, rfl, rfl, fun _ => Or.inl rfl⟩
  · rcases h : PFunctor.M.dest t with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have ht : t = pure r := by
          apply PFunctor.M.eq_of_dest_eq
          rw [h]
          change (⟨.pure r, c⟩ :
              (Poly (D + E : PFunctor.{max uDA uEA, uB}) α).Obj _) =
            ⟨.pure r, PEmpty.elim⟩
          congr 1
          funext z
          exact z.elim
        subst ht
        rw [bind_pure_left, interpMrec_pure, bind_pure_left]
        rcases hk : shape' (interpMrec body (k r)) with ⟨sh', c'⟩
        exact ⟨sh', c', c', hk, hk, fun _ => Or.inl rfl⟩
    | step =>
        have ht : t = step (c PUnit.unit) := by
          apply PFunctor.M.eq_of_dest_eq
          rw [h]
          rfl
        subst ht
        rw [bind_step, interpMrec_step, interpMrec_step, bind_step]
        exact ⟨.step,
          fun _ => interpMrec body (bind (c PUnit.unit) k),
          fun _ => bind (interpMrec body (c PUnit.unit)) next,
          shape'_step _, shape'_step _,
          fun _ => Or.inr ⟨c PUnit.unit, rfl, rfl⟩⟩
    | query event =>
        cases event with
        | inl d =>
            change D.B d →
              ITree (D + E : PFunctor.{max uDA uEA, uB}) α at c
            have ht : t = query (Sum.inl d) c := by
              apply PFunctor.M.eq_of_dest_eq
              rw [h]
              rfl
            subst ht
            clear h
            rw [bind_query, interpMrec_query_recursive,
              interpMrec_query_recursive, bind_step]
            have hassoc :
                bind (body d) (fun b => bind (c b) k) =
                  bind (bind (body d) c) k :=
              (bind_assoc (body d) c k).symm
            exact ⟨.step,
              fun _ => interpMrec body
                (bind (body d) (fun b => bind (c b) k)),
              fun _ => bind (interpMrec body (bind (body d) c)) next,
              shape'_step _, shape'_step _,
              fun _ => Or.inr ⟨bind (body d) c,
                congrArg (interpMrec body) hassoc, rfl⟩⟩
        | inr e =>
            change E.B e →
              ITree (D + E : PFunctor.{max uDA uEA, uB}) α at c
            have ht : t = query (Sum.inr e) c := by
              apply PFunctor.M.eq_of_dest_eq
              rw [h]
              rfl
            subst ht
            clear h
            rw [bind_query, interpMrec_query_external,
              interpMrec_query_external, bind_query]
            exact ⟨.query e,
              fun b => interpMrec body (bind (c b) k),
              fun b => bind (interpMrec body (c b)) next,
              shape'_query _ _, shape'_query _ _,
              fun b => Or.inr ⟨c b, rfl, rfl⟩⟩

/-- Recursive interpretation is natural in the untouched external event
signature. Renaming external events before or after eliminating recursive
calls gives exactly the same tree. -/
theorem mapSpec_interpMrec {G : PFunctor.{uGA, uB}}
    (φ : PFunctor.Lens E G)
    (t : ITree (D + E : PFunctor.{max uDA uEA, uB}) α) :
    mapSpec φ (interpMrec body t) =
      interpMrec
        (fun d => mapSpec
          (PFunctor.Lens.sumMap (PFunctor.Lens.id D) φ) (body d))
        (mapSpec (PFunctor.Lens.sumMap (PFunctor.Lens.id D) φ) t) := by
  let sumLens : PFunctor.Lens
      (D + E : PFunctor.{max uDA uEA, uB})
      (D + G : PFunctor.{max uDA uGA, uB}) :=
    PFunctor.Lens.sumMap (PFunctor.Lens.id D) φ
  let mappedBody : ∀ d : D.A,
      ITree (D + G : PFunctor.{max uDA uGA, uB}) (D.B d) :=
    fun d => mapSpec sumLens (body d)
  refine PFunctor.M.bisim
    (fun (u v : ITree G α) =>
      u = v ∨
      ∃ t : ITree (D + E : PFunctor.{max uDA uEA, uB}) α,
        u = mapSpec φ (interpMrec body t) ∧
        v = interpMrec mappedBody (mapSpec sumLens t))
    ?_ _ _ (Or.inr ⟨t, rfl, rfl⟩)
  rintro u v (rfl | ⟨t, rfl, rfl⟩)
  · rcases h : PFunctor.M.dest u with ⟨sh, c⟩
    exact ⟨sh, c, c, rfl, rfl, fun _ => Or.inl rfl⟩
  · rcases h : PFunctor.M.dest t with ⟨sh, c⟩
    cases sh with
    | pure r =>
        have ht : t = pure r := by
          apply PFunctor.M.eq_of_dest_eq
          rw [h]
          change (⟨.pure r, c⟩ :
              (Poly (D + E : PFunctor.{max uDA uEA, uB}) α).Obj _) =
            ⟨.pure r, PEmpty.elim⟩
          congr 1
          funext z
          exact z.elim
        subst ht
        rw [interpMrec_pure, mapSpec_pure, mapSpec_pure, interpMrec_pure]
        exact ⟨.pure r, PEmpty.elim, PEmpty.elim,
          shape'_pure _, shape'_pure _, fun z => z.elim⟩
    | step =>
        have ht : t = step (c PUnit.unit) := by
          apply PFunctor.M.eq_of_dest_eq
          rw [h]
          rfl
        subst ht
        rw [interpMrec_step, mapSpec_step, mapSpec_step, interpMrec_step]
        exact ⟨.step,
          fun _ => mapSpec φ (interpMrec body (c PUnit.unit)),
          fun _ => interpMrec mappedBody (mapSpec sumLens (c PUnit.unit)),
          shape'_step _, shape'_step _,
          fun _ => Or.inr ⟨c PUnit.unit, rfl, rfl⟩⟩
    | query event =>
        cases event with
        | inl d =>
            change D.B d →
              ITree (D + E : PFunctor.{max uDA uEA, uB}) α at c
            have ht : t = query
                (Sum.inl d :
                  (D + E : PFunctor.{max uDA uEA, uB}).A) c := by
              apply PFunctor.M.eq_of_dest_eq
              rw [h]
              rfl
            subst ht
            clear h
            have hmap :
                mapSpec sumLens (bind (body d) c) =
                  bind (mappedBody d) (fun b => mapSpec sumLens (c b)) := by
              simpa only [mappedBody] using
                mapSpec_bind (α := D.B d) (β := α) sumLens (body d) c
            rw [interpMrec_query_recursive, mapSpec_step, mapSpec_query]
            dsimp [sumLens, PFunctor.Lens.sumMap, PFunctor.Lens.id]
            rw [interpMrec_query_recursive]
            exact ⟨.step,
              fun _ => mapSpec φ (interpMrec body (bind (body d) c)),
              fun _ => interpMrec mappedBody
                (bind (mappedBody d) (fun b => mapSpec sumLens (c b))),
              shape'_step _, shape'_step _,
              fun _ => Or.inr ⟨bind (body d) c, rfl,
                (congrArg (interpMrec mappedBody) hmap).symm⟩⟩
        | inr e =>
            change E.B e →
              ITree (D + E : PFunctor.{max uDA uEA, uB}) α at c
            have ht : t = query
                (Sum.inr e :
                  (D + E : PFunctor.{max uDA uEA, uB}).A) c := by
              apply PFunctor.M.eq_of_dest_eq
              rw [h]
              rfl
            subst ht
            clear h
            rw [interpMrec_query_external, mapSpec_query, mapSpec_query]
            dsimp [sumLens, PFunctor.Lens.sumMap, PFunctor.Lens.id]
            rw [interpMrec_query_external]
            exact ⟨.query (φ.toFunA e),
              fun b => mapSpec φ
                (interpMrec body (c (φ.toFunB e b))),
              fun b => interpMrec mappedBody
                (mapSpec sumLens (c (φ.toFunB e b))),
              shape'_query _ _, shape'_query _ _,
              fun b => Or.inr ⟨c (φ.toFunB e b), rfl, rfl⟩⟩

/-! ### Recursive interpretation as a handler -/

/-- The canonical handler presenting recursive interpretation as ordinary
ITree simulation. Recursive events invoke `mutualRec body`; external events
are forwarded unchanged. This is the polynomial-functor counterpart of the
upstream ITree handler `mrecursive`. -/
def recursiveHandler :
    Handler (D + E : PFunctor.{max uDA uEA, uB}) E :=
  Handler.case_ (mutualRec body) (Handler.id E)

@[simp] theorem recursiveHandler_inl (d : D.A) :
    recursiveHandler body (.inl d) = mutualRec body d := rfl

@[simp] theorem recursiveHandler_inr (e : E.A) :
    recursiveHandler body (.inr e) = Handler.id E e := rfl

/-- Interpreting a lifted recursive event agrees with the canonical recursive
handler up to the productivity guard inserted by `interpMrec`. -/
theorem interpMrec_lift_inl (d : D.A) :
    WeakBisim
      (interpMrec body
        (lift (F := (D + E : PFunctor.{max uDA uEA, uB})) (.inl d)))
      (recursiveHandler body (.inl d)) := by
  have hbind :
      bind (body d)
          (fun b : D.B d =>
            pure (F := (D + E : PFunctor.{max uDA uEA, uB})) b) =
        body d :=
    bind_pure_right (body d)
  rw [lift, interpMrec_query_recursive]
  change WeakBisim
    (step (interpMrec body
      (bind (body d) (fun b : D.B d =>
        pure (F := (D + E : PFunctor.{max uDA uEA, uB})) b))))
    (mutualRec body d)
  rw [hbind]
  exact step_weakBisim _

/-- Interpreting a lifted external event forwards it through the canonical
recursive handler. The trees are equal before promotion to weak
bisimulation. -/
theorem interpMrec_lift_inr (e : E.A) :
    WeakBisim
      (interpMrec body
        (lift (F := (D + E : PFunctor.{max uDA uEA, uB})) (.inr e)))
      (recursiveHandler body (.inr e)) := by
  rw [lift, interpMrec_query_external, recursiveHandler_inr]
  simp only [interpMrec_pure, Handler.id, lift]
  exact WeakBisim.refl _

/-- Definition bridge: `mutualRec` is the recursive interpreter applied to
one body invocation. The guarded recursive-query equation is
`interpMrec_query_recursive`. -/
theorem mutualRec_eq_interpMrec (d : D.A) :
    mutualRec body d = interpMrec body (body d) := rfl

/-- Definition bridge reducing `fixRec` to `interpMrec`. Combine this with
`interpMrec_query_recursive` to expose the silent guard on a recursive call. -/
theorem fixRec_eq_interpMrec {α : Type uCallA} {β : Type uB}
    (body : α →
      ITree (CallE α β + E : PFunctor.{max uCallA uEA, uB}) β)
    (a : α) :
    fixRec body a = interpMrec (D := CallE α β) body (body a) := rfl

end ITree
