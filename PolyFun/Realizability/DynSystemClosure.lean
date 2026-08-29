/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Realizability.DynSystem

/-!
# Closure of dynamical-system realizability under asynchronous choice

Scheduled interleavings of processes are wrappers of the binary choice product
`DynSystem.choiceProd`: at each step the composite exposes both positions and
a direction selects which side advances while the other is frozen.  This file
proves that realizability is closed under that composite.

The flattened index space of a product polynomial is a sigma type, which no
`StepClass` mixin represents.  `Lens.IsChoiceAdmissible` therefore routes the
partial direction pullback through the *sum of the flattened operand indices*
`p.Idx ⊕ q.Idx`, which `HasSum` represents compositionally; a free `pull?`
field with an enabled-routing law avoids decidable equality on positions,
exactly as in `Lens.IsDynAdmissible`.

A two-stage factoring — realize `choiceProd`, then transport along the lens —
is impossible: the intermediate boundary would need a representation of the
sigma-shaped index space.  `Realization.choiceProd` therefore fuses the
product-state machine with the lens transport, as `seqComp` fuses its phases
on the returning track.

`IsRealizableBy.ulift_wrapChoiceProd` is the universe-normalized form consumed
by the UC bridge: the operands and the composite are all `DynSystem.ulift`s,
the certificate is stated for the composition of `Lens.uliftProd` with
`lens.uliftMap`, and the composite state representation
`ULift (S × T)` is assembled with `StepClass.HasULiftProd`.
-/

@[expose] public section

universe u v uS uA uB vA vB

namespace PFunctor

/- Lean compares the sigma presentations of polynomial objects and indices at
implicit transparency in the flattened maps below. -/
attribute [local implicit_reducible] PFunctor.Obj PFunctor.Idx PFunctor.prod
  PFunctor.ulift PFunctor.Lens.comp PFunctor.Lens.uliftMap
  DynSystem.wrap DynSystem.expose DynSystem.update
  DynSystem.choiceProd DynSystem.ulift

/-! ## The regrouping lens -/

/-- Regroup a product of lifted polynomials into the lift of the product:
positions pair after unlifting, and a lifted composite direction routes to the
side it selects. -/
def Lens.uliftProd (p q : PFunctor.{uA, uB}) :
    Lens
      (PFunctor.prod (PFunctor.ulift.{uA, uB, vA, vB} p)
        (PFunctor.ulift.{uA, uB, vA, vB} q))
      (PFunctor.ulift.{uA, uB, vA, vB} (PFunctor.prod p q)) where
  toFunA x := ULift.up (x.1.down, x.2.down)
  toFunB _ d :=
    d.down.elim (fun d₁ => Sum.inl (ULift.up d₁)) (fun d₂ => Sum.inr (ULift.up d₂))

attribute [local implicit_reducible] Lens.uliftProd

namespace DynSystem

variable {p q r : PFunctor.{u, u}} {S T : Type u}

/-! ## The choice-admissibility certificate -/

/-- Admissibility data for transporting two realizations across a lens out of
a choice product `PFunctor.prod p q ⟹ r`.  The partial pullback lands in the
sum of the flattened operand indices; on every enabled target direction it
routes the lens's dependent pullback to the side it selects, tagged with that
side's exposed position.  No decidable equality on positions is assumed. -/
structure _root_.PFunctor.Lens.IsChoiceAdmissible
    (C : StepClass.{u, v}) [P : C.HasProd] [S : C.HasSum] [O : C.HasOption]
    {p q r : PFunctor.{u, u}}
    (left : Boundary C p) (right : Boundary C q) (target : Boundary C r)
    (lens : Lens (PFunctor.prod p q) r) where
  /-- The lens position map is admissible at paired operand positions. -/
  onPos : C.Hom (P.prod left.pos right.pos) target.pos lens.toFunA
  /-- A first-order partial extension of the routed direction pullback. -/
  pull? : (p.A × q.A) × r.Idx → Option (p.Idx ⊕ q.Idx)
  /-- The routed pullback is admissible. -/
  onPull : C.Hom (P.prod (P.prod left.pos right.pos) target.idx)
    (StepClass.HasOption.option (S.sum left.idx right.idx)) pull?
  /-- On every enabled target direction the extension routes the lens's
  dependent pullback, tagged with the exposing side's position. -/
  pull?_enabled : ∀ (a : p.A × q.A) (d : r.B (lens.toFunA a)),
    pull? (a, ⟨lens.toFunA a, d⟩) =
      some ((lens.toFunB a d).elim
        (fun d₁ => Sum.inl ⟨a.1, d₁⟩) (fun d₂ => Sum.inr ⟨a.2, d₂⟩))

/-- Route a flattened target index back through a choice-product lens at a
supplied pair of source positions, choosing classically on the position tag.
The classical constructor for `Lens.IsChoiceAdmissible.pull?`. -/
def _root_.PFunctor.Lens.pullChoicePosIdx [DecidableEq r.A]
    (lens : Lens (PFunctor.prod p q) r) :
    (p.A × q.A) × r.Idx → Option (p.Idx ⊕ q.Idx) := fun input =>
  if h : input.2.1 = lens.toFunA input.1 then
    some ((lens.toFunB input.1 (h ▸ input.2.2)).elim
      (fun d₁ => Sum.inl ⟨input.1.1, d₁⟩) (fun d₂ => Sum.inr ⟨input.1.2, d₂⟩))
  else none

theorem _root_.PFunctor.Lens.pullChoicePosIdx_enabled [DecidableEq r.A]
    (lens : Lens (PFunctor.prod p q) r) (a : p.A × q.A)
    (d : r.B (lens.toFunA a)) :
    lens.pullChoicePosIdx (a, ⟨lens.toFunA a, d⟩) =
      some ((lens.toFunB a d).elim
        (fun d₁ => Sum.inl ⟨a.1, d₁⟩) (fun d₂ => Sum.inr ⟨a.2, d₂⟩)) := by
  unfold Lens.pullChoicePosIdx
  rw [dif_pos rfl]

/-! ## The fused product-state combinator -/

/-- Product-state realization of a wrapped asynchronous choice.  The private
state pairs the two operand states; the update routes the pulled-back
direction to the side it selects and freezes the other component alongside
it. -/
def Realization.choiceProd
    {C : StepClass.{u, v}} [P : C.HasProd] [Su : C.HasSum] [O : C.HasOption]
    [C.IsDistributive]
    {s : DynSystem S p} {t : DynSystem T q}
    {left : Boundary C p} {right : Boundary C q} {target : Boundary C r}
    {lens : Lens (PFunctor.prod p q) r}
    (R₁ : Realization C left s) (R₂ : Realization C right t)
    (hlens : lens.IsChoiceAdmissible C left right target) :
    Realization C target ((s.choiceProd t).wrap lens) where
  state := P.prod R₁.state R₂.state
  expose_mem :=
    (C.comp_mem (P.map_mem R₁.expose_mem R₂.expose_mem) hlens.onPos).congr
      fun _ => rfl
  update? := fun y =>
    (hlens.pull? ((s.expose y.1.1, t.expose y.1.2), y.2)).bind fun i =>
      i.elim
        (fun i₁ => (R₁.update? (y.1.1, i₁)).map fun n => (n, y.1.2))
        (fun i₂ => (R₂.update? (y.1.2, i₂)).map fun n => (y.1.1, n))
  update_mem := by
    have hpull : C.Hom (P.prod (P.prod R₁.state R₂.state) target.idx)
        (StepClass.HasOption.option (Su.sum left.idx right.idx))
        fun y => hlens.pull? ((s.expose y.1.1, t.expose y.1.2), y.2) :=
      (C.comp_mem
        (P.map_mem (P.map_mem R₁.expose_mem R₂.expose_mem)
          (C.id_mem target.idx))
        hlens.onPull).congr fun _ => rfl
    have hpullState : C.Hom (P.prod (P.prod R₁.state R₂.state) target.idx)
        (P.prod (StepClass.HasOption.option (Su.sum left.idx right.idx))
          (P.prod R₁.state R₂.state))
        fun y => (hlens.pull? ((s.expose y.1.1, t.expose y.1.2), y.2), y.1) :=
      P.pair_mem hpull (P.fst_mem _ _)
    have hleft : C.Hom (P.prod left.idx (P.prod R₁.state R₂.state))
        (StepClass.HasOption.option (P.prod R₁.state R₂.state))
        fun x => (R₁.update? (x.2.1, x.1)).map fun n => (n, x.2.2) := by
      have hreorder : C.Hom (P.prod left.idx (P.prod R₁.state R₂.state))
          (P.prod (P.prod R₁.state left.idx) R₂.state)
          fun x => ((x.2.1, x.1), x.2.2) :=
        P.pair_mem
          (P.pair_mem
            ((C.comp_mem (P.snd_mem _ _) (P.fst_mem _ _)).congr fun _ => rfl)
            (P.fst_mem _ _))
          ((C.comp_mem (P.snd_mem _ _) (P.snd_mem _ _)).congr fun _ => rfl)
      have hstep : C.Hom (P.prod (P.prod R₁.state left.idx) R₂.state)
          (P.prod (StepClass.HasOption.option R₁.state) R₂.state)
          (Prod.map R₁.update? id) :=
        P.map_mem R₁.update_mem (C.id_mem R₂.state)
      have hrepack : C.Hom
          (P.prod (StepClass.HasOption.option R₁.state) R₂.state)
          (StepClass.HasOption.option (P.prod R₁.state R₂.state))
          fun y => y.1.map fun j => (j, y.2) :=
        StepClass.HasOption.omapCtx_mem
          (P.pair_mem (P.fst_mem _ _) (P.snd_mem _ _))
      exact (C.comp_mem hreorder (C.comp_mem hstep hrepack)).congr fun _ => rfl
    have hright : C.Hom (P.prod right.idx (P.prod R₁.state R₂.state))
        (StepClass.HasOption.option (P.prod R₁.state R₂.state))
        fun x => (R₂.update? (x.2.2, x.1)).map fun n => (x.2.1, n) := by
      have hreorder : C.Hom (P.prod right.idx (P.prod R₁.state R₂.state))
          (P.prod (P.prod R₂.state right.idx) R₁.state)
          fun x => ((x.2.2, x.1), x.2.1) :=
        P.pair_mem
          (P.pair_mem
            ((C.comp_mem (P.snd_mem _ _) (P.snd_mem _ _)).congr fun _ => rfl)
            (P.fst_mem _ _))
          ((C.comp_mem (P.snd_mem _ _) (P.fst_mem _ _)).congr fun _ => rfl)
      have hstep : C.Hom (P.prod (P.prod R₂.state right.idx) R₁.state)
          (P.prod (StepClass.HasOption.option R₂.state) R₁.state)
          (Prod.map R₂.update? id) :=
        P.map_mem R₂.update_mem (C.id_mem R₁.state)
      have hrepack : C.Hom
          (P.prod (StepClass.HasOption.option R₂.state) R₁.state)
          (StepClass.HasOption.option (P.prod R₁.state R₂.state))
          fun y => y.1.map fun j => (y.2, j) :=
        StepClass.HasOption.omapCtx_mem
          (P.pair_mem (P.snd_mem _ _) (P.fst_mem _ _))
      exact (C.comp_mem hreorder (C.comp_mem hstep hrepack)).congr fun _ => rfl
    have hroute : C.Hom
        (P.prod (Su.sum left.idx right.idx) (P.prod R₁.state R₂.state))
        (StepClass.HasOption.option (P.prod R₁.state R₂.state))
        fun x => Sum.elim
          (fun i₁ => (R₁.update? (x.2.1, i₁)).map fun n => (n, x.2.2))
          (fun i₂ => (R₂.update? (x.2.2, i₂)).map fun n => (x.2.1, n)) x.1 :=
      StepClass.IsDistributive.elimCtx_mem hleft hright
    exact (C.comp_mem hpullState
      (StepClass.HasOption.obindCtx_mem hroute)).congr fun y => rfl
  update?_enabled := by
    intro st direction
    change r.B (lens.toFunA (s.expose st.1, t.expose st.2)) at direction
    change (hlens.pull? ((s.expose st.1, t.expose st.2),
        ⟨lens.toFunA (s.expose st.1, t.expose st.2), direction⟩)).bind _ =
      some (((s.choiceProd t).wrap lens).update st direction)
    rw [hlens.pull?_enabled, Option.bind_some]
    have hupdate : ((s.choiceProd t).wrap lens).update st direction =
        Sum.elim (fun d => (s.update st.1 d, st.2))
          (fun d => (st.1, t.update st.2 d))
          (lens.toFunB (s.expose st.1, t.expose st.2) direction) := rfl
    rw [hupdate]
    rcases lens.toFunB (s.expose st.1, t.expose st.2) direction with d₁ | d₂
    · rw [Sum.elim_inl, Sum.elim_inl, R₁.update?_enabled, Option.map_some]
      rfl
    · rw [Sum.elim_inr, Sum.elim_inr, R₂.update?_enabled, Option.map_some]
      rfl

/-! ## The universe-normalized combinator -/

/-- Universe-normalized closure under a wrapped asynchronous choice: the form
consumed by the UC bridge.  The operands and the composite are
`DynSystem.ulift`s, the certificate is stated for the composition of
`Lens.uliftProd` with `lens.uliftMap`, and the composite state representation
`ULift (S × T)` is assembled from the operand representations with
`StepClass.HasULiftProd`. -/
theorem IsRealizableBy.ulift_wrapChoiceProd
    {p q r : PFunctor.{uA, uB}} {S T : Type uS}
    {C : StepClass.{max uS uA uB, v}} [P : C.HasProd] [Su : C.HasSum]
    [O : C.HasOption] [C.IsDistributive]
    [U : C.HasULiftProd.{uS, max uA uB}]
    {s : DynSystem S p} {t : DynSystem T q}
    {left : Boundary C (PFunctor.ulift.{uA, uB, max uS uB, max uS uA} p)}
    {right : Boundary C (PFunctor.ulift.{uA, uB, max uS uB, max uS uA} q)}
    {target : Boundary C (PFunctor.ulift.{uA, uB, max uS uB, max uS uA} r)}
    {lens : Lens (PFunctor.prod p q) r}
    (h₁ : IsRealizableBy C left (DynSystem.ulift s))
    (h₂ : IsRealizableBy C right (DynSystem.ulift t))
    (hlens : (Lens.comp
        lens.uliftMap.{uA, uB, uA, uB, max uS uB, max uS uA,
          max uS uB, max uS uA}
        (Lens.uliftProd p q)).IsChoiceAdmissible C left right target) :
    IsRealizableBy C target (DynSystem.ulift ((s.choiceProd t).wrap lens)) := by
  obtain ⟨R₁⟩ := h₁
  obtain ⟨R₂⟩ := h₂
  refine ⟨{
    state := StepClass.HasULiftProd.uliftProd R₁.state R₂.state
    expose_mem :=
      (C.comp_mem (StepClass.HasULiftProd.down_mem R₁.state R₂.state)
        (R₁.choiceProd R₂ hlens).expose_mem).congr fun _ => rfl
    update? := fun y =>
      ((R₁.choiceProd R₂ hlens).update?
          ((ULift.up y.1.down.1, ULift.up y.1.down.2), y.2)).map
        fun x => ULift.up (x.1.down, x.2.down)
    update_mem :=
      (C.comp_mem
        (C.comp_mem
          (P.map_mem (StepClass.HasULiftProd.down_mem R₁.state R₂.state)
            (C.id_mem target.idx))
          (R₁.choiceProd R₂ hlens).update_mem)
        (StepClass.HasOption.omap_mem
          (StepClass.HasULiftProd.up_mem R₁.state R₂.state))).congr
        fun _ => rfl
    update?_enabled := ?_ }⟩
  intro st direction
  change (PFunctor.ulift.{uA, uB, max uS uB, max uS uA} r).B
    ((Lens.comp lens.uliftMap (Lens.uliftProd p q)).toFunA
      ((DynSystem.ulift s).expose (ULift.up st.down.1),
        (DynSystem.ulift t).expose (ULift.up st.down.2))) at direction
  change ((hlens.pull?
      (((DynSystem.ulift s).expose (ULift.up st.down.1),
          (DynSystem.ulift t).expose (ULift.up st.down.2)),
        ⟨(Lens.comp lens.uliftMap (Lens.uliftProd p q)).toFunA
          ((DynSystem.ulift s).expose (ULift.up st.down.1),
            (DynSystem.ulift t).expose (ULift.up st.down.2)),
          direction⟩)).bind fun i =>
    i.elim
      (fun i₁ => (R₁.update? (ULift.up st.down.1, i₁)).map
        fun n => (n, ULift.up st.down.2))
      (fun i₂ => (R₂.update? (ULift.up st.down.2, i₂)).map
        fun n => (ULift.up st.down.1, n))).map
      (fun x => ULift.up (x.1.down, x.2.down)) =
    some ((DynSystem.ulift ((s.choiceProd t).wrap lens)).update st direction)
  rw [hlens.pull?_enabled, Option.bind_some]
  have hRHS : (DynSystem.ulift ((s.choiceProd t).wrap lens)).update st
        direction =
      ULift.up (Sum.elim (fun d => (s.update st.down.1 d, st.down.2))
        (fun d => (st.down.1, t.update st.down.2 d))
        (lens.toFunB (s.expose st.down.1, t.expose st.down.2)
          direction.down)) := rfl
  rw [hRHS]
  have hB' : (Lens.comp lens.uliftMap (Lens.uliftProd p q)).toFunB
      ((DynSystem.ulift s).expose (ULift.up st.down.1),
        (DynSystem.ulift t).expose (ULift.up st.down.2)) direction =
      (lens.toFunB (s.expose st.down.1, t.expose st.down.2)
          direction.down).elim
        (fun d₁ => Sum.inl (ULift.up d₁)) (fun d₂ => Sum.inr (ULift.up d₂)) :=
    rfl
  rw [hB']
  rcases lens.toFunB (s.expose st.down.1, t.expose st.down.2) direction.down
    with d₁ | d₂
  · exact congrArg
      (fun o => Option.map (fun x => ULift.up (x.1.down, x.2.down))
        (Option.map (fun n => (n, ULift.up st.down.2)) o))
      (R₁.update?_enabled (ULift.up st.down.1) (ULift.up d₁))
  · exact congrArg
      (fun o => Option.map (fun x => ULift.up (x.1.down, x.2.down))
        (Option.map (fun n => (ULift.up st.down.1, n)) o))
      (R₂.update?_enabled (ULift.up st.down.2) (ULift.up d₂))

/-- Realizability is closed under a wrapped asynchronous choice, given a
choice-admissibility certificate for the lens. -/
theorem IsRealizableBy.wrapChoiceProd
    {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption]
    [C.IsDistributive]
    {s : DynSystem S p} {t : DynSystem T q}
    {left : Boundary C p} {right : Boundary C q} {target : Boundary C r}
    {lens : Lens (PFunctor.prod p q) r}
    (h₁ : IsRealizableBy C left s) (h₂ : IsRealizableBy C right t)
    (hlens : lens.IsChoiceAdmissible C left right target) :
    IsRealizableBy C target ((s.choiceProd t).wrap lens) := by
  obtain ⟨R₁⟩ := h₁
  obtain ⟨R₂⟩ := h₂
  exact ⟨R₁.choiceProd R₂ hlens⟩

end DynSystem

end PFunctor
