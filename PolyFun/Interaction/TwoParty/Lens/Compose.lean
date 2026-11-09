/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.TwoParty.Lens.Strategy
public import PolyFun.PFunctor.Free.Path.AppendAlong

/-!
# Composition at a boundary

The suffix tree depends on the projected shape path. Suffix strategies may use the full
transcript and private prefix outputs. A focal suffix constructor executes in the prefix leaf
slot and is merged into the suffix's first slot. Counterpart append supports pure prefix ends
and effectful prefix ends whose seam actions satisfy an explicit commutation condition.
-/

public section

universe u uA uB

namespace Interaction.TwoParty.Lens
open PFunctor
open FreeM (Path PathAlong projectPathAlong)

variable {P : PFunctor.{uA, uB}} {l : PFunctor.Lens P rolePoly.{u}}
variable {m : Type u → Type u}

-- Suffix indices reduce through source append and runtime projection during dependent rewriting.
attribute [local implicit_reducible] FreeM.projectPathAlong
  FreeM.projectPathAlongLocalMap FreeM.Displayed.LocalMap.toHom
  FreeM.Displayed.LocalMap.toHomFun PathAlong.append


/-- Graft strategies at pure terminal payloads, following runtime moves through the lens. -/
@[expose] def PureEnd.graft [Functor m] {agent : Participant.{u}} :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Mid : PathAlong l s₁ → Type u} → {Out : PathAlong l (s₁.append s₂) → Type u} →
    PureEnd l m agent s₁ Mid →
    ((tr : PathAlong l s₁) → Mid tr → PureEnd l m agent (s₂ (projectPathAlong l s₁ tr))
      (fun tail => Out (PathAlong.append l s₁ s₂ tr tail))) →
    PureEnd l m agent (s₁.append s₂) Out
  | .pure _, _, _, _, p, f => f ⟨⟩ p
  | .liftBind a _, _, _, _, p, f =>
    Choice.map agent (owner l a) (fun x next =>
      PureEnd.graft next (fun tr => f ⟨x, tr⟩)) <$> p

/-- Compose a focal strategy with an effectful suffix constructor in its leaf slot. -/
@[expose] def Focal.compFlat [Monad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Mid : PathAlong l s₁ → Type u} {Out : PathAlong l (s₁.append s₂) → Type u}
    (p : Focal l m s₁ Mid)
    (f : (tr : PathAlong l s₁) → Mid tr →
      m (Focal l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => Out (PathAlong.append l s₁ s₂ tr tail)))) :
    Focal l m (s₁.append s₂) Out :=
  PureEnd.graft p (fun tr act => Strategy.joinSlot (act >>= f tr))

/-- Compose with a suffix selected without a construction effect. -/
@[expose] def Focal.compFlatPure [Monad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Mid : PathAlong l s₁ → Type u} {Out : PathAlong l (s₁.append s₂) → Type u}
    (p : Focal l m s₁ Mid)
    (f : (tr : PathAlong l s₁) → Mid tr →
      Focal l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => Out (PathAlong.append l s₁ s₂ tr tail))) :
    Focal l m (s₁.append s₂) Out := Focal.compFlat p (fun tr mid => pure (f tr mid))

/-- A pure suffix constructor specializes effectful composition. -/
theorem Focal.compFlat_pure [Monad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Mid : PathAlong l s₁ → Type u} {Out : PathAlong l (s₁.append s₂) → Type u}
    (p : Focal l m s₁ Mid)
    (f : (tr : PathAlong l s₁) → Mid tr →
      Focal l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => Out (PathAlong.append l s₁ s₂ tr tail))) :
    Focal.compFlat p (fun tr mid => pure (f tr mid)) = Focal.compFlatPure p f := rfl

/-- Append a counterpart suffix selected purely from a pure prefix terminal payload. -/
@[expose] def Counterpart.appendFlat [Functor m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Mid : PathAlong l s₁ → Type u} {Out : PathAlong l (s₁.append s₂) → Type u}
    (c : PureEnd l m .counterpart s₁ Mid)
    (f : (tr : PathAlong l s₁) → Mid tr →
      Counterpart l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => Out (PathAlong.append l s₁ s₂ tr tail))) :
    Counterpart l m (s₁.append s₂) Out := PureEnd.graft c f

/-- Append an effectful counterpart prefix, merging its leaf action into the suffix slot. -/
@[expose] def Counterpart.appendFlatM [Monad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Mid : PathAlong l s₁ → Type u} {Out : PathAlong l (s₁.append s₂) → Type u}
    (c : Counterpart l m s₁ Mid)
    (g : (tr : PathAlong l s₁) → Mid tr →
      Counterpart l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => Out (PathAlong.append l s₁ s₂ tr tail))) :
    Counterpart l m (s₁.append s₂) Out :=
  PureEnd.graft c (fun tr act => Strategy.joinSlot (g tr <$> act))

/-- At each counterpart prefix leaf, its action commutes with focal suffix construction
and the first suffix slot, under arbitrary continuations. Node slots retain their effects;
the subtype certificates require the property only of their returned continuations. -/
@[expose] def SeamCommutes [Monad m] :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {MidP MidC : PathAlong l s₁ → Type u} →
    {OutP : PathAlong l (s₁.append s₂) → Type u} →
    Counterpart l m s₁ MidC →
    ((tr : PathAlong l s₁) → MidP tr →
      m (Focal l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => OutP (PathAlong.append l s₁ s₂ tr tail)))) → Prop
  | .pure _, _, _, _, _, c, f =>
    ∀ mid, ActionsCommute (f ⟨⟩ mid >>= Strategy.splitSlot) c
  | .liftBind a rest, s₂, MidP, MidC, OutP, c, f =>
    ∃ checked : m (Choice .counterpart (owner l a) (Move l a) (fun x =>
      {next : Counterpart l m (rest (l.toFunB a x)) (fun tr => MidC ⟨x, tr⟩) //
        SeamCommutes (s₂ := fun tr => s₂ ⟨l.toFunB a x, tr⟩)
          (MidP := fun tr => MidP ⟨x, tr⟩) (OutP := fun tr => OutP ⟨x, tr⟩)
          next (fun tr => f ⟨x, tr⟩)})),
      c = Choice.map .counterpart (owner l a) (fun _ => Subtype.val) <$> checked

/-- Effectful counterpart composition agrees with sequential execution when each seam
leaf commutes with focal suffix construction and its first slot. -/
theorem run_compFlat_appendFlatM [Monad m] [LawfulMonad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {MidP MidC : PathAlong l s₁ → Type u}
    {OutP OutC : PathAlong l (s₁.append s₂) → Type u}
    (p : Focal l m s₁ MidP)
    (f : (tr : PathAlong l s₁) → MidP tr →
      m (Focal l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => OutP (PathAlong.append l s₁ s₂ tr tail))))
    (c : Counterpart l m s₁ MidC)
    (g : (tr : PathAlong l s₁) → MidC tr →
      Counterpart l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => OutC (PathAlong.append l s₁ s₂ tr tail)))
    (h : SeamCommutes c f) :
    run (s₁.append s₂) (Focal.compFlat p f) (Counterpart.appendFlatM c g) = (do
      let ⟨tr, op, oc⟩ ← run s₁ p c
      let next ← f tr op
      let ⟨tail, outP, outC⟩ ← run (s₂ (projectPathAlong l s₁ tr)) next (g tr oc)
      pure ⟨PathAlong.append l s₁ s₂ tr tail, outP, outC⟩) := by
  induction s₁ using FreeM.rec with
  | pure a =>
    cases a
    simp only [Focal.compFlat, Counterpart.appendFlatM, PureEnd.graft,
      run_joinSlot, FreeM.pure_eq_pure, run_done, bind_assoc,
      LawfulMonad.pure_bind, PathAlong.append_pure]
    congr 1
    funext mid
    simp only [run_splitSlot_joinSlot]
    simp only [bind_map_left]
    have comm := h mid ((tr : PathAlong l ((FreeM.pure (P := P) PUnit.unit).append s₂)) ×
      OutP tr × OutC tr) (fun next oc => do
      let ⟨tail, op, outC⟩ ← run (s₂ (projectPathAlong l (.pure PUnit.unit) ⟨⟩)) next (g ⟨⟩ oc)
      pure ⟨PathAlong.append l (.pure PUnit.unit) s₂ ⟨⟩ tail, op, outC⟩)
    simp only [FreeM.pure_eq_pure, bind_assoc, run_splitSlot, PathAlong.append_pure,
      Sigma.eta, Prod.eta, bind_pure] at comm
    convert comm using 1 <;> first | rfl | simp only [Sigma.eta, Prod.eta, bind_pure]
  | liftBind a rest ih =>
    obtain ⟨checked, rfl⟩ := h
    simp only [Focal.compFlat, Counterpart.appendFlatM, PureEnd.graft,
      FreeM.append_liftBind, run_node, step_map_left, step_map_right, step_bind]
    congr 1
    funext x pn cn
    have ih' := ih (l.toFunB a x)
      (s₂ := fun tr => s₂ ⟨l.toFunB a x, tr⟩)
      (OutP := fun tr => OutP ⟨x, tr⟩) (OutC := fun tr => OutC ⟨x, tr⟩)
      pn (fun tr => f ⟨x, tr⟩) cn.val (fun tr => g ⟨x, tr⟩) cn.property
    simp only [Focal.compFlat, Counterpart.appendFlatM] at ih'
    rw [ih']
    simp only [bind_assoc, LawfulMonad.pure_bind, PathAlong.append_liftBind]
    rfl

/-- A pure counterpart prefix end discharges the seam commutation condition. -/
theorem SeamCommutes.toStrategy [Monad m] [LawfulMonad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {MidP MidC : PathAlong l s₁ → Type u}
    {OutP : PathAlong l (s₁.append s₂) → Type u}
    (c : PureEnd l m .counterpart s₁ MidC)
    (f : (tr : PathAlong l s₁) → MidP tr →
      m (Focal l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => OutP (PathAlong.append l s₁ s₂ tr tail)))) :
    SeamCommutes c.toStrategy f := by
  induction s₁ using FreeM.rec with
  | pure a =>
    intro mid
    exact ActionsCommute.pure_right _ _
  | liftBind a rest ih =>
    refine ⟨Choice.map .counterpart (owner l a) (fun x next =>
      ⟨next.toStrategy, ih (l.toFunB a x)
        (s₂ := fun tr => s₂ ⟨l.toFunB a x, tr⟩)
        (MidP := fun tr => MidP ⟨x, tr⟩) (OutP := fun tr => OutP ⟨x, tr⟩)
        next (fun tr => f ⟨x, tr⟩)⟩) <$> c, ?_⟩
    simp only [PureEnd.toStrategy, PureEnd.mapOutput, Functor.map_map,
      ← Function.comp_def, Choice.map_comp]

/-- Compose focal strategies with a factored output family. -/
@[expose] def Focal.comp [Monad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Mid : PathAlong l s₁ → Type u}
    {F : (tr : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ tr)) → Type u}
    (p : Focal l m s₁ Mid)
    (f : (tr : PathAlong l s₁) → Mid tr → m (Focal l m
      (s₂ (projectPathAlong l s₁ tr)) (F tr))) :
    Focal l m (s₁.append s₂) (PathAlong.LiftAppend l s₁ s₂ F) :=
  Focal.compFlat p (fun tr mid =>
    Strategy.mapOutput (fun tail => PathAlong.packAppend l s₁ s₂ F tr tail) <$> f tr mid)

/-- Append counterpart strategies with a factored output family. -/
@[expose] def Counterpart.append [Functor m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Mid : PathAlong l s₁ → Type u}
    {F : (tr : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ tr)) → Type u}
    (c : PureEnd l m .counterpart s₁ Mid)
    (f : (tr : PathAlong l s₁) → Mid tr → Counterpart l m
      (s₂ (projectPathAlong l s₁ tr)) (F tr)) :
    Counterpart l m (s₁.append s₂) (PathAlong.LiftAppend l s₁ s₂ F) :=
  Counterpart.appendFlat c (fun tr mid =>
    Strategy.mapOutput (fun tail => PathAlong.packAppend l s₁ s₂ F tr tail) (f tr mid))

/-- The flat presentation of factored focal composition. -/
theorem Focal.comp_eq_compFlat_mapOutput [Monad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Mid : PathAlong l s₁ → Type u}
    {F : (tr : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ tr)) → Type u}
    (p : Focal l m s₁ Mid)
    (f : (tr : PathAlong l s₁) → Mid tr → m (Focal l m
      (s₂ (projectPathAlong l s₁ tr)) (F tr))) :
    Focal.comp p f = Focal.compFlat p (fun tr mid =>
      Strategy.mapOutput (fun tail => PathAlong.packAppend l s₁ s₂ F tr tail) <$> f tr mid) := rfl

/-- The flat presentation of factored counterpart append. -/
theorem Counterpart.append_eq_appendFlat_mapOutput [Functor m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Mid : PathAlong l s₁ → Type u}
    {F : (tr : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ tr)) → Type u}
    (c : PureEnd l m .counterpart s₁ Mid)
    (f : (tr : PathAlong l s₁) → Mid tr → Counterpart l m
      (s₂ (projectPathAlong l s₁ tr)) (F tr)) :
    Counterpart.append c f = Counterpart.appendFlat c (fun tr mid =>
      Strategy.mapOutput (fun tail => PathAlong.packAppend l s₁ s₂ F tr tail) (f tr mid)) := rfl

/-- Split a whole focal strategy, executing its actual seam slot in the prefix leaf.
The returned strategy retains the slot's payload and all private continuations. -/
@[expose] def Focal.splitPrefix [Monad m] :
    {s₁ : FreeM P PUnit.{u + 1}} → {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} →
    {Out : PathAlong l (s₁.append s₂) → Type u} →
    Focal l m (s₁.append s₂) Out → Focal l m s₁ (fun tr =>
      Focal l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => Out (PathAlong.append l s₁ s₂ tr tail)))
  | .pure _, _, _, p => Strategy.splitSlot p
  | .liftBind a _, _, _, p =>
    Choice.map .focal (owner l a) (fun _ next => Focal.splitPrefix next) <$> p

/-- Composed execution equals sequential execution when the counterpart prefix end is pure.
The focal suffix constructor may have arbitrary effects in a lawful monad. -/
theorem run_compFlat_appendFlat [Monad m] [LawfulMonad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {MidP MidC : PathAlong l s₁ → Type u}
    {OutP OutC : PathAlong l (s₁.append s₂) → Type u}
    (p : Focal l m s₁ MidP)
    (f : (tr : PathAlong l s₁) → MidP tr →
      m (Focal l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => OutP (PathAlong.append l s₁ s₂ tr tail))))
    (c : PureEnd l m .counterpart s₁ MidC)
    (g : (tr : PathAlong l s₁) → MidC tr →
      Counterpart l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => OutC (PathAlong.append l s₁ s₂ tr tail))) :
    run (s₁.append s₂) (Focal.compFlat p f) (Counterpart.appendFlat c g) = (do
      let ⟨tr, op, oc⟩ ← run s₁ p c.toStrategy
      let next ← f tr op
      let ⟨tail, outP, outC⟩ ← run (s₂ (projectPathAlong l s₁ tr)) next (g tr oc)
      pure ⟨PathAlong.append l s₁ s₂ tr tail, outP, outC⟩) := by
  induction s₁ using FreeM.rec with
  | pure a =>
    cases a
    simp only [Focal.compFlat, Counterpart.appendFlat, PureEnd.graft,
      PureEnd.toStrategy, PureEnd.mapOutput, run_joinSlot, FreeM.pure_eq_pure, run_done,
      bind_assoc, pure_bind, PathAlong.append_pure]
    simp only [Sigma.eta, Prod.eta, bind_pure]
    rfl
  | liftBind a rest ih =>
    simp only [Focal.compFlat, Counterpart.appendFlat, PureEnd.graft,
      FreeM.append_liftBind, run_node, PureEnd.toStrategy, PureEnd.mapOutput,
      step_map_left, step_map_right, step_bind]
    congr 1
    funext x pn cn
    have ih' := ih (l.toFunB a x)
      (s₂ := fun tr => s₂ ⟨l.toFunB a x, tr⟩)
      (OutP := fun tr => OutP ⟨x, tr⟩) (OutC := fun tr => OutC ⟨x, tr⟩) pn (fun tr => f ⟨x, tr⟩) cn
      (fun tr => g ⟨x, tr⟩)
    simp only [Focal.compFlat, Counterpart.appendFlat] at ih'
    rw [ih']
    simp only [bind_assoc, pure_bind, PathAlong.append_liftBind]
    rfl

/-- Recomposition restores every node and the actual seam slot of a whole strategy. -/
theorem Focal.compFlat_splitPrefix [Monad m] [LawfulMonad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Out : PathAlong l (s₁.append s₂) → Type u}
    (p : Focal l m (s₁.append s₂) Out) :
    Focal.compFlat (Focal.splitPrefix (s₁ := s₁) p) (fun _ next => pure next) = p := by
  induction s₁ using FreeM.rec with
  | pure a =>
    simp only [Focal.compFlat, PureEnd.graft, Focal.splitPrefix, bind_pure]
    exact Strategy.joinSlot_splitSlot p
  | liftBind a rest ih =>
    simp only [Focal.compFlat, PureEnd.graft, Focal.splitPrefix, Functor.map_map]
    simp only [← Function.comp_def, Choice.map_comp]
    have hf : (fun x next => Focal.compFlat (m := m)
        (Focal.splitPrefix (s₁ := rest (l.toFunB a x))
          (s₂ := fun tr => s₂ ⟨l.toFunB a x, tr⟩)
          (Out := fun tr => Out ⟨x, tr⟩) next)
        (fun _ next => pure next)) = (fun _ next => next) := by
      funext x next
      exact ih _ next
    exact (congrArg (fun f => Choice.map .focal (owner l a) f <$> p) hf).trans
      ((congrArg (fun f => f <$> p) (Choice.map_id .focal (owner l a))).trans (id_map p))

/-- Decompose an arbitrary focal strategy using its actual suffix strategy and private memory. -/
theorem run_appendFlat_splitPrefix [Monad m] [LawfulMonad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {MidC : PathAlong l s₁ → Type u}
    {OutP OutC : PathAlong l (s₁.append s₂) → Type u}
    (p : Focal l m (s₁.append s₂) OutP)
    (c : PureEnd l m .counterpart s₁ MidC)
    (g : (tr : PathAlong l s₁) → MidC tr →
      Counterpart l m (s₂ (projectPathAlong l s₁ tr))
        (fun tail => OutC (PathAlong.append l s₁ s₂ tr tail))) :
    run (s₁.append s₂) p (Counterpart.appendFlat c g) = (do
      let ⟨tr, next, oc⟩ ← run s₁ (Focal.splitPrefix p) c.toStrategy
      let ⟨tail, op, outC⟩ ← run (s₂ (projectPathAlong l s₁ tr)) next (g tr oc)
      pure ⟨PathAlong.append l s₁ s₂ tr tail, op, outC⟩) := by
  simpa only [Focal.compFlat_splitPrefix, pure_bind] using
    run_compFlat_appendFlat (Focal.splitPrefix p) (fun _ next => pure next) c g

/-- Factored composition packs the two suffix outputs separately. -/
theorem run_comp_append [Monad m] [LawfulMonad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {MidP MidC : PathAlong l s₁ → Type u}
    {FP FC : (tr : PathAlong l s₁) → PathAlong l (s₂ (projectPathAlong l s₁ tr)) → Type u}
    (p : Focal l m s₁ MidP)
    (f : (tr : PathAlong l s₁) → MidP tr →
      m (Focal l m (s₂ (projectPathAlong l s₁ tr)) (FP tr)))
    (c : PureEnd l m .counterpart s₁ MidC)
    (g : (tr : PathAlong l s₁) → MidC tr →
      Counterpart l m (s₂ (projectPathAlong l s₁ tr)) (FC tr)) :
    run (s₁.append s₂) (Focal.comp p f) (Counterpart.append c g) = (do
      let ⟨tr, op, oc⟩ ← run s₁ p c.toStrategy
      let next ← f tr op
      let ⟨tail, outP, outC⟩ ← run (s₂ (projectPathAlong l s₁ tr)) next (g tr oc)
      pure ⟨PathAlong.append l s₁ s₂ tr tail,
        PathAlong.packAppend l s₁ s₂ FP tr tail outP,
        PathAlong.packAppend l s₁ s₂ FC tr tail outC⟩) := by
  simp only [Focal.comp, Counterpart.append, run_compFlat_appendFlat, bind_map_left,
    run_mapOutput_mapOutput, bind_assoc, pure_bind]

end Interaction.TwoParty.Lens
