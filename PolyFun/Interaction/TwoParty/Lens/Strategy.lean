/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

-- The runner equations unfold the generic runner, which has no public constructor equations.
import all PolyFun.Interaction.Basic.Interaction
public import PolyFun.Interaction.TwoParty.Lens.Syntax

/-!
# Strategies and scheduled execution

Strategies use uniform slots at nodes and leaves. Execution uses `InteractionOver.run`
to collect the two terminal actions, then sequences those actions in the same boundary order.
-/

public section

universe u uA uB

namespace Interaction.TwoParty.Lens
open PFunctor FreeM

variable {P : PFunctor.{uA, uB}} (l : PFunctor.Lens P rolePoly.{u})

/-- The unique trivial context decoration. Ownership is carried only by the lens. -/
@[expose, implicit_reducible] def contexts : (s : FreeM P PUnit.{u + 1}) →
    Displayed.Decoration (fun _ => PUnit.{1}) s
  | .pure _ => ⟨⟩
  | .liftBind _ rest => ⟨⟨⟩, fun b => contexts (rest b)⟩

/-- Node slots with a pure terminal payload, used to specify a pure prefix end. -/
abbrev PureEnd (m : Type u → Type u) (agent : Participant.{u})
    (s : FreeM P PUnit.{u + 1}) (Out : PathAlong l s → Type u) : Type u :=
  StrategyOver (paired l m) agent s (contexts s) Out

/-- A strategy with an effect slot at every boundary, including the leaf. -/
abbrev Strategy (m : Type u → Type u) (agent : Participant.{u})
    (s : FreeM P PUnit.{u + 1}) (Out : PathAlong l s → Type u) : Type u :=
  PureEnd l m agent s (fun tr => m (Out tr))

/-- Focal participant strategy. -/
abbrev Focal (m : Type u → Type u) := Strategy l m .focal

/-- Counterpart participant strategy. -/
abbrev Counterpart (m : Type u → Type u) := Strategy l m .counterpart

variable {l} {m : Type u → Type u}

/-- Map pure terminal payloads, preserving every node slot. -/
@[expose] def PureEnd.mapOutput [Functor m] {agent : Participant.{u}} :
    {s : FreeM P PUnit.{u + 1}} → {A B : PathAlong l s → Type u} →
    (∀ tr, A tr → B tr) → PureEnd l m agent s A → PureEnd l m agent s B
  | .pure _, _, _, f, p => f ⟨⟩ p
  | .liftBind a _, _, _, f, p =>
    Choice.map agent (owner l a) (fun x => PureEnd.mapOutput (fun tr => f ⟨x, tr⟩)) <$> p

/-- Include a strategy whose terminal action is pure in the uniform-slot API. -/
@[expose] def PureEnd.toStrategy [Applicative m] {agent : Participant.{u}}
    {s : FreeM P PUnit.{u + 1}} {Out : PathAlong l s → Type u}
    (p : PureEnd l m agent s Out) : Strategy l m agent s Out :=
  PureEnd.mapOutput (fun _ => pure) p

/-- Map the outputs of a strategy after its leaf action. -/
@[expose] def Strategy.mapOutput [Functor m] {agent : Participant.{u}}
    {s : FreeM P PUnit.{u + 1}} {A B : PathAlong l s → Type u}
    (f : ∀ tr, A tr → B tr) (p : Strategy l m agent s A) : Strategy l m agent s B :=
  PureEnd.mapOutput (fun tr => Functor.map (f tr)) p

/-- Merge an action constructing a strategy into that strategy's first slot. -/
@[expose] def Strategy.joinSlot [Monad m] {agent : Participant.{u}} :
    {s : FreeM P PUnit.{u + 1}} → {Out : PathAlong l s → Type u} →
    m (Strategy l m agent s Out) → Strategy l m agent s Out
  | .pure _, _, p => p >>= id
  | .liftBind _ _, _, p => p >>= id

/-- Execute the first slot and retain its payload in a pure slot of the returned strategy. -/
@[expose] def Strategy.splitSlot [Monad m] {agent : Participant.{u}} :
    {s : FreeM P PUnit.{u + 1}} → {Out : PathAlong l s → Type u} →
    Strategy l m agent s Out → m (Strategy l m agent s Out)
  | .pure _, _, p => pure <$> p
  | .liftBind _ _, _, p => pure <$> p

/-- Joining a split slot preserves the original action. -/
@[simp] theorem Strategy.joinSlot_splitSlot [Monad m] [LawfulMonad m]
    {agent : Participant.{u}} {s : FreeM P PUnit.{u + 1}} {Out : PathAlong l s → Type u}
    (p : Strategy l m agent s Out) : Strategy.joinSlot (Strategy.splitSlot p) = p := by
  cases s <;> simp only [Strategy.joinSlot, Strategy.splitSlot, bind_map_left, id_eq]
  all_goals exact bind_pure p

/-- Participant-indexed terminal payloads. -/
@[expose, implicit_reducible] def participantOutputFamily {s : FreeM P PUnit.{u + 1}}
    (OutP OutC : PathAlong l s → Type u) (agent : Participant.{u})
    (tr : PathAlong l s) : Type u :=
  match agent with
  | .focal => OutP tr
  | .counterpart => OutC tr

/-- Collect the separate focal and counterpart outputs. -/
@[expose] def collectParticipantOutputs {s : FreeM P PUnit.{u + 1}}
    {OutP OutC : PathAlong l s → Type u} (tr : PathAlong l s)
    (out : (agent : Participant.{u}) → participantOutputFamily OutP OutC agent tr) :
    OutP tr × OutC tr := (out .focal, out .counterpart)

/-- The profile supplied to the generic runner. -/
@[expose] def participantProfile {s : FreeM P PUnit.{u + 1}}
    {OutP OutC : PathAlong l s → Type u}
    (p : Focal l m s OutP) (c : Counterpart l m s OutC) :
    (agent : Participant.{u}) → PureEnd l m agent s
      (participantOutputFamily (fun tr => m (OutP tr)) (fun tr => m (OutC tr)) agent)
  | .focal => p
  | .counterpart => c

/-- Run the generic interaction, then execute its collected leaf actions in boundary order. -/
@[expose] def runWith [Monad m] (order : Schedule) (s : FreeM P PUnit.{u + 1})
    {OutP OutC : PathAlong l s → Type u}
    (p : Focal l m s OutP) (c : Counterpart l m s OutC) :
    m ((tr : PathAlong l s) × OutP tr × OutC tr) := do
  let ⟨tr, pEnd, cEnd⟩ ← InteractionOver.run (contexts s)
    (participantProfile p c) collectParticipantOutputs (interaction l m order)
  order.seq pEnd cEnd fun a b => pure ⟨tr, a, b⟩

/-- Execute focal slot, counterpart slot, and move exchange at every boundary. -/
@[expose] def run [Monad m] (s : FreeM P PUnit.{u + 1})
    {OutP OutC : PathAlong l s → Type u}
    (p : Focal l m s OutP) (c : Counterpart l m s OutC) :
    m ((tr : PathAlong l s) × OutP tr × OutC tr) := runWith .focalFirst s p c

/-- Terminal actions execute in the selected schedule. -/
@[simp] theorem runWith_done [Monad m] [LawfulMonad m] (order : Schedule)
    {OutP OutC : PathAlong l (Pure.pure (f := FreeM P) PUnit.unit) → Type u}
    (p : m (OutP ⟨⟩)) (c : m (OutC ⟨⟩)) :
    runWith (l := l) order (Pure.pure (f := FreeM P) PUnit.unit) p c =
      order.seq p c (fun a b => pure ⟨⟨⟩, a, b⟩) := by
  simp [runWith, InteractionOver.run, participantProfile, collectParticipantOutputs]

/-- The node equation retains the generic interaction law and the runtime move. -/
theorem runWith_node [Monad m] [LawfulMonad m] (order : Schedule)
    (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    {OutP OutC : PathAlong l (.liftBind a rest) → Type u}
    (p : Focal l m (.liftBind a rest) OutP) (c : Counterpart l m (.liftBind a rest) OutC) :
    runWith order (.liftBind a rest) p c =
      (interaction l m order).interact (γ := PUnit.unit)
        (Cont := fun agent x => PureEnd l m agent (rest (l.toFunB a x))
          (fun tr => participantOutputFamily (fun t => m (OutP t))
            (fun t => m (OutC t)) agent ⟨x, tr⟩))
        (fun | .focal => p | .counterpart => c)
        (fun x cont => do
          let ⟨tr, outP, outC⟩ ← runWith order (rest (l.toFunB a x))
            (cont .focal) (cont .counterpart)
          pure ⟨⟨x, tr⟩, outP, outC⟩) := by
  cases order <;> simp only [runWith, InteractionOver.run, contexts, interaction]
  all_goals
    simp only [step_bind]
    congr 1
    funext x p c
    simp only [Schedule.seq, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
    rfl

/-- Focal-first execution at a leaf runs both terminal actions. -/
@[simp] theorem run_done [Monad m] [LawfulMonad m]
    {OutP OutC : PathAlong l (Pure.pure (f := FreeM P) PUnit.unit) → Type u}
    (p : m (OutP ⟨⟩)) (c : m (OutC ⟨⟩)) :
    run (l := l) (Pure.pure (f := FreeM P) PUnit.unit) p c =
      (do let a ← p; let b ← c; pure ⟨⟨⟩, a, b⟩) := runWith_done .focalFirst p c

/-- Execute a node's two slots and continue along the runtime move. -/
theorem run_node [Monad m] [LawfulMonad m]
    (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    {OutP OutC : PathAlong l (.liftBind a rest) → Type u}
    (p : Focal l m (.liftBind a rest) OutP) (c : Counterpart l m (.liftBind a rest) OutC) :
    run (.liftBind a rest) p c =
      step (owner l a) .focalFirst p c (fun x pn cn => do
        let ⟨tr, op, oc⟩ ← run (rest (l.toFunB a x)) pn cn
        pure ⟨⟨x, tr⟩, op, oc⟩) := runWith_node .focalFirst a rest p c

/-- Joining a focal construction slot preserves its execution before the counterpart slot. -/
theorem run_joinSlot [Monad m] [LawfulMonad m] (s : FreeM P PUnit.{u + 1})
    {OutP OutC : PathAlong l s → Type u}
    (p : m (Focal l m s OutP)) (c : Counterpart l m s OutC) :
    run s (Strategy.joinSlot p) c = (p >>= fun next => run s next c) := by
  cases s with
  | pure a =>
    cases a
    simp only [Strategy.joinSlot, FreeM.pure_eq_pure, run_done, LawfulMonad.bind_assoc, id_eq]
  | liftBind a rest =>
    simp only [Strategy.joinSlot, run_node]
    exact step_joinSlot _ _ _ _

/-- A pure terminal-output map leaves every boundary effect intact. -/
@[simp] theorem PureEnd.mapOutput_id [Functor m] [LawfulFunctor m]
    {agent : Participant.{u}} {s : FreeM P PUnit.{u + 1}}
    {Out : PathAlong l s → Type u} (p : PureEnd l m agent s Out) :
    PureEnd.mapOutput (fun _ x => x) p = p := by
  induction s using FreeM.rec with
  | pure a => rfl
  | liftBind a rest ih =>
    simp only [PureEnd.mapOutput]
    have hf : (fun x => PureEnd.mapOutput (m := m) (agent := agent)
        (A := fun tr => Out ⟨x, tr⟩) (s := rest (l.toFunB a x)) (fun _ y => y)) =
        (fun _ next => next) := by
      funext x next
      exact ih _ next
    exact (congrArg (fun f => Choice.map agent (owner l a) f <$> p) hf).trans
      ((congrArg (fun f => f <$> p) (Choice.map_id agent (owner l a))).trans (id_map p))

/-- Mapping identity over the terminal action preserves a strategy. -/
@[simp] theorem Strategy.mapOutput_id [Functor m] [LawfulFunctor m]
    {agent : Participant.{u}} {s : FreeM P PUnit.{u + 1}}
    {Out : PathAlong l s → Type u} (p : Strategy l m agent s Out) :
    Strategy.mapOutput (fun _ x => x) p = p := by
  unfold Strategy.mapOutput
  have hf : (fun tr => Functor.map (fun x : Out tr => x) (f := m)) =
      (fun _ x => x) := by
    funext tr x
    exact id_map x
  rw [hf, PureEnd.mapOutput_id]

/-- Mapping both terminal outputs preserves the transcript and every scheduled effect. -/
theorem runWith_mapOutput_mapOutput [Monad m] [LawfulMonad m]
    (order : Schedule) (s : FreeM P PUnit.{u + 1})
    {A B C D : PathAlong l s → Type u}
    (f : ∀ tr, A tr → C tr) (g : ∀ tr, B tr → D tr)
    (p : Focal l m s A) (c : Counterpart l m s B) :
    runWith order s (Strategy.mapOutput f p) (Strategy.mapOutput g c) = (do
      let ⟨tr, a, b⟩ ← runWith order s p c
      pure ⟨tr, f tr a, g tr b⟩) := by
  induction s using FreeM.rec with
  | pure a =>
    cases a
    cases order <;>
      simp only [Strategy.mapOutput, PureEnd.mapOutput, FreeM.pure_eq_pure, runWith_done,
      Schedule.seq, bind_map_left, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
  | liftBind a rest ih =>
    simp only [runWith_node, Strategy.mapOutput, PureEnd.mapOutput, interaction,
      step_map, step_bind]
    congr 1
    funext x pn cn
    have ih' := ih (l.toFunB a x) (fun tr => f ⟨x, tr⟩) (fun tr => g ⟨x, tr⟩) pn cn
    simp only [Strategy.mapOutput] at ih'
    rw [ih']
    simp only [LawfulMonad.bind_assoc, LawfulMonad.pure_bind]

/-- Focal-first execution commutes with separate terminal output maps. -/
theorem run_mapOutput_mapOutput [Monad m] [LawfulMonad m]
    (s : FreeM P PUnit.{u + 1}) {A B C D : PathAlong l s → Type u}
    (f : ∀ tr, A tr → C tr) (g : ∀ tr, B tr → D tr)
    (p : Focal l m s A) (c : Counterpart l m s B) :
    run s (Strategy.mapOutput f p) (Strategy.mapOutput g c) = (do
      let ⟨tr, a, b⟩ ← run s p c
      pure ⟨tr, f tr a, g tr b⟩) := runWith_mapOutput_mapOutput .focalFirst s f g p c

/-- Lift a deterministic strategy by inserting pure slots at every boundary. -/
@[expose] def Strategy.liftId [Applicative m] {agent : Participant.{u}} :
    {s : FreeM P PUnit.{u + 1}} → {Out : PathAlong l s → Type u} →
    Strategy l Id agent s Out → Strategy l m agent s Out
  | .pure _, _, p => pure p
  | .liftBind a _, _, p =>
    pure (Choice.map agent (owner l a) (fun _ next => Strategy.liftId next) p)

/-- Deterministic leaf lifting inserts a pure terminal action. -/
@[simp] theorem Strategy.liftId_done [Applicative m] {agent : Participant.{u}}
    {Out : PathAlong l (Pure.pure (f := FreeM P) PUnit.unit) → Type u} (p : Out ⟨⟩) :
    Strategy.liftId (l := l) (m := m) (agent := agent) (s := .pure PUnit.unit) p = pure p := rfl

/-- Deterministic node lifting preserves the move and lifts every continuation. -/
theorem Strategy.liftId_node [Applicative m] {agent : Participant.{u}}
    (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    {Out : PathAlong l (.liftBind a rest) → Type u}
    (p : Strategy l Id agent (.liftBind a rest) Out) :
    Strategy.liftId (m := m) p =
      pure (Choice.map agent (owner l a) (fun _ next => Strategy.liftId next) p) := rfl

/-- Sender execution runs the focal slot before the counterpart observation slot. -/
theorem run_sender [Monad m] [LawfulMonad m]
    (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1}) (h : owner l a = .sender)
    {OutP OutC : PathAlong l (.liftBind a rest) → Type u}
    (p : Focal l m (.liftBind a rest) OutP) (c : Counterpart l m (.liftBind a rest) OutC) :
    run (.liftBind a rest) p c = (do
      let v ← (show m ((x : Move l a) × Focal l m (rest (l.toFunB a x))
        (fun tr => OutP ⟨x, tr⟩)) from cast (congrArg (fun role => m (Choice .focal role (Move l a)
          (fun x => Focal l m (rest (l.toFunB a x)) (fun tr => OutP ⟨x, tr⟩)))) h) p)
      let f ← (show m ((x : Move l a) → Counterpart l m (rest (l.toFunB a x))
        (fun tr => OutC ⟨x, tr⟩)) from
          cast (congrArg (fun role => m (Choice .counterpart role (Move l a)
          (fun x => Counterpart l m (rest (l.toFunB a x)) (fun tr => OutC ⟨x, tr⟩)))) h) c)
      let ⟨tr, op, oc⟩ ← run (rest (l.toFunB a v.1)) v.2 (f v.1)
      pure ⟨⟨v.1, tr⟩, op, oc⟩) := by
  rw [run_node]
  exact step_sender (owner l a) h p c _

/-- Receiver execution runs the focal observation slot before the counterpart choice slot. -/
theorem run_receiver [Monad m] [LawfulMonad m]
    (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1}) (h : owner l a = .receiver)
    {OutP OutC : PathAlong l (.liftBind a rest) → Type u}
    (p : Focal l m (.liftBind a rest) OutP) (c : Counterpart l m (.liftBind a rest) OutC) :
    run (.liftBind a rest) p c = (do
      let f ← (show m ((x : Move l a) → Focal l m (rest (l.toFunB a x))
        (fun tr => OutP ⟨x, tr⟩)) from cast (congrArg (fun role => m (Choice .focal role (Move l a)
          (fun x => Focal l m (rest (l.toFunB a x)) (fun tr => OutP ⟨x, tr⟩)))) h) p)
      let v ← (show m ((x : Move l a) × Counterpart l m (rest (l.toFunB a x))
        (fun tr => OutC ⟨x, tr⟩)) from
          cast (congrArg (fun role => m (Choice .counterpart role (Move l a)
          (fun x => Counterpart l m (rest (l.toFunB a x)) (fun tr => OutC ⟨x, tr⟩)))) h) c)
      let ⟨tr, op, oc⟩ ← run (rest (l.toFunB a v.1)) (f v.1) v.2
      pure ⟨⟨v.1, tr⟩, op, oc⟩) := by
  rw [run_node]
  exact step_receiver (owner l a) h p c _

end Interaction.TwoParty.Lens
