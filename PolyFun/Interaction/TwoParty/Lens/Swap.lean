/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.TwoParty.Lens.Strategy

/-!
# Ownership exchange

Swapping ownership preserves runtime moves and source branches. Exchanging the participants
also exchanges the boundary schedule; focal-first execution becomes counterpart-first execution.
-/

public section

universe u uA uB
namespace Interaction.TwoParty.Lens
open PFunctor
open FreeM (PathAlong)

/-- Exchange ownership of a move. -/
@[expose, implicit_reducible] def swapRole : Role → Role
  | .sender => .receiver
  | .receiver => .sender

@[simp] theorem swapRole_swapRole (r : Role) : swapRole (swapRole r) = r := by
  cases r <;> rfl

/-- Exchange the two participants. -/
@[expose, implicit_reducible] def Participant.swap : Participant.{u} → Participant.{u}
  | .focal => .counterpart
  | .counterpart => .focal

@[simp] theorem Participant.swap_swap (agent : Participant.{u}) : agent.swap.swap = agent := by
  cases agent <;> rfl

/-- Swap the ownership component without changing the move carrier. -/
@[expose] def rolePoly.swapLens : PFunctor.Lens rolePoly.{u} rolePoly.{u} where
  toFunA r := (swapRole r.1, r.2)
  toFunB _ x := x

/-- Swapping the ownership polynomial twice is the identity lens. -/
theorem rolePoly.swapLens_involutive :
    rolePoly.swapLens.comp rolePoly.swapLens = PFunctor.Lens.id rolePoly.{u} := by
  apply PFunctor.Lens.ext
  · intro a; cases a with | mk role X => cases role <;> rfl
  · intro a; cases a with | mk role X => cases role <;> rfl

variable {P : PFunctor.{uA, uB}}

/-- Swap ownership in an arbitrary source lens. -/
@[expose, implicit_reducible] def swapLens (l : PFunctor.Lens P rolePoly.{u}) :
    PFunctor.Lens P rolePoly.{u} where
  toFunA a := (swapRole (owner l a), Move l a)
  toFunB := l.toFunB

/-- Ownership swapping is an involution on source lenses. -/
@[simp] theorem swapLens_swapLens (l : PFunctor.Lens P rolePoly.{u}) :
    swapLens (swapLens l) = l := by
  change rolePoly.swapLens.comp (rolePoly.swapLens.comp l) = l
  rw [← PFunctor.Lens.comp_assoc, rolePoly.swapLens_involutive, PFunctor.Lens.id_comp]

/-- Exchange local participant payloads when ownership is swapped. -/
@[expose] def Choice.swap {X : Type u} {A : X → Type u}
    (agent : Participant.{u}) (role : Role) :
    Choice agent role X A → Choice agent.swap (swapRole role) X A := by
  cases agent <;> cases role <;> exact id

variable {l : PFunctor.Lens P rolePoly.{u}} {m : Type u → Type u}

/-- Transport a participant strategy across ownership exchange on the same source tree. -/
@[expose] def Strategy.swap [Functor m] {agent : Participant.{u}} :
    {s : FreeM P PUnit.{u + 1}} → {Out : PathAlong l s → Type u} →
    Strategy l m agent s Out → Strategy (swapLens l) m agent.swap s Out
  | .pure _, _, p => p
  | .liftBind a _, _, p =>
    (fun v => Choice.swap agent (owner l a)
      (Choice.map agent (owner l a) (fun _ next => Strategy.swap next) v)) <$> p

/-- Swapped ownership is the exchanged source owner. -/
@[simp] theorem owner_swapLens (l : PFunctor.Lens P rolePoly.{u}) (a : P.A) :
    owner (swapLens l) a = swapRole (owner l a) := rfl

/-- Local participant exchange reverses the boundary schedule. -/
theorem step_swap_map [Monad m] [LawfulMonad m]
    {X : Type u} {A B A' B' : X → Type u} {R : Type u}
    (role : Role) (p : m (Choice .focal role X A))
    (c : m (Choice .counterpart role X B))
    (f : ∀ x, A x → A' x) (g : ∀ x, B x → B' x)
    (k : ∀ x, B' x → A' x → m R) :
    step (swapRole role) .focalFirst
      ((fun v => Choice.swap .counterpart role (Choice.map .counterpart role g v)) <$> c)
      ((fun v => Choice.swap .focal role (Choice.map .focal role f v)) <$> p) k =
    step role .counterpartFirst p c (fun x a b => k x (g x b) (f x a)) := by
  cases role <;> simp only [step, Schedule.seq, Choice.map, Choice.swap,
    swapRole, bind_map_left, id_eq]

/-- Exchanging participants exchanges outputs against the counterpart-first schedule. -/
theorem run_swap [Monad m] [LawfulMonad m] (s : FreeM P PUnit.{u + 1})
    {OutP OutC : PathAlong l s → Type u}
    (p : Focal l m s OutP) (c : Counterpart l m s OutC) :
    run (l := swapLens l) s (Strategy.swap c) (Strategy.swap p) = (do
      let ⟨tr, op, oc⟩ ← runWith .counterpartFirst s p c
      pure ⟨tr, oc, op⟩) := by
  induction s using FreeM.rec with
  | pure a =>
    cases a
    simp only [run, Strategy.swap, FreeM.pure_eq_pure, runWith_done,
      Schedule.seq, bind_assoc, pure_bind]
  | liftBind a rest ih =>
    change runWith .focalFirst (.liftBind a rest) (Strategy.swap c) (Strategy.swap p) = _
    rw [runWith_node (l := swapLens l), runWith_node (l := l)]
    simp only [interaction, Strategy.swap, owner_swapLens,
      step_bind]
    rw [step_swap_map]
    congr 1
    funext x pn cn
    have ih' := ih (l.toFunB a x) pn cn
    simp only [run] at ih'
    refine (congrArg (fun action => action >>= fun result =>
      pure (⟨⟨x, result.1⟩, result.2⟩ :
        (tr : PathAlong l (.liftBind a rest)) × OutC tr × OutP tr)) ih').trans ?_
    simp only [bind_assoc, pure_bind]

end Interaction.TwoParty.Lens
