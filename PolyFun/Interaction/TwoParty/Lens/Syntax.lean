/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.TwoParty.Lens.Signature
public import PolyFun.Interaction.Basic.Interaction

/-!
# Uniform boundary slots

Both participants have one action before each move. An owner's action returns a move
and continuation; an observer's action returns an entire continuation function.
-/

public section

universe u uA uB

namespace Interaction.TwoParty.Lens
open PFunctor

/-- The pure payload of a participant's node slot. -/
@[expose, implicit_reducible] def Choice (agent : Participant.{u}) (role : Role)
    (X : Type u) (Cont : X → Type u) : Type u :=
  match agent, role with
  | .focal, .sender | .counterpart, .receiver => (x : X) × Cont x
  | .focal, .receiver | .counterpart, .sender => (x : X) → Cont x

/-- Map the continuations inside a slot payload. -/
@[expose] def Choice.map {X : Type u} {A B : X → Type u}
    (agent : Participant.{u}) (role : Role) (f : ∀ x, A x → B x) :
    Choice agent role X A → Choice agent role X B :=
  match agent, role with
  | .focal, .sender | .counterpart, .receiver => fun v => ⟨v.1, f v.1 v.2⟩
  | .focal, .receiver | .counterpart, .sender => fun v x => f x (v x)

/-- Identity continuation maps preserve the local payload. -/
@[simp] theorem Choice.map_id {X : Type u} {A : X → Type u}
    (agent : Participant.{u}) (role : Role) :
    Choice.map (A := A) agent role (fun _ x => x) = id := by
  cases agent <;> cases role <;> rfl

/-- Successive continuation maps compose inside a local payload. -/
theorem Choice.map_comp {X : Type u} {A B C : X → Type u}
    (agent : Participant.{u}) (role : Role) (f : ∀ x, A x → B x) (g : ∀ x, B x → C x) :
    Choice.map agent role g ∘ Choice.map agent role f =
      Choice.map agent role (fun x a => g x (f x a)) := by
  cases agent <;> cases role <;> rfl

variable {P : PFunctor.{uA, uB}} (l : PFunctor.Lens P rolePoly.{u})

/-- Paired syntax whose metadata is trivial and whose ownership comes from the lens. -/
@[expose, implicit_reducible] def paired (m : Type u → Type u) :
    SyntaxOver l Participant.{u} (fun _ => PUnit.{1}) where
  Node agent a _ Cont := m (Choice agent (owner l a) (Move l a) Cont)

/-- The focal participant's slot at a sender node. -/
theorem paired_focal_sender (m : Type u → Type u) (a : P.A)
    (Cont : Move l a → Type u) (h : owner l a = .sender) :
    (paired l m).Node .focal a PUnit.unit Cont = m ((x : Move l a) × Cont x) := by
  simp only [paired, Choice, h]

/-- The focal participant's slot at a receiver node. -/
theorem paired_focal_receiver (m : Type u → Type u) (a : P.A)
    (Cont : Move l a → Type u) (h : owner l a = .receiver) :
    (paired l m).Node .focal a PUnit.unit Cont = m ((x : Move l a) → Cont x) := by
  simp only [paired, Choice, h]

/-- The counterpart participant's slot at a sender node. -/
theorem paired_counterpart_sender (m : Type u → Type u) (a : P.A)
    (Cont : Move l a → Type u) (h : owner l a = .sender) :
    (paired l m).Node .counterpart a PUnit.unit Cont = m ((x : Move l a) → Cont x) := by
  simp only [paired, Choice, h]

/-- The counterpart participant's slot at a receiver node. -/
theorem paired_counterpart_receiver (m : Type u → Type u) (a : P.A)
    (Cont : Move l a → Type u) (h : owner l a = .receiver) :
    (paired l m).Node .counterpart a PUnit.unit Cont = m ((x : Move l a) × Cont x) := by
  simp only [paired, Choice, h]

/-- Continuation maps preserve the boundary slot and its selected move. -/
@[expose] def shape (m : Type u → Type u) [Functor m] :
    ShapeOver l Participant.{u} (fun _ => PUnit.{1}) where
  toSyntaxOver := paired l m
  map := fun {agent} {pos} {_γ} {_A} {_B} f node => Choice.map agent (owner l pos) f <$> node

/-- Sequence a pair of slots in the chosen order. -/
@[expose] def Schedule.seq {m : Type u → Type u} [Monad m]
    (order : Schedule) {A B R : Type u} (p : m A) (c : m B) (k : A → B → m R) : m R :=
  match order with
  | .focalFirst => do let a ← p; let b ← c; k a b
  | .counterpartFirst => do let b ← c; let a ← p; k a b

/-- Exchange the owner's move after sequencing both slots. -/
@[expose] def step {m : Type u → Type u} [Monad m] {X : Type u}
    {A B : X → Type u} {R : Type u} (role : Role) (order : Schedule) :
    m (Choice .focal role X A) → m (Choice .counterpart role X B) →
    ((x : X) → A x → B x → m R) → m R :=
  match role with
  | .sender => fun p c k => order.seq p c (fun v f => k v.1 v.2 (f v.1))
  | .receiver => fun p c k => order.seq p c (fun f v => k v.1 (f v.1) v.2)

/-- Exchange a move after both participants have executed their boundary slots. -/
@[expose] def interaction (m : Type u → Type u) [Monad m] (order : Schedule) :
    InteractionOver l Participant.{u} (fun _ => PUnit.{1}) (paired l m) m where
  interact := fun {pos} {_γ} {_Cont} {_Result} profile k =>
    step (owner l pos) order (profile .focal) (profile .counterpart)
      (fun x p c => k x (fun | .focal => p | .counterpart => c))

/-- Mapping continuations changes only the continuations passed to the execution law. -/
theorem step_map {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {X : Type u} {A B A' B' : X → Type u} {R : Type u}
    (role : Role) (order : Schedule)
    (p : m (Choice .focal role X A)) (c : m (Choice .counterpart role X B))
    (f : ∀ x, A x → A' x) (g : ∀ x, B x → B' x)
    (k : ∀ x, A' x → B' x → m R) :
    step role order (Choice.map .focal role f <$> p)
      (Choice.map .counterpart role g <$> c) k =
    step role order p c (fun x a b => k x (f x a) (g x b)) := by
  cases role <;> cases order <;>
    simp only [step, Schedule.seq, Choice.map, bind_map_left]

/-- Map only the counterpart continuations in a local exchange. -/
theorem step_map_right {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {X : Type u} {A B B' : X → Type u} {R : Type u}
    (role : Role) (order : Schedule)
    (p : m (Choice .focal role X A)) (c : m (Choice .counterpart role X B))
    (g : ∀ x, B x → B' x) (k : ∀ x, A x → B' x → m R) :
    step role order p (Choice.map .counterpart role g <$> c) k =
      step role order p c (fun x a b => k x a (g x b)) := by
  cases role <;> cases order <;> simp only [step, Schedule.seq, Choice.map, bind_map_left]

/-- Map only the focal continuations in a local exchange. -/
theorem step_map_left {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {X : Type u} {A A' B : X → Type u} {R : Type u}
    (role : Role) (order : Schedule)
    (p : m (Choice .focal role X A)) (c : m (Choice .counterpart role X B))
    (f : ∀ x, A x → A' x) (k : ∀ x, A' x → B x → m R) :
    step role order (Choice.map .focal role f <$> p) c k =
      step role order p c (fun x a b => k x (f x a) b) := by
  cases role <;> cases order <;> simp only [step, Schedule.seq, Choice.map, bind_map_left]

/-- A continuation after a local exchange can be moved inside that exchange. -/
theorem step_bind {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {X : Type u} {A B : X → Type u} {R S : Type u}
    (role : Role) (order : Schedule)
    (p : m (Choice .focal role X A)) (c : m (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → m R) (f : R → m S) :
    step role order p c k >>= f = step role order p c (fun x a b => k x a b >>= f) := by
  cases role <;> cases order <;> simp only [step, Schedule.seq, bind_assoc]

/-- A focal construction action is part of its first boundary slot. -/
theorem step_joinSlot {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {X : Type u} {A B : X → Type u} {R : Type u} (role : Role)
    (p : m (m (Choice .focal role X A))) (c : m (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → m R) :
    step role .focalFirst (p >>= id) c k =
      (p >>= fun next => step role .focalFirst next c k) := by
  cases role <;> simp only [step, Schedule.seq, bind_assoc, id_eq]

/-- Execute a sender exchange after specializing its ownership equation. -/
theorem step_sender {m : Type u → Type u} [Monad m]
    {X : Type u} {A B : X → Type u} {R : Type u}
    (role : Role) (h : role = .sender)
    (p : m (Choice .focal role X A)) (c : m (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → m R) :
    step role .focalFirst p c k = (do
      let v ← cast (congrArg (fun r => m (Choice .focal r X A)) h) p
      let f ← cast (congrArg (fun r => m (Choice .counterpart r X B)) h) c
      k v.1 v.2 (f v.1)) := by
  cases h
  rfl

/-- Execute a receiver exchange after specializing its ownership equation. -/
theorem step_receiver {m : Type u → Type u} [Monad m]
    {X : Type u} {A B : X → Type u} {R : Type u}
    (role : Role) (h : role = .receiver)
    (p : m (Choice .focal role X A)) (c : m (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → m R) :
    step role .focalFirst p c k = (do
      let f ← cast (congrArg (fun r => m (Choice .focal r X A)) h) p
      let v ← cast (congrArg (fun r => m (Choice .counterpart r X B)) h) c
      k v.1 (f v.1) v.2) := by
  cases h
  rfl

end Interaction.TwoParty.Lens
