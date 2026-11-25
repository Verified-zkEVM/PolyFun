/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import PolyFun.Interaction.TwoParty.Lens.Strategy

/-!
# Public-coin execution and replay

A challenge node exposes its sampler separately from its continuation. Replay follows the
recorded move without executing that sampler, including when the sampler fails.
-/

public section

universe u uA uB

namespace Interaction.TwoParty.Lens
open PFunctor
open FreeM (PathAlong)

variable {P : PFunctor.{uA, uB}} (l : PFunctor.Lens P rolePoly.{u})

/-- A sender move selects a continuation. A receiver node also supplies a challenge draw. -/
@[expose, implicit_reducible] def publicCoinSyntax (m : Type u → Type u) :
    SyntaxOver l PUnit.{u + 1} (fun _ => PUnit.{1}) where
  Node _ a _ (Cont : Move l a → Type u) := match owner l a with
    | .sender => (x : Move l a) → Cont x
    | .receiver => m (Move l a) × ((x : Move l a) → Cont x)

/-- A public-coin counterpart with pure terminal output. -/
abbrev PublicCoinCounterpart (m : Type u → Type u) (s : FreeM P PUnit.{u + 1})
    (Out : PathAlong l s → Type u) :=
  StrategyOver (publicCoinSyntax l m) PUnit.unit s (contexts s) Out

namespace PublicCoinCounterpart
variable {l} {m : Type u → Type u}

/-- Interpret the exposed sampler as the counterpart's challenge slot. -/
@[expose] def toCounterpart [Monad m] : {s : FreeM P PUnit.{u + 1}} →
    {Out : PathAlong l s → Type u} → PublicCoinCounterpart l m s Out → Counterpart l m s Out
  | .pure _, _, p => pure p
  | .liftBind a rest, Out, p =>
    match h : owner l a with
    | .sender => by
      have p' : (x : Move l a) → PublicCoinCounterpart l m
          (rest (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      simpa only [Counterpart, Strategy, PureEnd, StrategyOver, contexts, paired, Choice, h] using
        (pure (fun x => toCounterpart (p' x)) :
          m ((x : Move l a) → Counterpart l m (rest (l.toFunB a x))
            (fun tr => Out ⟨x, tr⟩)))
    | .receiver => by
      have p' : m (Move l a) × ((x : Move l a) → PublicCoinCounterpart l m
          (rest (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩)) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      simpa only [Counterpart, Strategy, PureEnd, StrategyOver, contexts, paired, Choice, h] using
        (do let x ← p'.1; pure ⟨x, toCounterpart (p'.2 x)⟩ :
          m ((x : Move l a) × Counterpart l m (rest (l.toFunB a x))
            (fun tr => Out ⟨x, tr⟩)))

/-- Follow the recorded moves to their terminal output. -/
@[expose] def replay : {s : FreeM P PUnit.{u + 1}} →
    {Out : PathAlong l s → Type u} → PublicCoinCounterpart l m s Out →
    (tr : PathAlong l s) → Out tr
  | .pure _, _, p, _ => p
  | .liftBind a rest, Out, p, ⟨x, tr⟩ =>
    match h : owner l a with
    | .sender =>
      let f : (x : Move l a) → PublicCoinCounterpart l m
          (rest (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      replay (f x) tr
    | .receiver =>
      let p' : m (Move l a) × ((x : Move l a) → PublicCoinCounterpart l m
          (rest (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩)) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      replay (p'.2 x) tr

/-- Map terminal outputs while preserving samplers and observation slots. -/
@[expose] def mapOutput : {s : FreeM P PUnit.{u + 1}} →
    {A B : PathAlong l s → Type u} → (∀ tr, A tr → B tr) →
    PublicCoinCounterpart l m s A → PublicCoinCounterpart l m s B
  | .pure _, _, _, f, p => f ⟨⟩ p
  | .liftBind a rest, A, B, f, p =>
    match h : owner l a with
    | .sender => by
      have p' : (x : Move l a) → PublicCoinCounterpart l m
          (rest (l.toFunB a x)) (fun tr => A ⟨x, tr⟩) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using
        ((fun x => mapOutput (fun tr => f ⟨x, tr⟩) (p' x)) :
          (x : Move l a) → PublicCoinCounterpart l m (rest (l.toFunB a x))
            (fun tr => B ⟨x, tr⟩))
    | .receiver => by
      have p' : m (Move l a) × ((x : Move l a) → PublicCoinCounterpart l m
          (rest (l.toFunB a x)) (fun tr => A ⟨x, tr⟩)) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using
        ((p'.1, fun x => mapOutput (fun tr => f ⟨x, tr⟩) (p'.2 x)) :
          m (Move l a) × ((x : Move l a) → PublicCoinCounterpart l m
            (rest (l.toFunB a x)) (fun tr => B ⟨x, tr⟩)))

/-- Replay returns the terminal output. -/
@[simp] theorem replay_done {Out : PathAlong l (.pure PUnit.unit) → Type u}
    (p : Out ⟨⟩) : replay (l := l) (m := m) (Out := Out) (s := .pure PUnit.unit) p ⟨⟩ = p := rfl

/-- Conversion returns the terminal output with `pure`. -/
@[simp] theorem toCounterpart_done [Monad m] {Out : PathAlong l (.pure PUnit.unit) → Type u}
    (p : Out ⟨⟩) :
    toCounterpart (l := l) (m := m) (Out := Out) (s := .pure PUnit.unit) p = pure p := rfl

/-- Replay at a sender node follows the recorded move. -/
theorem replay_sender (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    (h : owner l a = .sender) {Out : PathAlong l (.liftBind a rest) → Type u}
    (p : PublicCoinCounterpart l m (.liftBind a rest) Out)
    (x : Move l a) (tr : PathAlong l (rest (l.toFunB a x))) :
    replay p ⟨x, tr⟩ =
      let p' : (x : Move l a) → PublicCoinCounterpart l m
        (rest (l.toFunB a x)) (fun t => Out ⟨x, t⟩) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      replay (p' x) tr := by
  simp only [replay]
  split <;> rename_i h' <;> first | rfl | cases h.symm.trans h'

/-- Replay at a receiver node follows the recorded move. -/
theorem replay_receiver (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    (h : owner l a = .receiver) {Out : PathAlong l (.liftBind a rest) → Type u}
    (p : PublicCoinCounterpart l m (.liftBind a rest) Out)
    (x : Move l a) (tr : PathAlong l (rest (l.toFunB a x))) :
    replay p ⟨x, tr⟩ =
      let p' : m (Move l a) × ((x : Move l a) → PublicCoinCounterpart l m
        (rest (l.toFunB a x)) (fun t => Out ⟨x, t⟩)) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      replay (p'.2 x) tr := by
  simp only [replay]
  split <;> rename_i h' <;> first | rfl | cases h.symm.trans h'

/-- Conversion at a sender node returns its observation function with `pure`. -/
theorem toCounterpart_sender [Monad m] (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    (h : owner l a = .sender) {Out : PathAlong l (.liftBind a rest) → Type u}
    (p : PublicCoinCounterpart l m (.liftBind a rest) Out) :
    toCounterpart p =
      let p' : (x : Move l a) → PublicCoinCounterpart l m
        (rest (l.toFunB a x)) (fun t => Out ⟨x, t⟩) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      (show Counterpart l m (.liftBind a rest) Out from by
        simpa only [Counterpart, Strategy, PureEnd, StrategyOver, contexts, paired, Choice, h] using
          (pure (fun x => toCounterpart (p' x)) :
            m ((x : Move l a) → Counterpart l m (rest (l.toFunB a x))
            (fun tr => Out ⟨x, tr⟩)))) := by
  simp only [toCounterpart]
  split <;> rename_i h' <;> first | rfl | cases h.symm.trans h'

/-- Conversion at a receiver node preserves its boundary action. -/
theorem toCounterpart_receiver [Monad m] (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    (h : owner l a = .receiver) {Out : PathAlong l (.liftBind a rest) → Type u}
    (p : PublicCoinCounterpart l m (.liftBind a rest) Out) :
    toCounterpart p =
      let p' : m (Move l a) × ((x : Move l a) → PublicCoinCounterpart l m
        (rest (l.toFunB a x)) (fun t => Out ⟨x, t⟩)) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      (show Counterpart l m (.liftBind a rest) Out from by
        simpa only [Counterpart, Strategy, PureEnd, StrategyOver, contexts, paired, Choice, h] using
          (do let x ← p'.1; pure ⟨x, toCounterpart (p'.2 x)⟩ :
            m ((x : Move l a) × Counterpart l m (rest (l.toFunB a x))
            (fun tr => Out ⟨x, tr⟩)))) := by
  simp only [toCounterpart]
  split <;> rename_i h' <;> first | rfl | cases h.symm.trans h'

end PublicCoinCounterpart
end Interaction.TwoParty.Lens
