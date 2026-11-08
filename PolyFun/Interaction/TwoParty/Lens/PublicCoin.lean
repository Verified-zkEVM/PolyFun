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

/-- Replayable counterpart nodes: observation slots or a sampler with pure continuations. -/
@[expose, implicit_reducible] def publicCoinSyntax (m : Type u → Type u) :
    SyntaxOver l PUnit.{u + 1} (fun _ => PUnit.{1}) where
  Node _ a _ Cont := match owner l a with
    | .sender => m ((x : Move l a) → Cont x)
    | .receiver => m (Move l a) × ((x : Move l a) → Cont x)

/-- A public-coin counterpart with effectful terminal output. -/
abbrev PublicCoinCounterpart (m : Type u → Type u) (s : FreeM P PUnit.{u + 1})
    (Out : PathAlong l s → Type u) :=
  StrategyOver (publicCoinSyntax l m) PUnit.unit s (contexts s) (fun tr => m (Out tr))

namespace PublicCoinCounterpart
variable {l} {m : Type u → Type u} [Monad m]

/-- Interpret the exposed sampler as the counterpart's challenge slot. -/
@[expose] def toCounterpart : {s : FreeM P PUnit.{u + 1}} →
    {Out : PathAlong l s → Type u} → PublicCoinCounterpart l m s Out → Counterpart l m s Out
  | .pure _, _, p => p
  | .liftBind a rest, Out, p =>
    match h : owner l a with
    | .sender => by
      have p' : m ((x : Move l a) → PublicCoinCounterpart l m
          (rest (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩)) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      simpa only [Counterpart, Strategy, PureEnd, StrategyOver, contexts, paired, Choice, h] using
        (do let f ← p'; pure (fun x => toCounterpart (f x)) :
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

/-- Replay observation and leaf slots, using recorded challenges without resampling. -/
@[expose] def replay : {s : FreeM P PUnit.{u + 1}} →
    {Out : PathAlong l s → Type u} → PublicCoinCounterpart l m s Out →
    (tr : PathAlong l s) → m (Out tr)
  | .pure _, _, p, _ => p
  | .liftBind a rest, Out, p, ⟨x, tr⟩ =>
    match h : owner l a with
    | .sender => do
      let f ← (show m ((x : Move l a) → PublicCoinCounterpart l m
          (rest (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩)) from by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p)
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
  | .pure _, _, _, f, p => f ⟨⟩ <$> p
  | .liftBind a rest, A, B, f, p =>
    match h : owner l a with
    | .sender => by
      have p' : m ((x : Move l a) → PublicCoinCounterpart l m
          (rest (l.toFunB a x)) (fun tr => A ⟨x, tr⟩)) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using
        ((fun next x => mapOutput (fun tr => f ⟨x, tr⟩) (next x)) <$> p' :
          m ((x : Move l a) → PublicCoinCounterpart l m (rest (l.toFunB a x))
            (fun tr => B ⟨x, tr⟩)))
    | .receiver => by
      have p' : m (Move l a) × ((x : Move l a) → PublicCoinCounterpart l m
          (rest (l.toFunB a x)) (fun tr => A ⟨x, tr⟩)) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using
        ((p'.1, fun x => mapOutput (fun tr => f ⟨x, tr⟩) (p'.2 x)) :
          m (Move l a) × ((x : Move l a) → PublicCoinCounterpart l m
            (rest (l.toFunB a x)) (fun tr => B ⟨x, tr⟩)))

/-- Replay executes the terminal action. -/
@[simp] theorem replay_done {Out : PathAlong l (.pure PUnit.unit) → Type u}
    (p : m (Out ⟨⟩)) : replay (l := l) (s := .pure PUnit.unit) p ⟨⟩ = p := rfl

/-- Conversion preserves the terminal action. -/
@[simp] theorem toCounterpart_done {Out : PathAlong l (.pure PUnit.unit) → Type u}
    (p : m (Out ⟨⟩)) : toCounterpart (l := l) (s := .pure PUnit.unit) p = p := rfl

/-- Replay at a sender node follows the recorded move. -/
theorem replay_sender (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    (h : owner l a = .sender) {Out : PathAlong l (.liftBind a rest) → Type u}
    (p : PublicCoinCounterpart l m (.liftBind a rest) Out)
    (x : Move l a) (tr : PathAlong l (rest (l.toFunB a x))) :
    replay p ⟨x, tr⟩ =
      let p' : m ((x : Move l a) → PublicCoinCounterpart l m
        (rest (l.toFunB a x)) (fun t => Out ⟨x, t⟩)) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      (do let f ← p'; replay (f x) tr) := by
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

/-- Conversion at a sender node preserves its boundary action. -/
theorem toCounterpart_sender (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
    (h : owner l a = .sender) {Out : PathAlong l (.liftBind a rest) → Type u}
    (p : PublicCoinCounterpart l m (.liftBind a rest) Out) :
    toCounterpart p =
      let p' : m ((x : Move l a) → PublicCoinCounterpart l m
        (rest (l.toFunB a x)) (fun t => Out ⟨x, t⟩)) := by
        simpa only [PublicCoinCounterpart, StrategyOver, contexts, publicCoinSyntax, h] using p
      (show Counterpart l m (.liftBind a rest) Out from by
        simpa only [Counterpart, Strategy, PureEnd, StrategyOver, contexts, paired, Choice, h] using
          (do let f ← p'; pure (fun x => toCounterpart (f x)) :
            m ((x : Move l a) → Counterpart l m (rest (l.toFunB a x))
            (fun tr => Out ⟨x, tr⟩)))) := by
  simp only [toCounterpart]
  split <;> rename_i h' <;> first | rfl | cases h.symm.trans h'

/-- Conversion at a receiver node preserves its boundary action. -/
theorem toCounterpart_receiver (a : P.A) (rest : P.B a → FreeM P PUnit.{u + 1})
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
