/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.Basic.StrategyOver
import all PolyFun.Interaction.TwoParty.Syntax
import all PolyFun.Interaction.TwoParty.Strategy
public import PolyFun.Interaction.TwoParty.Strategy

/-!
# Public equations for replayable public-coin counterparts

The constructor equations expose replay and ordinary execution through the
public interface, including dependent output families. Replay chooses an
already prescribed public challenge without resampling it.
-/

public section

universe u

namespace Interaction.TwoParty.PublicCoinCounterpart

open PFunctor.FreeM

variable {m : Type u → Type u} [Monad m]

/-- Replay at a terminal protocol node returns its output. -/
@[simp]
theorem replay_done {Output : Path TypeTree.done → Type u} (out : Output ⟨⟩) :
    replay (spec := .done) (roles := PUnit.unit) out ⟨⟩ = (pure out : m (Output ⟨⟩)) := rfl

/-- Replay observes the sender's recorded message before continuing. -/
theorem replay_sender {X : Type u} {rest : X → TypeTree}
    {roles : (x : X) → RoleDecoration (rest x)}
    {Output : Path (TypeTree.node X rest) → Type u}
    (observe : (x : X) → m (StrategyOver (counterpartSyntax m) PUnit.unit
      (rest x) (roles x) (fun tr => Output ⟨x, tr⟩)))
    (x : X) (tr : Path (rest x)) :
    replay (spec := TypeTree.node X rest) (roles := ⟨.sender, roles⟩) observe ⟨x, tr⟩ =
      (do let next ← observe x; replay next tr) := rfl

/-- Replay uses the continuation indexed by the recorded challenge. -/
theorem replay_receiver {X : Type u} {rest : X → TypeTree}
    {roles : (x : X) → RoleDecoration (rest x)}
    {Output : Path (TypeTree.node X rest) → Type u}
    (sample : m X)
    (next : (x : X) → StrategyOver (counterpartSyntax m) PUnit.unit
      (rest x) (roles x) (fun tr => Output ⟨x, tr⟩))
    (x : X) (tr : Path (rest x)) :
    replay (spec := TypeTree.node X rest) (roles := ⟨.receiver, roles⟩)
      (sample, next) ⟨x, tr⟩ = replay (next x) tr := rfl

/-- Forgetting the public-coin structure preserves terminal outputs. -/
@[simp]
theorem toCounterpart_done {Output : Path TypeTree.done → Type u} (out : Output ⟨⟩) :
    toCounterpart (spec := .done) (roles := PUnit.unit) (m := m) out = out := by
  simp [toCounterpart, StrategyOver.map]

/-- Sender observations are unchanged by forgetting the public-coin structure. -/
theorem toCounterpart_sender {X : Type u} {rest : X → TypeTree}
    {roles : (x : X) → RoleDecoration (rest x)}
    {Output : Path (TypeTree.node X rest) → Type u}
    (observe : (x : X) → m (StrategyOver (counterpartSyntax m) PUnit.unit
      (rest x) (roles x) (fun tr => Output ⟨x, tr⟩))) :
    toCounterpart (spec := TypeTree.node X rest) (roles := ⟨.sender, roles⟩) observe =
      (fun x => toCounterpart <$> observe x) := by
  simp [toCounterpart, StrategyOver.map, toCounterpartHom,
    StrategyOver.TwoParty.PublicCoinCounterpart.toCounterpartHom]
  rfl

/-- Ordinary execution samples a challenge and follows its indexed continuation. -/
theorem toCounterpart_receiver {X : Type u} {rest : X → TypeTree}
    {roles : (x : X) → RoleDecoration (rest x)}
    {Output : Path (TypeTree.node X rest) → Type u}
    (sample : m X)
    (next : (x : X) → StrategyOver (counterpartSyntax m) PUnit.unit
      (rest x) (roles x) (fun tr => Output ⟨x, tr⟩)) :
    toCounterpart (spec := TypeTree.node X rest) (roles := ⟨.receiver, roles⟩)
      (sample, next) = (do let x ← sample; pure ⟨x, toCounterpart (next x)⟩) := by
  simp [toCounterpart, StrategyOver.map, toCounterpartHom,
    StrategyOver.TwoParty.PublicCoinCounterpart.toCounterpartHom]
  rfl

end Interaction.TwoParty.PublicCoinCounterpart
