/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.TwoParty.Strategy

/-!
# Ordinary-import reduction of two-party nodes

Deterministic counterpart lifting and path observations use the public node equations.
The tests retain the dependent output family and use explicit rewriting where the simplifier's
normal form differs from the constructor spelling.
-/

public section

open Interaction Interaction.TwoParty

variable {m : Type → Type} [Monad m] [LawfulMonad m] {X : Type}

example (x : X) :
    Sigma.fst <$> run (TypeTree.node X fun _ => .done)
      ⟨.receiver, fun _ => PUnit.unit⟩
      (OutputP := fun _ => PUnit) (OutputC := fun _ => PUnit)
      (fun _ => pure PUnit.unit)
      (StrategyOver.TwoParty.Counterpart.liftId (m := m) ⟨x, PUnit.unit⟩) =
        pure ⟨x, PUnit.unit⟩ := by
  rw [StrategyOver.TwoParty.Counterpart.liftId_receiver,
    StrategyOver.TwoParty.Counterpart.liftId_done]
  have h := run_receiver (m := m) (rest := fun (_ : X) => .done)
    (rRest := fun _ => PUnit.unit) (OutputP := fun _ => PUnit) (OutputC := fun _ => PUnit)
    (fun _ => pure PUnit.unit) (pure ⟨x, PUnit.unit⟩)
  exact (congrArg (fun t => Sigma.fst <$> t) h).trans (by
    simp only [pure_bind, run_done, map_pure]
    rfl)

example (sample : m X) :
    Sigma.fst <$> run (TypeTree.node X fun _ => .done)
      ⟨.sender, fun _ => PUnit.unit⟩
      (OutputP := fun _ => PUnit) (OutputC := fun _ => PUnit)
      ((fun x => ⟨x, PUnit.unit⟩) <$> sample)
      (StrategyOver.TwoParty.Counterpart.liftId (m := m) (fun _ => PUnit.unit)) =
        (fun x => ⟨x, PUnit.unit⟩) <$> sample := by
  simp only [StrategyOver.TwoParty.Counterpart.liftId_sender,
    StrategyOver.TwoParty.Counterpart.liftId_done]
  have h := run_sender (m := m) (rest := fun (_ : X) => .done)
    (rRest := fun _ => PUnit.unit) (OutputP := fun _ => PUnit) (OutputC := fun _ => PUnit)
    ((fun x => ⟨x, PUnit.unit⟩) <$> sample) (fun _ => pure PUnit.unit)
  exact (congrArg (fun t => Sigma.fst <$> t) h).trans (by
    simp only [run_done, map_eq_pure_bind, bind_assoc, pure_bind]
    rfl)

example {A : TypeTree.Path (TypeTree.node X fun _ => .done) → Type} (x : X)
    (out : A ⟨x, PUnit.unit⟩) :
    StrategyOver.TwoParty.Counterpart.liftId (m := m) (spec := TypeTree.node X fun _ => .done)
      (roles := ⟨.receiver, fun _ => PUnit.unit⟩)
      (Output := A) ⟨x, out⟩ = pure ⟨x, out⟩ := by
  rw [StrategyOver.TwoParty.Counterpart.liftId_receiver,
    StrategyOver.TwoParty.Counterpart.liftId_done]

end
