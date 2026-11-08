/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.TwoParty.Lens.Compose
public import PolyFun.PFunctor.Free.Replicate

/-!
# Iterated lens interactions

Each round uses the same source tree. The participants thread their own state through
terminal outputs; runtime challenge history can be stored in that state without affecting shape.
-/

public section

universe u uA uB
namespace Interaction.TwoParty.Lens
open PFunctor
open FreeM (PathAlong)

variable {P : PFunctor.{uA, uB}} {l : PFunctor.Lens P rolePoly.{u}}
variable {m : Type u → Type u} [Monad m]
variable (s : FreeM P PUnit.{u + 1})

/-- Iterate a focal round, threading its terminal state into the next round. -/
@[expose] def Focal.iterate {State : Type u}
    (round : State → Focal l m s (fun _ => State)) :
    (n : Nat) → State → Focal l m (FreeM.replicate PUnit.unit s n) (fun _ => State)
  | 0, state => pure state
  | n + 1, state => Focal.compFlat (round state)
    (fun _ next => pure (Focal.iterate round n next))

/-- Iterate a counterpart round whose terminal state is pure. -/
@[expose] def Counterpart.iterate {State : Type u}
    (round : State → PureEnd l m .counterpart s (fun _ => State)) :
    (n : Nat) → State → Counterpart l m (FreeM.replicate PUnit.unit s n) (fun _ => State)
  | 0, state => pure state
  | n + 1, state => Counterpart.appendFlat (round state)
    (fun _ next => Counterpart.iterate round n next)

/-- Zero rounds return the initial states and the empty transcript. -/
theorem run_iterate_zero [LawfulMonad m] {SP SC : Type u}
    (p : SP → Focal l m s (fun _ => SP))
    (c : SC → PureEnd l m .counterpart s (fun _ => SC)) (sp : SP) (sc : SC) :
    run (FreeM.replicate PUnit.unit s 0) (Focal.iterate s p 0 sp)
      (Counterpart.iterate s c 0 sc) = pure ⟨PUnit.unit, sp, sc⟩ := by
  simp only [Focal.iterate, Counterpart.iterate, FreeM.replicate_zero,
    FreeM.pure_eq_pure, run_done, pure_bind]

/-- One more iteration executes the first round before the remaining rounds. -/
theorem run_iterate_succ [LawfulMonad m] {SP SC : Type u}
    (p : SP → Focal l m s (fun _ => SP))
    (c : SC → PureEnd l m .counterpart s (fun _ => SC))
    (n : Nat) (sp : SP) (sc : SC) :
    run (FreeM.replicate PUnit.unit s (n + 1)) (Focal.iterate s p (n + 1) sp)
      (Counterpart.iterate s c (n + 1) sc) = (do
      let ⟨tr, sp', sc'⟩ ← run s (p sp) (c sc).toStrategy
      let ⟨tail, op, oc⟩ ← run (FreeM.replicate PUnit.unit s n)
        (Focal.iterate s p n sp') (Counterpart.iterate s c n sc')
      pure ⟨PathAlong.replicateCons l PUnit.unit s n tr tail, op, oc⟩) := by
  simpa only [Focal.iterate, Counterpart.iterate, FreeM.replicate_succ, pure_bind,
    PathAlong.replicateCons] using
    (run_compFlat_appendFlat (s₂ := fun _ => FreeM.replicate PUnit.unit s n)
      (OutP := fun _ => SP) (OutC := fun _ => SC) (p sp)
      (fun _ next => pure (Focal.iterate s p n next))
      (c sc) (fun _ next => Counterpart.iterate s c n next))

end Interaction.TwoParty.Lens
