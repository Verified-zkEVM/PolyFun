/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.PointedMachine
public import PolyFun.PFunctor.Dynamical.Speedup

/-!
# Examples for two-step systems and machine composition

Regression tests: `twoStep` preserves the state set, `seqComp` has `⊕`-state and
a faithful second phase, and a concrete halting machine unrolls as expected.
-/

@[expose] public section

universe u v w

namespace PFunctor

variable {p : PFunctor.{u, u}} {α β mid : Type u}

/-- The two-step system shares its state set with the original. -/
example (s : DynSystem p) : s.twoStep.State = s.State := rfl

/-- Sequential composition has state `M₁.State ⊕ M₂.State`. -/
example (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β) :
    (M₁.seqComp M₂).State = (M₁.State ⊕ M₂.State) := rfl

/-- The second phase of `seqComp` unrolls exactly like `M₂`. -/
example (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β) (s₂ : M₂.State) :
    (M₁.seqComp M₂).toComp 3 (Sum.inr s₂) = M₂.toComp 3 s₂ :=
  PointedMachine.toComp_seqComp_inr M₁ M₂ 3 s₂

/-- The first phase exposes `M₁` and hands off to `M₂` exactly on `M₁`'s output. -/
example (M₁ : PointedMachine p α mid) (M₂ : PointedMachine p mid β) (s₁ : M₁.State) :
    (M₁.seqComp M₂).toComp 1 (Sum.inl s₁)
      = FreeM.roll (M₁.expose s₁) (fun d =>
          (M₁.seqComp M₂).toComp 0 (match M₁.output (M₁.update s₁ d) with
            | some m => Sum.inr (M₂.init m)
            | none => Sum.inl (M₁.update s₁ d))) :=
  PointedMachine.toComp_seqComp_inl M₁ M₂ 0 s₁

/-- A machine that halts immediately with output `b`. -/
def haltMachine (b : β) : PointedMachine X.{u, u} α β where
  State := PUnit
  expose := fun _ => PUnit.unit
  update := fun _ _ => PUnit.unit
  init := fun _ => PUnit.unit
  output := fun _ => some b

/-- Machine states, inputs, and outputs may inhabit independent universes. -/
def universeSeparatedMachine {α : Type v} {β : Type w} (b : β) :
    PointedMachine X.{0, 0} α β where
  State := Bool
  expose := fun _ => PUnit.unit
  update := fun state _ => state
  init := fun _ => false
  output := fun _ => some b

/-- With fuel it reads off its value immediately; with none it is `none`. -/
example (b : β) : (haltMachine (α := α) b).toComp 1 PUnit.unit = FreeM.pure (some b) := rfl

example (b : β) : (haltMachine (α := α) b).toComp 0 PUnit.unit = FreeM.pure none := rfl

end PFunctor
