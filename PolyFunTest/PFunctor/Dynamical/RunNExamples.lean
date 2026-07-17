/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.RunN

/-!
# Examples for `n`-step systems

Regression tests: `nStep` preserves the state set, handles the zero- and
one-step boundaries, and collapses to `twoStep` at `n = 2`.
-/

@[expose] public section

universe u

namespace PFunctor

variable {S : Type u} {p : PFunctor.{u, u}}

/-- `nStep` preserves the state set, visible in its type: an `n`-step system on
states `S` is again a system on states `S`. -/
example (φ : DynSystem S p) (n : ℕ) : DynSystem S (compNth p n) := φ.nStep n

/-- `Run_2` collapses to `twoStep` after the inner unitor. -/
example (φ : DynSystem S p) :
    φ.nStep 2 ⨟ (Lens.id p ◃ₗ Lens.Equiv.compX.toLens) = φ.twoStep :=
  DynSystem.nStep_two_eq_twoStep φ

/-- `Run_0` performs no transition. -/
example (φ : DynSystem S p) (state : S)
    (direction : (compNth p 0).B ((φ.nStep 0).expose state)) :
    (φ.nStep 0).expose state = PUnit.unit ∧
      (φ.nStep 0).update state direction = state :=
  ⟨DynSystem.nStep_zero_expose φ state,
    DynSystem.nStep_zero_update φ state direction⟩

/-- `Run_1` exposes and executes exactly one transition of the original
system. -/
example (φ : DynSystem S p) (state : S)
    (direction : (compNth p 1).B ((φ.nStep 1).expose state)) :
    (φ.nStep 1).expose state = ⟨φ.expose state, fun _ => PUnit.unit⟩ ∧
      (φ.nStep 1).update state direction = φ.update state direction.1 :=
  ⟨DynSystem.nStep_one_expose φ state,
    DynSystem.nStep_one_update φ state direction⟩

end PFunctor
