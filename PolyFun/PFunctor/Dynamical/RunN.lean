/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Speedup
public import PolyFun.PFunctor.Comonoid

/-!
# `n`-step dynamical systems `Run_n`

Spivak–Niu §7.1.5 assembles the length-`n` behaviours of a `p`-dynamical system
into the **`n`-step system**

`Run_n(φ) = φ^{◁n} ∘ₗ δ^{(n)} : Sy^S ⇆ p^{◃n}`,

where `δ^{(n)}` is the `n`-fold comultiplication of the state comonoid on `S y^S`
(`PFunctor.Comonoid.comultN` on `stateComonoid S`) and `φ^{◁n}` is the
composition power of the interface lens (`Lens.compNthMap`). `DynSystem.nStep`
is that construction on bundled systems: one composite `p^{◃n}`-step exposes `n`
successive `p`-positions and threads the answers through `n` updates.

This generalises `DynSystem.twoStep` (the `n = 2` case over the *binary*
composite `p ◃ p`) to all `n` over the right-nested power `compNth p n`. It is the
generic core of the finite-run truncation ladder that a probabilistic run
semantics (VCVio's `RunLimit`) instantiates.
-/

@[expose] public section

universe u

namespace PFunctor

namespace DynSystem

variable {p : PFunctor.{u, u}}

/-- The **`n`-step system** `Run_n(φ) = φ^{◁n} ∘ₗ δ^{(n)} : DynSystem (p^{◃n})`
(Spivak–Niu §7.1.5): a single composite step exposes `n` successive `p`-positions,
consuming a direction after each, and updates the state. Same state set as `φ`. -/
def nStep (φ : DynSystem p) (n : ℕ) : DynSystem (compNth p n) :=
  ofLens (φ.toLens.compNthMap n ∘ₗ (stateComonoid φ.State).comultN n)

@[simp] theorem nStep_state (φ : DynSystem p) (n : ℕ) :
    (φ.nStep n).State = φ.State := rfl

@[simp] theorem nStep_toLens (φ : DynSystem p) (n : ℕ) :
    (φ.nStep n).toLens = φ.toLens.compNthMap n ∘ₗ (stateComonoid φ.State).comultN n := rfl

/-- Coherence with `twoStep`: the `n = 2` step over the right-nested power
`compNth p 2 = p ◃ (p ◃ y)` collapses to `twoStep`'s binary composite `p ◃ p`
after the inner unitor `compX` (`p ◃ y ≅ p`). -/
theorem twoStep_toLens_eq (φ : DynSystem p) :
    (Lens.id p ◃ₗ Lens.Equiv.compX.toLens) ∘ₗ (φ.nStep 2).toLens = (φ.twoStep).toLens := by
  rfl

end DynSystem

end PFunctor
