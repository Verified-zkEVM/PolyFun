/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Basic
public import PolyFun.PFunctor.Comonoid

/-!
# Two-step and `n`-step dynamical systems (`Run_n`)

Niu–Spivak §6.2.2 / §7.1.5 assemble the multi-step behaviours of a
`p`-dynamical system into composite systems over the composition powers of `p`.

The **two-step system** `Lens.speedup φ = (φ ◃ φ) ∘ₗ δ : DynSystem S (p ◃ p)`
(Example 6.44) runs `φ` twice through one composite `p ◃ p`-step via the
transition lens `δ = Lens.fixState`.

The **`n`-step system** `Run_n(φ) = φ^{◁n} ∘ₗ δ^{(n)} : Sy^S ⇆ p^{◃n}` (§7.1.5)
generalises this to all `n`, where `δ^{(n)}` is the `n`-fold comultiplication of
the state comonoid on `S y^S` (`PFunctor.Comonoid.comulN` on `stateComonoid S`)
and `φ^{◁n}` is the composition power of the interface lens (`Lens.compNthMap`).
`DynSystem.nStep` is that construction on bundled systems: one composite
`p^{◃n}`-step exposes `n` successive `p`-positions and threads the answers through
`n` updates. `nStep_two_eq_speedup` records that the `n = 2` case collapses to
`Lens.speedup`. This is the generic core of a finite-run truncation ladder, which a
probabilistic run semantics can instantiate.
-/

@[expose] public section

universe u uA uB

namespace PFunctor

namespace DynSystem

@[deprecated (since := "2026-10-19")] alias twoStep := Lens.speedup

/-! ## The `n`-step system `Run_n` (§7.1.5) -/

section
variable {S : Type u} {p : PFunctor.{u, u}}

/-- The **`n`-step system** `Run_n(φ) = φ^{◁n} ∘ₗ δ^{(n)} : DynSystem (p^{◃n})`
(Niu–Spivak §7.1.5): a single composite step exposes `n` successive `p`-positions,
consuming a direction after each, and updates the state. Same state set as `φ`. -/
def nStep (φ : DynSystem S p) (n : ℕ) : DynSystem S (compNth p n) :=
  φ.compNthMap n ∘ₗ (stateComonoid S).comulN n

theorem nStep_eq (φ : DynSystem S p) (n : ℕ) :
    φ.nStep n = φ.compNthMap n ∘ₗ (stateComonoid S).comulN n := rfl

/-- A zero-step system exposes the composition unit and leaves its state
unchanged. -/
@[simp] theorem nStep_zero_expose (φ : DynSystem S p) (state : S) :
    (φ.nStep 0).expose state = PUnit.unit := rfl

@[simp] theorem nStep_zero_update (φ : DynSystem S p) (state : S)
    (direction : (compNth p 0).B ((φ.nStep 0).expose state)) :
    (φ.nStep 0).update state direction = state := rfl

/-- A one-step system exposes the original position followed by the unique
position of the composition unit. -/
@[simp] theorem nStep_one_expose (φ : DynSystem S p) (state : S) :
    (φ.nStep 1).expose state = ⟨φ.expose state, fun _ => PUnit.unit⟩ := rfl

/-- A one-step composite direction performs exactly one original update. -/
@[simp] theorem nStep_one_update (φ : DynSystem S p) (state : S)
    (direction : (compNth p 1).B ((φ.nStep 1).expose state)) :
    (φ.nStep 1).update state direction = φ.update state direction.1 := rfl

/-- Coherence with the two-step system: the `n = 2` step over the right-nested power
`compNth p 2 = p ◃ (p ◃ y)` collapses to the binary composite `p ◃ p` of
`Lens.speedup` after the inner unitor `compY` (`p ◃ y ≅ p`). -/
theorem nStep_two_eq_speedup (φ : DynSystem S p) :
    (Lens.id p ◃ₗ Lens.Equiv.compY.toLens) ∘ₗ φ.nStep 2 = Lens.speedup φ := rfl

@[deprecated (since := "2026-10-19")] alias nStep_two_eq_twoStep := nStep_two_eq_speedup

end

end DynSystem

end PFunctor
