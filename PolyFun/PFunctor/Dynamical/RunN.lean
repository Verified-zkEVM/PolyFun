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

Spivak–Niu §6.2.2 / §7.1.5 assemble the multi-step behaviours of a
`p`-dynamical system into composite systems over the composition powers of `p`.

The **two-step system** `DynSystem.twoStep φ = δ ⨟ (φ ◃ φ) : DynSystem S (p ◃ p)`
(Example 6.44) runs `φ` twice through one composite `p ◃ p`-step via the
transition lens `δ = Lens.fixState`; it is `Lens.speedup` on the interface lens.

The **`n`-step system** `Run_n(φ) = δ^{(n)} ⨟ φ^{◁n} : Sy^S ⇆ p^{◃n}` (§7.1.5)
generalises this to all `n`, where `δ^{(n)}` is the `n`-fold comultiplication of
the state comonoid on `S y^S` (`PFunctor.Comonoid.comultN` on `stateComonoid S`)
and `φ^{◁n}` is the composition power of the interface lens (`Lens.compNthMap`).
`DynSystem.nStep` is that construction on bundled systems: one composite
`p^{◃n}`-step exposes `n` successive `p`-positions and threads the answers through
`n` updates. `twoStep_toLens_eq` records that the `n = 2` case collapses to
`twoStep`. This is the generic core of the finite-run truncation ladder that a
probabilistic run semantics (VCVio's `RunLimit`) instantiates.
-/

@[expose] public section

universe u uA uB

namespace PFunctor

namespace DynSystem

/-! ## The two-step system (Example 6.44) -/

section
variable {S : Type u} {p : PFunctor.{uA, uB}}

/-- The two-step system `δ ⨟ (φ ◃ φ) : DynSystem S (p ◃ p)` of a `p`-dynamical
system (Spivak–Niu Example 6.44): one composite step exposes a first `p`-position,
consumes a direction, exposes a second `p`-position, and updates. Same state set
as `φ` — literally `Lens.speedup` on the system's interface lens, and the `n = 2`
case of `nStep` over the binary composite `p ◃ p` (see `twoStep_toLens_eq`). -/
def twoStep (s : DynSystem S p) : DynSystem S (p ◃ p) :=
  Lens.speedup s

@[simp] theorem twoStep_eq_speedup (s : DynSystem S p) :
    s.twoStep = Lens.speedup s := rfl

end

/-! ## The `n`-step system `Run_n` (§7.1.5) -/

section
variable {S : Type u} {p : PFunctor.{u, u}}

/-- The **`n`-step system** `Run_n(φ) = δ^{(n)} ⨟ φ^{◁n} : DynSystem (p^{◃n})`
(Spivak–Niu §7.1.5): a single composite step exposes `n` successive `p`-positions,
consuming a direction after each, and updates the state. Same state set as `φ`. -/
def nStep (φ : DynSystem S p) (n : ℕ) : DynSystem S (compNth p n) :=
  φ.compNthMap n ∘ₗ (stateComonoid S).comultN n

@[simp] theorem nStep_eq (φ : DynSystem S p) (n : ℕ) :
    φ.nStep n = φ.compNthMap n ∘ₗ (stateComonoid S).comultN n := rfl

/-- Coherence with `twoStep`: the `n = 2` step over the right-nested power
`compNth p 2 = p ◃ (p ◃ y)` collapses to `twoStep`'s binary composite `p ◃ p`
after the inner unitor `compX` (`p ◃ y ≅ p`). -/
theorem twoStep_toLens_eq (φ : DynSystem S p) :
    (Lens.id p ◃ₗ Lens.Equiv.compX.toLens) ∘ₗ φ.nStep 2 = φ.twoStep := by
  rfl

end

end DynSystem

end PFunctor
