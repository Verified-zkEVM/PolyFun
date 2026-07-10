/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Basic

/-!
# The transition lens and two-step dynamical systems

Spivak–Niu Example 6.44 identifies the **transition lens**

`δ : Sy^S ⇆ Sy^S ◃ Sy^S`,  `δ = (id, tgt, run)`,

on the self-monomial state polynomial: it remembers the start state (`id` on
positions), relabels each direction as the state it targets (`tgt`), and composes
two hops into one (`run`). This lens is already present as `PFunctor.Lens.fixState`;
`transitionLens` is a named, cited alias.

Precomposing `δ` with `φ ◃ φ` turns a `p`-dynamical system into an honest
two-step system over the composite interface `p ◃ p` — `PFunctor.Lens.speedup`
at the lens level. `DynSystem.twoStep` is that construction lifted to bundled
systems.

The general `n`-step system needs the canonical `δ^{(n)}` recursion, which is
comonoid data (Spivak–Niu Ch. 7); it lands with the comonoid layer (roadmap B3),
built on `Lens.compNthMap` from `PFunctor.Lens.Composite`.
-/

@[expose] public section

universe u uA uB

namespace PFunctor

/-- The transition lens `δ : Sy^S ⇆ Sy^S ◃ Sy^S` of the state comonoid
(Spivak–Niu Example 6.44), `δ = (id, tgt, run)`. Definitionally `Lens.fixState`.
Its counit and coassociativity laws are the state-comonoid laws (roadmap B2). -/
abbrev Lens.transitionLens (S : Type u) :
    Lens (selfMonomial S) (selfMonomial S ◃ selfMonomial S) :=
  Lens.fixState

namespace DynSystem

variable {p : PFunctor.{uA, uB}}

/-- The two-step system `δ ⨟ (φ ◃ φ) : DynSystem (p ◃ p)` of a `p`-dynamical
system (Spivak–Niu Example 6.44): one composite step exposes a first `p`-position,
consumes a direction, exposes a second `p`-position, and updates. Same state set
as `φ`. -/
def twoStep (s : DynSystem p) : DynSystem (p ◃ p) :=
  ofLens (Lens.speedup s.toLens)

@[simp] theorem twoStep_toLens (s : DynSystem p) :
    s.twoStep.toLens = Lens.speedup s.toLens := rfl

@[simp] theorem twoStep_state (s : DynSystem p) : s.twoStep.State = s.State := rfl

end DynSystem

end PFunctor
