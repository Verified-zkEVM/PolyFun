/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Composite
import Batteries.Tactic.Lint

/-!
# Comonoids in the composition-monoidal category

Following Spivak–Niu, *Polynomial Functors* (§7.1, Def 7.14), a **comonoid** in
the monoidal category `(Poly, ◃, y)` is a carrier `c : PFunctor` with a counit
`ε : c ⇆ y` and a comultiplication `δ : c ⇆ c ◃ c` satisfying counitality and
coassociativity. Comonoids in `Poly` are exactly small categories: `c.A` is the
objects, the directions are the outgoing morphisms, `ε` picks the identities, and
`δ` is composition.

Counitality and coassociativity are lens equations, phrased through the unitor and
associator equivalences `compX` / `XComp` / `compAssoc` (`PFunctor.Lens.Equiv`).
A comonoid is *data*, not a predicate: one carrier can admit many comonoid
structures (Spivak–Niu Ex 7.39), so the laws are fields, not a `Prop`-class.

The primary instance is the **state comonoid** `stateComonoid S` on the
self-monomial `S y^S` (Spivak–Niu Ex 6.44 / 7.19): the contractible groupoid on
the state set `S`, whose comultiplication is the transition lens `Lens.fixState`
(`δ = (id, tgt, run)`) and whose counit is the stay-put self-loop. `comultN`
packages the canonical `n`-fold comultiplication `δ^{(n)} : c ⇆ c^{◃n}`
(Spivak–Niu Prop 7.20) — the comonoid data underneath the `n`-step run `Run_n`
(`PFunctor.DynSystem.nStep`).

The layer is kept à-la-carte (explicit lens laws) rather than routed through a
`MonoidalCategory (Poly, ◃, y)` instance, matching the rest of PolyFun's
monoidal machinery.
-/

@[expose] public section

universe u

namespace PFunctor

/-! ## The comonoid structure -/

/-- A **comonoid** in the composition-monoidal category `(Poly, ◃, y)`
(Spivak–Niu Def 7.14): a carrier `c`, a counit `ε : c ⇆ y`, and a
comultiplication `δ : c ⇆ c ◃ c` satisfying left/right counitality and
coassociativity as lens equations (through the unitors `XComp` / `compX` and the
associator `compAssoc`). This is the polynomial encoding of a small category. -/
structure Comonoid where
  /-- The carrier polynomial (the "objects and morphisms"). -/
  carrier : PFunctor.{u, u}
  /-- The counit `ε : c ⇆ y` — selects the identity morphisms. -/
  counit : Lens carrier X.{u, u}
  /-- The comultiplication `δ : c ⇆ c ◃ c` — the composition operation. -/
  comult : Lens carrier (carrier ◃ carrier)
  /-- Left counitality: `λ ∘ (ε ◃ id) ∘ δ = id`. -/
  counit_left : Lens.Equiv.XComp.toLens ∘ₗ (counit ◃ₗ Lens.id carrier) ∘ₗ comult
      = Lens.id carrier
  /-- Right counitality: `ρ ∘ (id ◃ ε) ∘ δ = id`. -/
  counit_right : Lens.Equiv.compX.toLens ∘ₗ (Lens.id carrier ◃ₗ counit) ∘ₗ comult
      = Lens.id carrier
  /-- Coassociativity: `α ∘ (δ ◃ id) ∘ δ = (id ◃ δ) ∘ δ`. -/
  coassoc : Lens.Equiv.compAssoc.toLens ∘ₗ (comult ◃ₗ Lens.id carrier) ∘ₗ comult
      = (Lens.id carrier ◃ₗ comult) ∘ₗ comult

namespace Comonoid

/-! ## The `n`-fold comultiplication `δ^{(n)}` -/

/-- The canonical `n`-fold comultiplication `δ^{(n)} : c ⇆ c^{◃n}` of a comonoid
(Spivak–Niu Prop 7.20), recursively `δ^{(0)} = ε` and
`δ^{(n+1)} = (id ◃ δ^{(n)}) ∘ δ`. The comonoid data underneath the `n`-step run
`PFunctor.DynSystem.nStep`. -/
def comultN (C : Comonoid.{u}) : (n : ℕ) → Lens C.carrier (compNth C.carrier n)
  | 0 => C.counit
  | n + 1 => (Lens.id C.carrier ◃ₗ C.comultN n) ∘ₗ C.comult

@[simp] theorem comultN_zero (C : Comonoid.{u}) : C.comultN 0 = C.counit := rfl

@[simp] theorem comultN_succ (C : Comonoid.{u}) (n : ℕ) :
    C.comultN (n + 1) = (Lens.id C.carrier ◃ₗ C.comultN n) ∘ₗ C.comult := rfl

/-! ## State systems (Spivak–Niu Ex 7.22) -/

/-- A comonoid **is a state system** when, at every object, its codomain map
`d ↦ cod d` (the second component of `δ`'s position action) is a bijection: from
each object there is exactly one morphism to each object (a contractible
groupoid). A predicate, never a field (Spivak–Niu Ex 7.22). -/
def IsStateSystem (C : Comonoid.{u}) : Prop :=
  ∀ a : C.carrier.A, Function.Bijective (C.comult.toFunA a).2

end Comonoid

/-! ## The state comonoid `S y^S` -/

/-- The **state comonoid** on `S y^S` (Spivak–Niu Ex 6.44 / 7.19): the
contractible groupoid on the state set `S`. Its comultiplication is the
transition lens `Lens.fixState` and its counit is the stay-put self-loop
`s ↦ (⋆ ↦ s)`. This discharges the state-comonoid laws referenced by
`PFunctor.Lens.transitionLens`. -/
def stateComonoid (S : Type u) : Comonoid.{u} where
  carrier := selfMonomial S
  counit := (fun _ => PUnit.unit) ⇆ (fun s _ => s)
  comult := Lens.fixState
  counit_left := rfl
  counit_right := rfl
  coassoc := rfl

@[simp] theorem stateComonoid_carrier (S : Type u) :
    (stateComonoid S).carrier = selfMonomial S := rfl

@[simp] theorem stateComonoid_comult (S : Type u) :
    (stateComonoid S).comult = Lens.fixState := rfl

/-- The state comonoid is a state system: its codomain map `s₁ ↦ s₁` is the
identity, hence bijective (Spivak–Niu Ex 7.22). -/
theorem isStateSystem_stateComonoid (S : Type u) :
    (stateComonoid S).IsStateSystem :=
  fun _ => Function.bijective_id

end PFunctor
