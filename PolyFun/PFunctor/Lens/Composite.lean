/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic
import Batteries.Tactic.Lint

/-!
# Lenses into composites, and the composition-power of a lens

Two pieces of Spivak–Niu Ch. 6 machinery for the composition product `◃`.

## Destructor triple (Example 6.40)

A lens `φ : p ⇆ q ◃ r` is exactly a triple `(φ^q, φ^r, φ♯)`:

* `φ^q : (i : p.A) → q.A` — the `q`-position policy;
* `φ^r : (i : p.A) → q.B (φ^q i) → r.A` — the `r`-position policy, given a
  `q`-direction; and
* `φ♯ : (i : p.A) → (Σ u : q.B (φ^q i), r.B (φ^r i u)) → p.B i` — the joint pullback
  of directions.

`toCompTriple` packages this as an `Equiv`, so protocol lenses into a two-phase
interface can be built and destructed without unfolding `PFunctor.comp`. This is
the intro/elim rule VCVio's two-phase games (`TwoPhaseGame`) want.

## Composition power of a lens (§6.1.4)

`Lens.compNthMap l n : Lens (compNth p n) (compNth q n)` lifts a lens `l : p ⇆ q`
through the `n`-fold composition power `p^{◃n}` (Spivak–Niu's `φ^{◁n}`, the
"`n` steps of the interface" map). It is the interface-lift underneath multi-step
dynamical systems.
-/

@[expose] public section

universe uA uB

namespace PFunctor

namespace Lens

variable {p q r : PFunctor.{uA, uB}}

/-! ## Destructor triple for `Lens p (q ◃ r)` -/

/-- The triple `(φ^q, φ^r, φ♯)` equivalent to a lens `p ⇆ q ◃ r` (Spivak–Niu
Example 6.40): a `q`-position policy, an `r`-position policy depending on a
`q`-direction, and a joint pullback of directions. -/
def CompTriple (p q r : PFunctor.{uA, uB}) : Type (max uA uB) :=
  Σ φq : (i : p.A) → q.A,
  Σ _φr : (i : p.A) → q.B (φq i) → r.A,
    (i : p.A) → (Σ u : q.B (φq i), r.B (_φr i u)) → p.B i

/-- A lens into a composite `q ◃ r` is equivalently its destructor triple
`(φ^q, φ^r, φ♯)` (Spivak–Niu Example 6.40). Both round-trips are `rfl`. -/
def toCompTriple : Lens p (q ◃ r) ≃ CompTriple p q r where
  toFun φ := ⟨fun i => (φ.toFunA i).1, fun i => (φ.toFunA i).2, fun i => φ.toFunB i⟩
  invFun t := (fun i => ⟨t.1 i, t.2.1 i⟩) ⇆ (fun i => t.2.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Build a lens into `q ◃ r` from its destructor triple. -/
abbrev ofCompTriple (t : CompTriple p q r) : Lens p (q ◃ r) := toCompTriple.symm t

/-! ## The composition power of a lens -/

/-- The `n`-fold composition power of a lens: `l^{◃n} : compNth p n ⇆ compNth q n`
(Spivak–Niu §6.1.4). Built by iterating `compMap` (`◃ₗ`). -/
def compNthMap (l : Lens p q) : (n : ℕ) → Lens (compNth p n) (compNth q n)
  | 0 => Lens.id X
  | n + 1 => l ◃ₗ compNthMap l n

@[simp] theorem compNthMap_zero (l : Lens p q) : compNthMap l 0 = Lens.id X := rfl

@[simp] theorem compNthMap_succ (l : Lens p q) (n : ℕ) :
    compNthMap l (n + 1) = l ◃ₗ compNthMap l n := rfl

@[simp] theorem compNthMap_id (P : PFunctor.{uA, uB}) (n : ℕ) :
    compNthMap (Lens.id P) n = Lens.id (compNth P n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [compNthMap, ih, compMap_id]

end Lens

end PFunctor
