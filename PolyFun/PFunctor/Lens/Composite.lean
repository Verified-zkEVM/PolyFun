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

These are not a second representation: they are the components already stored by
the lens. The accessors `Lens.compOuter`, `Lens.compInner`, and
`Lens.compPullback` expose the three views directly, without conversion or an
auxiliary wrapper type.

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

/-! ## Components of a lens into `q ◃ r` -/

/-- The outer `q`-position selected by a lens into `q ◃ r` at each source
position (Spivak–Niu Example 6.40). -/
def compOuter (l : Lens p (q ◃ r)) (i : p.A) : q.A :=
  (l.toFunA i).1

/-- The inner `r`-position selected by a lens into `q ◃ r` after receiving
an outer `q`-direction. -/
def compInner (l : Lens p (q ◃ r)) (i : p.A) (u : q.B (l.compOuter i)) : r.A :=
  (l.toFunA i).2 u

/-- The joint pullback of the outer and inner directions of a lens into
`q ◃ r`. -/
def compPullback (l : Lens p (q ◃ r)) (i : p.A) :
    (Σ u : q.B (l.compOuter i), r.B (l.compInner i u)) → p.B i :=
  l.toFunB i

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

/-- Composition powers preserve lens composition: taking `n` copies of a
composite is the composite of the two `n`-fold maps. -/
@[simp] theorem compNthMap_comp (l₁ : Lens q r) (l₂ : Lens p q) (n : ℕ) :
    compNthMap (l₁ ∘ₗ l₂) n = compNthMap l₁ n ∘ₗ compNthMap l₂ n := by
  induction n with
  | zero => simp [compNthMap]
  | succ n ih =>
      rw [compNthMap_succ, compNthMap_succ, compNthMap_succ, ih]
      exact compMap_comp l₂ (compNthMap l₂ n) l₁ (compNthMap l₁ n)

end Lens

end PFunctor
