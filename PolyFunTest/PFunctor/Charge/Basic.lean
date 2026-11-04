/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.Sub.Prod

/-!
# Charge bounds on concrete programs

Checks for `PolyFun.PFunctor.Free.Cost` and for the lens transport of roll bounds:

* `simp` decides a budget on a concrete `do` program;
* a call with no answers is still charged;
* a per-kind vector budget pushes forward to a weighted budget;
* a pair budget is the subtractive roll bound on what remains;
* simulating through a handler that doubles every call doubles a unit budget;
* a non-additive roll bound transports along a lens into a sum.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.Charge

/-! ## Concrete budgets -/

/-- Two kinds of call, each with three answers. -/
abbrev Pq : PFunctor := ⟨Bool, fun _ => Fin 3⟩

def chgN : Pq.A → ℕ := fun a => cond a 2 1

def prog : FreeM Pq Nat := do
  let x ← FreeM.lift (P := Pq) true
  let y ← FreeM.lift (P := Pq) false
  if x.val = 0 then
    let _ ← FreeM.lift (P := Pq) true
    pure y.val
  else pure (x.val + y.val)

example : IsChargeBound prog chgN 5 := by
  simp [prog, chgN]

example : ¬ IsChargeBound prog chgN 4 := by
  simp [prog, chgN]

/-- One call that can never be answered. -/
abbrev Dead : PFunctor := ⟨Unit, fun _ => PEmpty⟩

def stuck : FreeM Dead PEmpty := FreeM.lift ()

/-- The call is charged although no run completes. -/
example : ¬ stuck.IsChargeBound (fun _ => (1 : ℕ)) 0 := by
  simp [stuck]

/-! ## Changing the cost type -/

/-- Two kinds of query. -/
inductive Op
  | hash
  | group
  deriving DecidableEq

/-- Count each kind of query separately. -/
def kind (o : Op) : Op → ℕ := Pi.single o 1

/-- Weigh a hash query 3 and a group operation 5. -/
def weigh : (Op → ℕ) →+o ℕ where
  toFun v := 3 * v Op.hash + 5 * v Op.group
  map_zero' := by simp
  map_add' v w := by simp only [Pi.add_apply]; omega
  monotone' v w h := by
    have h₁ : v Op.hash ≤ w Op.hash := h Op.hash
    have h₂ : v Op.group ≤ w Op.group := h Op.group
    dsimp only
    omega

/-- A per-kind budget of `q` hash queries and one group operation pushes forward to the weighted
budget `3 q + 5`. -/
example {P : PFunctor} (c : P.A → Op) (x : FreeM P PUnit) (q : ℕ)
    (h : x.IsChargeBound (kind ∘ c) (q • kind Op.hash + kind Op.group)) :
    x.IsChargeBound (weigh ∘ kind ∘ c) (3 * q + 5) := by
  have := h.map weigh
  simp only [map_zero, map_add, map_nsmul] at this
  convert this using 1
  simp [weigh, kind, mul_comm]

/-- Keys with two answers. -/
abbrev Keys : PFunctor.{0, 0} := ⟨ℕ, fun _ => Bool⟩

def twoKeys : FreeM Keys Bool := do
  let _ ← FreeM.lift (P := Keys) 1
  FreeM.lift (P := Keys) 2

/-- A pair budget is the subtractive roll bound on the remaining pair. -/
example : twoKeys.IsChargeBound (fun k => if k = 1 then ((1 : ℕ), (0 : ℕ)) else (0, 1)) (1, 1) ↔
    IsRollBound twoKeys ((1, 1) - 0) (fun a b => (if a = 1 then ((1 : ℕ), (0 : ℕ)) else (0, 1)) ≤ b)
      (fun a b => b - if a = 1 then ((1 : ℕ), (0 : ℕ)) else (0, 1)) := by
  rw [isChargeBound_iff_isRollBound_orderedSub]
  simp

/-! ## Free handlers -/

/-- A single interface with two answers. -/
abbrev Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- Implement each call by two calls, returning the second answer. -/
def doubled : (a : Coin.A) → FreeM Coin (Coin.B a) := fun _ => do
  let _ ← FreeM.lift (P := Coin) ()
  FreeM.lift (P := Coin) ()

/-- Doubling a natural-number budget. -/
def double : ℕ →+o ℕ where
  toFun n := 2 * n
  map_zero' := rfl
  map_add' a b := by omega
  monotone' a b h := by dsimp only; omega

example {α : Type} (x : FreeM Coin α) (n : ℕ) (hx : x.IsChargeBound (fun _ => 1) n) :
    (x.liftM doubled).IsChargeBound (fun _ => 1) (2 * n) := by
  have h2 : x.IsChargeBound (fun _ => 2) (2 * n) := hx.map double
  exact h2.liftM doubled fun _ => by simp [doubled]

/-! ## Roll bounds along lenses -/

/-- Two operations with a single answer each. -/
abbrev Two : PFunctor.{0, 0} := ⟨Bool, fun _ => PUnit⟩

/-- A protocol that is not a charge: once `false` has been called, `true` may not be. The state
records whether `false` has been called. -/
def admits (a : Two.A) (seen : Bool) : Prop := ¬ (seen = true ∧ a = true)

def record (a : Two.A) (seen : Bool) : Bool := seen || !a

def upThenDown : FreeM Two Bool := do
  let _ ← FreeM.lift (P := Two) true
  let _ ← FreeM.lift (P := Two) false
  pure true

theorem upThenDown_isRollBound : upThenDown.IsRollBound false admits record := by
  simp only [upThenDown, isRollBound_lift_bind_iff']
  simp [admits, record]

/-- Relabelled into the left summand of a sum, the protocol constrains the left calls only. -/
example : (upThenDown.mapLens (Lens.inl (Q := Coin))).IsRollBound false
    (fun a s => Sum.elim (admits · s) (fun _ => True) a)
    (fun a s => Sum.elim (record · s) (fun _ => s) a) :=
  IsRollBound.mapLens Lens.inl upThenDown_isRollBound

end PolyFunTest.Charge
