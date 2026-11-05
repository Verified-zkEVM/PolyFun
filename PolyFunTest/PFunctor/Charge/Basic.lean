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
* a non-additive roll bound transports along a lens into a sum;
* contracts need care: a per-kind budget over infinitely many kinds does not bound total use, and
  with a negative price a refund call meets a budget the work alone would exceed;
* a bound restricted to allowed answers holds where the unrestricted one fails, matches the
  restricted roll bound and transfers through a handler, and a lens that answers only some
  directions can hide calls from a bound.
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

instance : Fintype Op := ⟨{.hash, .group}, fun o => by cases o <;> simp⟩

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

/-! ## Totals, constants and uniform steps -/

/-- Per-kind budgets sum to a total budget. -/
example {P : PFunctor} (c : P.A → Op) (x : FreeM P PUnit) (q : ℕ)
    (h : x.IsChargeBound (kind ∘ c) (q • kind Op.hash + kind Op.group)) :
    x.IsChargeBound (fun a => ∑ o, kind (c a) o) (∑ o, (q • kind Op.hash + kind Op.group) o)
      (∑ o, (0 : Op → ℕ) o) :=
  h.sum

/-- A natural-number budget is a budget in `ℕ∞`. -/
example {α : Type} (x : FreeM Coin α) (n : ℕ) (h : x.IsChargeBound (fun _ => (1 : ℕ)) n) :
    x.IsChargeBound (fun _ => ((1 : ℕ) : ℕ∞)) (n : ℕ∞) ((0 : ℕ) : ℕ∞) :=
  isChargeBound_natCast_iff.2 h

/-- Each call implemented by two calls: `n` calls become `n • 2`. -/
example {α : Type} (x : FreeM Coin α) (n : ℕ) (hx : x.IsChargeBound (fun _ => (1 : ℕ)) n) :
    (x.liftM doubled).IsChargeBound (fun _ => (1 : ℕ)) (n • 2) :=
  IsChargeBound.liftM_nsmul doubled (fun _ => by simp [doubled]) hx

/-- Two calls to distinct keys. -/
def keysOneTwo : FreeM Keys Bool := do
  let _ ← FreeM.lift (P := Keys) 1
  let _ ← FreeM.lift (P := Keys) 2
  pure true

/-- Per-index budgets with unit charges are the per-index subtractive roll bound. -/
example :
    keysOneTwo.IsChargeBound (fun a => Pi.single a 1) (fun k => if k = 1 ∨ k = 2 then 1 else 0) :=
  (isChargeBound_single_iff_isRollBound _ _).2 (by
    simp only [keysOneTwo, isRollBound_lift_bind_iff', isRollBound_pure]
    exact ⟨by decide, fun _ => ⟨by decide, fun _ => trivial⟩⟩)

/-! ## Bounds as contracts -/

/-- Infinitely many kinds of call, one answer each. -/
abbrev Kinds : PFunctor.{0, 0} := ⟨ℕ, fun _ => PUnit⟩

/-- One call to each of three kinds. -/
def spread : FreeM Kinds Bool := do
  let _ ← FreeM.lift (P := Kinds) 0
  let _ ← FreeM.lift (P := Kinds) 1
  let _ ← FreeM.lift (P := Kinds) 2
  pure true

/-- Each kind is called at most once: the per-kind budget `1` holds. -/
example : spread.IsChargeBound (fun k => Pi.single k 1) (fun _ => (1 : ℕ)) := by
  rw [isChargeBound_pi_iff]
  intro i
  simp only [spread, isChargeBound_lift_bind_iff', isChargeBound_pure_iff, Pi.single_apply,
    Pi.zero_apply]
  refine ⟨?_, fun _ => ⟨?_, fun _ => ⟨?_, fun _ => ?_⟩⟩⟩ <;> split_ifs <;> omega

/-- The total use is three, so the per-kind budget does not bound it. -/
example : ¬ spread.IsChargeBound (fun _ => (1 : ℕ)) 1 := by
  simp [spread]

/-- A call costing `5`, preceded by a refund of `5`. -/
def refundThenWork : FreeM Two Bool := do
  let _ ← FreeM.lift (P := Two) false
  let _ ← FreeM.lift (P := Two) true
  pure true

def refundPrice (b : Two.A) : ℤ := if b then 5 else -5

/-- With a negative price, the padded program meets the budget `0`, although its work costs `5`. -/
example : refundThenWork.IsChargeBound refundPrice 0 := by
  simp [refundThenWork, refundPrice]

/-- Under the reversed order, every program meets the budget `0`: `≤` no longer bounds use. -/
example (x : FreeM Coin Bool) (s : ℕᵒᵈ) :
    x.IsChargeBound (fun _ => OrderDual.toDual (1 : ℕ)) (OrderDual.toDual 0) s := by
  induction x using FreeM.rec generalizing s with
  | pure a => exact Nat.zero_le _
  | liftBind a r ih => exact ⟨Nat.zero_le _, fun b => ih b _⟩

/-- `ℕ` with `max` as its addition. -/
structure MaxNat where
  /-- The underlying natural number. -/
  val : ℕ

instance : Add MaxNat := ⟨fun a b => ⟨max a.val b.val⟩⟩
instance : LE MaxNat := ⟨fun a b => a.val ≤ b.val⟩
instance : Zero MaxNat := ⟨⟨0⟩⟩

/-- With `max` as addition, a budget bounds only the largest price: every program, however many
calls it makes, meets the budget `1` at price `1`. -/
example (x : FreeM Coin Bool) : x.IsChargeBound (fun _ => (⟨1⟩ : MaxNat)) ⟨1⟩ := by
  suffices h : ∀ s : MaxNat, s.val ≤ 1 → x.IsChargeBound (fun _ => (⟨1⟩ : MaxNat)) ⟨1⟩ s from
    h 0 (Nat.zero_le 1)
  induction x using FreeM.rec with
  | pure a => exact fun _ hs => hs
  | liftBind a r ih =>
    exact fun s hs => ⟨max_le hs le_rfl, fun b => ih b _ (max_le hs le_rfl)⟩

/-! ## Restricted answers -/

/-- Flip a coin; on `false`, make two more calls. -/
def flipThenMore : FreeM Coin Bool := do
  let b ← FreeM.lift (P := Coin) ()
  if b then pure true else do
    let _ ← FreeM.lift (P := Coin) ()
    let _ ← FreeM.lift (P := Coin) ()
    pure false

/-- When the handler can only answer `true`, as a sampler supported on `true`, the continuation at
`false` is never run, so one call fits the budget `1`. -/
example : flipThenMore.IsChargeBoundUnder (fun _ => (1 : ℕ)) (fun _ b => b = true) 1 := by
  simp [flipThenMore]

/-- Without the restriction the budget `1` does not hold. -/
example : ¬ flipThenMore.IsChargeBound (fun _ => (1 : ℕ)) 1 := by
  simp [flipThenMore]

/-- Every answer allowed: the restricted bound is the charge bound, and a charge bound holds under
any restriction. -/
example (x : FreeM Coin Bool) (n : ℕ) :
    x.IsChargeBoundUnder (fun _ => (1 : ℕ)) (fun _ _ => True) n ↔ x.IsChargeBound (fun _ => 1) n :=
  isChargeBoundUnder_true_iff x

example (x : FreeM Coin Bool) (n : ℕ) (h : x.IsChargeBound (fun _ => (1 : ℕ)) n) :
    x.IsChargeBoundUnder (fun _ => (1 : ℕ)) (fun _ b => b = true) n :=
  h.under _

/-- The restricted bound is the plain bound of the program relabelled to the allowed answers. -/
example : (flipThenMore.restrict fun _ b => b = true).IsChargeBound (fun _ => (1 : ℕ)) 1 := by
  have h : flipThenMore.IsChargeBoundUnder (fun _ => (1 : ℕ)) (fun _ b => b = true) 1 := by
    simp [flipThenMore]
  exact (isChargeBoundUnder_iff_restrict flipThenMore).1 h

/-- The restricted charge bound is the restricted roll bound on the amount spent. -/
example : flipThenMore.IsRollBoundUnder 0 (fun _ t => t + 1 ≤ 1) (fun _ t => t + 1)
    (fun _ b => b = true) :=
  ((isChargeBoundUnder_iff_isRollBoundUnder flipThenMore).1 (by simp [flipThenMore])).2

/-- A handler that answers each flip with a flip of its own, along the same allowed answers,
transfers the restricted bound. -/
example : (flipThenMore.liftM fun _ => FreeM.lift (P := Coin) ()).IsChargeBoundUnder
    (fun _ => (1 : ℕ)) (fun _ b => b = true) 1 :=
  IsChargeBoundUnder.liftM (P := Coin) (c := fun _ => 1) (allows := fun _ b => b = true)
    (allowsQ := fun _ b => b = true) (fun _ => FreeM.lift (P := Coin) ()) (fun _ => by simp)
    (fun _ _ hb => hb) (by simp [flipThenMore])

/-- A lens whose map of directions is not surjective: every flip is answered `true`, so the mapped
program meets the budget `1` that the program itself exceeds. Pulling a bound back along a lens
needs surjective maps of directions (`isChargeBound_mapLens_iff`). -/
example : (flipThenMore.mapLens (id ⇆ fun _ _ => true : Lens Coin Coin)).IsChargeBound
    (fun _ => (1 : ℕ)) 1 :=
  ⟨le_rfl, fun _ => le_rfl⟩

end PolyFunTest.Charge
