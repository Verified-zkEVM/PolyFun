/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Certified
public import PolyFun.PFunctor.Handler.Stateful.Charge
public import PolyFun.PFunctor.Free.Cost.Tactic

/-!
# Certified handlers

Checks for `PolyFun.PFunctor.Handler.Certified` and `PolyFun.PFunctor.Handler.Stateful.Charge`:

* hash queries implemented by two compression calls each, and compression calls by three steps
  each, are certified links with exchanges `2 •` and `3 •`, and they compose into a link with
  exchange `6 •`;
* a budget of `q` hash queries transfers to `6 q` steps, and in value form the worst-case cost is
  at most the exchanged cost;
* a reduction with one setup call and one finishing call has the affine bound `1 + 2 q + 1`;
* stateful certificates compose along `link`.
-/

public section

open PFunctor PFunctor.FreeM PFunctor.Handler

namespace PolyFunTest.ChargeCertified

/-- Hash queries, compression calls and machine steps, each with a Boolean answer. -/
abbrev Hash : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩
abbrev Compress : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩
abbrev Step : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- Scale a natural-number count. -/
@[expose] def scale (k : ℕ) : ℕ →+o ℕ where
  toFun n := k * n
  map_zero' := by simp
  map_add' a b := Nat.mul_add k a b
  monotone' _ _ h := by dsimp only; exact Nat.mul_le_mul_left k h

@[simp]
theorem scale_apply (k n : ℕ) : scale k n = k * n :=
  rfl

/-- Each hash query is two compression calls. -/
def hashByCompress : Handler (FreeM Compress) Hash := fun _ => do
  let _ ← FreeM.lift (P := Compress) ()
  FreeM.lift (P := Compress) ()

/-- Each compression call is three steps. -/
def compressBySteps : Handler (FreeM Step) Compress := fun _ => do
  let _ ← FreeM.lift (P := Step) ()
  let _ ← FreeM.lift (P := Step) ()
  FreeM.lift (P := Step) ()

def hashLayer : Certified Hash Compress (fun _ => (1 : ℕ)) (fun _ => 1) where
  handler := hashByCompress
  exchange := scale 2
  certificate _ := by cost_bound [hashByCompress]

def compressLayer : Certified Compress Step (fun _ => (1 : ℕ)) (fun _ => 1) where
  handler := compressBySteps
  exchange := scale 3
  certificate _ := by cost_bound [compressBySteps]

/-- The composite link exchanges a hash query for six steps. -/
example (n : ℕ) : (compressLayer.comp hashLayer).exchange n = 6 * n := by
  simp [compressLayer, hashLayer]
  omega

/-- A specification within `q` hash queries runs within `6 q` steps. -/
example {α : Type} (x : FreeM Hash α) (q : ℕ) (hx : x.IsChargeBound (fun _ => 1) q) :
    (x.liftM (compressLayer.comp hashLayer).handler).IsChargeBound (fun _ => 1) (6 * q) := by
  have h := (compressLayer.comp hashLayer).transfer hx
  simp only [Certified.comp_exchange, OrderAddMonoidHom.comp_apply, scale_apply, map_zero,
    compressLayer, hashLayer] at h
  exact h.mono (by omega)

/-! ## Value form -/

/-- Doubling in `ℕ∞`. -/
@[expose] def doubleENat : ℕ∞ →+o ℕ∞ where
  toFun n := 2 * n
  map_zero' := mul_zero 2
  map_add' a b := mul_add 2 a b
  monotone' _ _ h := by dsimp only; gcongr

@[simp]
theorem doubleENat_apply (n : ℕ∞) : doubleENat n = 2 * n :=
  rfl

def hashLayerENat : Certified Hash Compress (fun _ => (1 : ℕ∞)) (fun _ => (1 : ℕ∞)) where
  handler := hashByCompress
  exchange := doubleENat
  certificate _ := by cost_bound [hashByCompress]

/-- In value form, a simulated program costs at most the exchange of its cost. -/
example {α : Type} (x : FreeM Hash α) :
    cost (fun _ => (1 : ℕ∞)) (x.liftM hashLayerENat.handler) ≤ doubleENat (cost (fun _ => 1) x) :=
  hashLayerENat.cost_liftM_le x

/-! ## Reductions -/

/-- A reduction that makes one compression call before the simulated program, keeping its answer
as a key, and one after it, combining the key with the result. -/
def oneEachSide : CostedReduction Hash Compress (fun _ => (1 : ℕ)) (fun _ => 1) Bool Bool Bool where
  setup := FreeM.lift (P := Compress) ()
  handler _ := hashLayer.handler
  exchange := hashLayer.exchange
  certificate _ := hashLayer.certificate
  finish key b := do
    let c ← FreeM.lift (P := Compress) ()
    pure (b && c && key)
  setupCost := 1
  finishCost := 1
  setup_le := by cost_bound
  finish_le _ _ := by cost_bound

/-- The reduction's cost transformer is affine: `1 + 2 q + 1`. -/
example (x : FreeM Hash Bool) (q : ℕ) (hx : x.IsChargeBound (fun _ => 1) q) :
    (oneEachSide.run x).IsChargeBound (fun _ => 1) (1 + 2 * q + 1) := by
  simpa [CostedReduction.bound, oneEachSide, hashLayer] using oneEachSide.run_isChargeBound hx

/-! ## Stateful packages -/

/-- Each compression call is three steps; the package also counts compressions. -/
def countingSteps : Stateful (FreeM Step) ℕ Compress := fun _ count => do
  let _ ← FreeM.lift (P := Step) ()
  let _ ← FreeM.lift (P := Step) ()
  let b ← FreeM.lift (P := Step) ()
  pure (b, count + 1)

theorem countingSteps_withinCharge :
    countingSteps.WithinCharge (fun _ => (1 : ℕ)) (fun _ => 3) := fun _ count => by
  change (FreeM.bind (FreeM.lift (P := Step) ()) fun _ => FreeM.bind (FreeM.lift (P := Step) ())
    fun _ => FreeM.bind (FreeM.lift (P := Step) ()) fun b =>
      (pure (b, count + 1) : FreeM Step (Bool × ℕ))).IsChargeBound _ _
  cost_bound

/-- The hash layer, lifted to a package with trivial state, linked to the counting package:
each hash query is within `6` steps from every state. -/
example : ((Stateful.lift (S := PUnit) hashByCompress).link countingSteps).WithinCharge
    (fun _ => (1 : ℕ)) (fun _ => 6) := by
  refine Stateful.WithinCharge.link (d := fun _ => 3) ?_ countingSteps_withinCharge
  exact Handler.WithinCharge.lift fun _ => by cost_bound [hashByCompress]

end PolyFunTest.ChargeCertified
