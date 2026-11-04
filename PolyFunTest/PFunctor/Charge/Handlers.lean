/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Tactic
public import PolyFun.PFunctor.Handler.Charge

/-!
# Charges through handlers

Checks for `PolyFun.PFunctor.Handler.Charge`:

* a handler that implements each call by two calls is within twice the charge, and simulating
  through it doubles a unit budget, statelessly and through a counting state;
* instrumented runs stay within budget, and a run through a deterministic handler is the output
  and charge of the path it picks;
* the budget gate is transparent within budget and refuses beyond it, and the gate with a
  fallback answers beyond it;
* a caching handler makes a target call only on a miss, which grows its cache, so the amortized
  transfer bounds its target calls by the growth of the cache.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeHandlers

/-! ## Free and stateful handlers -/

/-- A single interface with two answers. -/
abbrev Coin : PFunctor := ⟨Unit, fun _ => Bool⟩

/-- Implement each call by two calls, returning the second answer. -/
def doubled : Handler (FreeM Coin) Coin := fun _ => do
  let _ ← FreeM.lift (P := Coin) ()
  FreeM.lift (P := Coin) ()

example : doubled.WithinCharge (fun _ => (1 : ℕ)) (fun _ => 2) := fun _ => by
  cost_bound [doubled]

/-- Doubling a natural-number budget. -/
def double : ℕ →+o ℕ where
  toFun n := 2 * n
  map_zero' := rfl
  map_add' a b := by omega
  monotone' a b h := by dsimp only; omega

example {α : Type} (x : FreeM Coin α) (n : ℕ) (hx : x.IsChargeBound (fun _ => 1) n) :
    (x.liftM doubled).IsChargeBound (fun _ => 1) (2 * n) := by
  have h2 : x.IsChargeBound (fun _ => 2) (2 * n) := hx.map double
  exact h2.liftM doubled fun _ => by cost_bound [doubled]

/-- A counting handler: each call increments a counter and makes two calls. -/
def counted : Handler (StateT ℕ (FreeM Coin)) Coin := fun a => do
  modify (· + 1)
  StateT.lift (doubled a)

example {α : Type} (x : FreeM Coin α) (n : ℕ) (hx : x.IsChargeBound (fun _ => 2) n) (k : ℕ) :
    ((x.liftM counted).run k).IsChargeBound (fun _ => 1) n :=
  hx.run_liftM counted (fun _ σ => by cost_bound [counted, doubled]) k

/-! ## Instrumented and deterministic runs -/

def chgN : Coin.A → ℕ := fun _ => 2

/-- Always answer `true`. -/
def answer : Handler Id Coin := fun _ => true

def flips : FreeM Coin Bool := do
  let b ← FreeM.lift (P := Coin) ()
  if b then FreeM.lift (P := Coin) () else pure false

/-- The instrumented run spends `4`, within the budget. -/
example : ((flips.liftM (answer.withCharge chgN)).run 0).2 = 4 := rfl

example : ((flips.liftM (answer.withCharge chgN)).run 0).2 ≤ 4 :=
  (show flips.IsChargeBound chgN 4 by cost_bound [flips, chgN]).le_of_canReturn_run_liftM_withCharge
    answer rfl

/-- The instrumented deterministic run is the output and charge of the path it picks. -/
example : ((flips.liftM (answer.withCharge fun _ => (3 : ℕ))).run 0).run =
    (output flips (Path.ofHandler (fun _ => true) flips),
      Path.charge (fun _ => (3 : ℕ)) flips (Path.ofHandler (fun _ => true) flips)) := by
  rw [Handler.run_liftM_withCharge_id, zero_add]
  rfl

/-- The writer form logs the same charge as the state form. -/
example : (flips.liftM (answer.withChargeW chgN)).run.run = (true, Multiplicative.ofAdd 4) := rfl

/-- On each completed path, the writer log is that path's charge. -/
example {α : Type} (x : FreeM Coin α) :
    FreeM.supp (x.liftM ((Handler.id Coin).withChargeW chgN)).run =
      Set.range fun p : Path x => (output x p, Multiplicative.ofAdd (Path.charge chgN x p)) :=
  Handler.supp_run_liftM_id_withChargeW chgN x

/-! ## Gates -/

/-- Within budget the gate is transparent; with budget `3` the second call is refused. -/
example : ((flips.liftM (answer.withBudget chgN 4)).run 0).run =
    some <$> (flips.liftM (answer.withCharge chgN)).run 0 :=
  Handler.run_liftM_withBudget_of_isChargeBound answer chgN (by cost_bound [flips, chgN])

example : ((flips.liftM (answer.withBudget chgN 3)).run 0).run = none := rfl

abbrev Keys : PFunctor.{0, 0} := ⟨ℕ, fun _ => Bool⟩

def answerTrue : Handler Id Keys := fun _ => true

def twoKeys : FreeM Keys Bool := do
  let _ ← FreeM.lift (P := Keys) 1
  FreeM.lift (P := Keys) 2

/-- Within budget, the gate with a fallback answers every call with the handler. -/
example : (twoKeys.liftM (answerTrue.withBudgetOr (fun _ => (1 : ℕ)) 2 fun _ => false)).run 0 =
    (twoKeys.liftM (answerTrue.withCharge fun _ => (1 : ℕ))).run 0 :=
  Handler.run_liftM_withBudgetOr_of_isChargeBound answerTrue _ _ (by cost_bound [twoKeys])

/-- Beyond budget, the second call gets the fallback. -/
example :
    ((twoKeys.liftM (answerTrue.withBudgetOr (fun _ => (1 : ℕ)) 1 fun _ => false)).run 0).run =
      (false, 1) := rfl

/-! ## A caching handler -/

/-- Answer a key from the cache when it has been seen, otherwise query it and remember it. -/
def cached : Handler (StateT (Finset ℕ) (FreeM Keys)) Keys := fun k cache =>
  if k ∈ cache then pure (true, cache)
  else (fun b => (b, insert k cache)) <$> FreeM.lift (P := Keys) k

theorem cached_step (a : ℕ) (σ₁ : Finset ℕ) (r : Path ((cached a).run σ₁)) :
    Path.charge (fun _ => (1 : ℕ)) _ r + σ₁.card ≤ (output _ r).2.card + 0 := by
  by_cases h : a ∈ σ₁
  · have hx : (cached a).run σ₁ = pure (true, σ₁) := by simp [cached, StateT.run, h]
    revert r
    rw [hx]
    intro r
    exact le_of_eq (by simp)
  · have hx : (cached a).run σ₁ = (fun b => (b, insert a σ₁)) <$> FreeM.lift (P := Keys) a := by
      simp [cached, StateT.run, h]
    revert r
    rw [hx]
    rintro ⟨b, ⟨⟩⟩
    change 1 + 0 + σ₁.card ≤ (insert a σ₁).card + 0
    rw [Finset.card_insert_of_notMem h]
    omega

/-- Every completed path of a cached run makes at most as many target calls as the cache grew. -/
example {α : Type} (x : FreeM Keys α) (σ₀ : Finset ℕ) (q : Path ((x.liftM cached).run σ₀)) :
    Path.charge (fun _ => (1 : ℕ)) _ q + σ₀.card ≤ (output _ q).2.card := by
  obtain ⟨p, -, hle⟩ := Path.exists_run_liftM_amortized cached (fun σ => σ.card)
    (c := fun _ => (0 : ℕ)) cached_step x σ₀ q
  have hp : Path.charge (fun _ => (0 : ℕ)) x p = 0 :=
    Path.charge_map_addMonoidHom (c := fun _ : Keys.A => (0 : ℕ)) (0 : ℕ →+ ℕ) x p
  simpa [hp] using hle

/-! ## A pausing run -/

/-- Answer the first `k` calls with one target call each, then pause. -/
def gate (k : ℕ) (a : Keys.A) (used : ℕ) : FreeM Keys (Option (Keys.B a × ℕ)) :=
  if used < k then .liftBind a fun b => .pure (some (b, used + 1)) else .pure none

/-- Free calls cost nothing. -/
theorem isChargeBound_free {α : Type} (x : FreeM Keys α) :
    x.IsChargeBound (fun _ => (0 : ℕ)) 0 0 := by
  induction x using FreeM.rec with
  | pure a => exact le_rfl
  | liftBind a r ih => exact ⟨le_rfl, ih⟩

/-- Whatever the program, a run through `gate k` makes at most `k` target calls: the potential
`k - used` pays for each one. -/
example {α : Type} (k : ℕ) (x : FreeM Keys α) :
    (runUntil (gate k) x 0).IsChargeBound (fun _ => 1) k 0 := by
  refine IsChargeBound.runUntil (B := 0) (c := fun _ => 0) (fun used => k - used)
    (fun _ => Nat.zero_le _) (fun a used e he => ?_) (isChargeBound_free x) (by omega)
  unfold gate
  split_ifs with hk
  · exact ⟨by change e + 1 ≤ k; omega,
      fun _ => by change e + 1 + (k - (used + 1)) ≤ e + (k - used) + 0; omega⟩
  · change e + (k - used) ≤ e + (k - used) + 0
    omega

end PolyFunTest.ChargeHandlers
