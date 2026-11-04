/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.WP.Budget
public import PolyFun.PFunctor.Free.Cost.Tactic
public import ToCslib.Data.PFunctor.Free.Basic
public import ToCslib.Data.PFunctor.Free.Loops

/-!
# Core `vcgen` on charges

Checks for `PolyFun.PFunctor.Free.WP.Budget`:

* under the budget reading, `vcgen` steps through every call of a free program;
* a charge bound is a triple of the budget reading (`isChargeBound_iff_triple`), so a bound
  computed by `cost_bound` is a triple;
* instrumented calls (`withCharge`) are state updates, so `vcgen` with a loop invariant bounds
  the amount spent by a `StateT` loop;
* for a free program over a generic interface, `liftM` unfolds through the loop, `vcgen` proves the
  spend of the instrumented run, and `triple_liftM_id_withCharge_iff` turns that triple into a
  bound on the charge of every completed path;
* with the `liftM` equations as `vcgen` rules, the instrumented run of a branching program goes
  through `FreeM.liftM_ite`.
-/

public section

open Std.WP PFunctor
open scoped PFunctor.FreeM.BudgetReading PFunctor.Handler.ChargeSteps

set_option experimental.vcgen true

namespace PFunctor.BudgetTest

abbrev Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

def flips : FreeM Coin Bool := do
  let b ← FreeM.lift (P := Coin) ()
  if b then FreeM.lift (P := Coin) () else pure false

def twoFlipsPure : FreeM Coin Bool := do
  let b ← FreeM.lift (P := Coin) ()
  let c ← FreeM.lift (P := Coin) ()
  pure (b && c)

section BudgetReading

/-- The budget reading of the unit charge with budget `3`. -/
abbrev coinBudget : WPMonad (FreeM Coin) (ℕ → Prop) EStack⟨⟩ :=
  FreeM.budgetWPMonad (fun _ => 1) 3

attribute [local instance] coinBudget

/- Under the budget reading, `vcgen` goes through every call. A `do` block that ends in a call is
not matched by the call rule, because the elaborator has reduced its value type to `Bool` (see
`docs/development/troubleshooting.md`), so the program ends in `pure`. -/
example : ⦃ fun s => s = 0 ⦄ twoFlipsPure ⦃ fun _ s => s ≤ 3 ⦄ := by
  unfold twoFlipsPure
  vcgen
  all_goals simp_all

end BudgetReading

/-- A budget computed by `cost_bound`, read as a triple of the budget reading. -/
example : @Triple (ℕ → Prop) EStack⟨⟩ (FreeM Coin Bool) Bool _ _ flips
    ((FreeM.budgetWPMonad (fun _ => (1 : ℕ)) 2).toWP Bool) (fun t => t = 0) (fun _ t => t ≤ 2)
    ⊥ :=
  (FreeM.isChargeBound_iff_triple _ _ flips 0).1 (by cost_bound [flips])

section Instrumented

open scoped PFunctor.FreeM.DemonicWP

/-- `n` instrumented calls, each charged `2`. -/
def chargedLoop (n : ℕ) : StateT ℕ (FreeM Coin) Unit := do
  for _ in List.range n do
    let _ ← (Handler.id Coin).withCharge (fun _ => 2) ()

theorem chargedLoop_spec (n : ℕ) :
    ⦃ fun s => s = 0 ⦄ chargedLoop n ⦃ fun _ s => s = 2 * n ⦄ := by
  vcgen [chargedLoop, Handler.id] invariants
    · fun pref _ _ s => s = 2 * pref.length
  all_goals simp_all
  all_goals omega

variable {P : PFunctor.{0, 0}}

/-- `n` calls at `a`, as a free program. -/
def loopCalls (a : P.A) (n : ℕ) : FreeM P Unit := do
  for _ in List.range n do
    let _ ← FreeM.lift (P := P) a

/-- `vcgen` proves the spend of the instrumented run of a free program with a loop. Over a generic
interface, a `simp` pass unfolding `liftM` first is harmless: the value type of each call stays
`P.B a`. -/
theorem loopCalls_spend (c : P.A → ℕ) (a : P.A) (n : ℕ) :
    ⦃ fun s => s = 0 ⦄ (loopCalls a n).liftM ((Handler.id P).withCharge c)
      ⦃ fun _ s => s ≤ n * c a ⦄ := by
  simp only [loopCalls, FreeM.liftM_bind, FreeM.liftM_forIn, FreeM.liftM_lift', FreeM.liftM_pure]
  vcgen [Handler.id] invariants
    · fun pref _ _ s => s = pref.length * c a
  all_goals simp_all [Nat.succ_mul]

/-- The triple bounds the charge of every completed path. -/
example (c : P.A → ℕ) (a : P.A) (n : ℕ) (p : FreeM.Path (loopCalls a n)) :
    FreeM.Path.charge c (loopCalls a n) p ≤ n * c a := by
  simpa using (Handler.triple_liftM_id_withCharge_iff c (loopCalls a n) 0
    (fun _ s => s ≤ n * c a)).1 (loopCalls_spend c a n) p

/-- A free program with a branch. -/
def branchy (a : P.A) (b : Bool) : FreeM P Unit := do
  let _ ← FreeM.lift (P := P) a
  if b then
    let _ ← FreeM.lift (P := P) a
    pure ()
  else pure ()

/-- With the `liftM` equations as `vcgen` rules, branches go through `FreeM.liftM_ite`. -/
example (c : P.A → ℕ) (a : P.A) (b : Bool) :
    ⦃ fun s => s = 0 ⦄ (branchy a b).liftM ((Handler.id P).withCharge c)
      ⦃ fun _ s => s ≤ 2 * c a ⦄ := by
  unfold branchy
  vcgen [FreeM.liftM_lift_bind', FreeM.liftM_ite, FreeM.liftM_pure, Handler.id]
  all_goals simp_all
  all_goals omega

end Instrumented

end PFunctor.BudgetTest
