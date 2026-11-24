/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Std.WP
public import ToCslib.Data.Fin.MOfFn

/-!
# A `vcgen` rule for `Fin.mOfFn`

`Fin.mOfFn n f` (`ToCslib.Data.Fin.MOfFn`) runs `f 0`, …, `f (n - 1)` in order and collects the
results as a function on `Fin n`. Its rule `Fin.Spec.mOfFn` carries a loop invariant
`Fin.MOfFnInvariant` over the results collected so far, indexed by their number, which `vcgen`'s
`invariants` clause fills. The rule holds for every interpretation of the monad, so it is
registered globally.

`Fin.mOfFn` is staged for Mathlib, not core, so the rule lives in the namespace of the function,
as the free-program rules do in `PFunctor.FreeM.Spec`. The staging library `ToCslib` imports no
`Std.WP` module, so the rule is stated here.
-/

@[expose] public section

universe u v w z

open Std.WP Lean.Order

namespace Fin

/-- The type of loop invariants used by the specification of `Fin.mOfFn`: an assertion on the
first `k` results, for every number `k` of results collected so far. `vcgen`'s `invariants`
clause fills it. -/
@[spec_invariant_type, simp, grind =]
def MOfFnInvariant (α : Type u) (Pred : Type w) :=
  (k : ℕ) → (Fin k → α) → Pred

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α : Type u}

/-- `Fin.mOfFn` with a loop invariant over the results collected so far, indexed by their number:
the step at index `k` starts from the first `k` results and extends them by its own. -/
@[spec]
theorem Spec.mOfFn {n : ℕ} {f : Fin n → m α} (inv : MOfFnInvariant α Pred) {epost : EPred}
    (step : ∀ k (hk : k < n) (v : Fin k → α),
      ⦃ inv k v ⦄ f ⟨k, hk⟩ ⦃ fun a => inv (k + 1) (Fin.snoc v a); epost ⦄) :
    ⦃ inv 0 Fin.elim0 ⦄ Fin.mOfFn n f ⦃ fun v => inv n v; epost ⦄ := by
  induction n generalizing inv with
  | zero => exact Triple.pure _ PartialOrder.rel_refl
  | succ n ih =>
    rw [Fin.mOfFn_succ]
    refine Triple.bind _ _ _ (step 0 n.succ_pos Fin.elim0) fun a => ?_
    have h₁ : (Fin.snoc (α := fun _ => α) Fin.elim0 a : Fin 1 → α) =
        Fin.cons (α := fun _ => α) a Fin.elim0 :=
      funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl
    rw [h₁]
    refine Triple.bind _ _ _
      (ih (fun k w => inv (k + 1) (Fin.cons a w)) fun k hk w => ?_)
      fun rest => Triple.pure _ PartialOrder.rel_refl
    simp only [Fin.cons_snoc_eq_snoc_cons]
    exact step (k + 1) (Nat.succ_lt_succ hk) (Fin.cons a w)

end Fin
