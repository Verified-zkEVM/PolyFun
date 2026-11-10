/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import PolyFun.PFunctor.Handler.CertifiedUnder

/-!
# Certified handlers over allowed answers

Checks for `PolyFun.PFunctor.Handler.CertifiedUnder` at use vectors in `ι → ℕ∞`:

* with every answer allowed, `isChargeBoundUnder_liftM_demand` gives
  `isChargeBound_liftM_demand`;
* over allowed answers, the demand rule reads in value form as a bound on `costUnder`.
-/

public section

open PFunctor PFunctor.FreeM PFunctor.Handler

namespace PolyFunTest.ChargeCertifiedUnder

universe uA uB

variable {P Q : PFunctor.{uA, uB}} {ι ι' : Type*} [Fintype ι] {α : Type uB}

/-- With every answer allowed, the restricted demand rule is the demand rule. -/
example {c : P.A → ι → ℕ∞} {e : Q.A → ι' → ℕ∞} {h : Handler (FreeM Q) P} {d : ι → ι' → ℕ∞}
    (hd : 0 ≤ d) (hh : ∀ a, (h a).IsChargeBound e (∑ i, c a i • d i)) {x : FreeM P α} {u : ι → ℕ∞}
    (hx : x.IsChargeBound c u) : (x.liftM h).IsChargeBound e (∑ i, u i • d i) := by
  have hh' : ∀ a, (h a).IsChargeBoundUnder e (fun _ _ => True) (∑ i, c a i • d i) :=
    fun a => (isChargeBoundUnder_true_iff _).2 (hh a)
  exact (isChargeBoundUnder_true_iff _).1
    (isChargeBoundUnder_liftM_demand hd hh'
      (fun a => wpFold_demonicUnder_of_forall _ (fun _ => trivial) (h a))
      ((isChargeBoundUnder_true_iff _).2 hx))

/-- The demand rule over allowed answers, for worst-case costs in `ι' → ℕ∞`. -/
example {c : P.A → ι → ℕ∞} {allowsP : (a : P.A) → P.B a → Prop} {e : Q.A → ι' → ℕ∞}
    {allowsQ : (q : Q.A) → Q.B q → Prop} {x : FreeM P α} {u : ι → ℕ∞}
    {h : (a : P.A) → FreeM Q (P.B a)} {d : ι → ι' → ℕ∞} (hd : 0 ≤ d)
    (hx : costUnder c allowsP x ≤ u)
    (hh : ∀ a, costUnder e allowsQ (h a) ≤ ∑ i, c a i • d i)
    (hout : ∀ a, wpFold (OpSpec.demonicUnder allowsQ) (h a) (allowsP a)) :
    costUnder e allowsQ (x.liftM h) ≤ ∑ i, u i • d i :=
  isChargeBoundUnder_iff_costUnder_le.1
    (isChargeBoundUnder_liftM_demand hd
      (fun a => isChargeBoundUnder_iff_costUnder_le.2 (hh a)) hout
      (isChargeBoundUnder_iff_costUnder_le.2 hx))

end PolyFunTest.ChargeCertifiedUnder
