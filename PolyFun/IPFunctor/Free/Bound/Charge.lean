/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.IPFunctor.Free.Bound
public import PolyFun.PFunctor.Free.Cost.Value

/-!
# Charges on indexed free programs through erasure

An indexed free program erases to a plain free program whose positions `Σ s, P.A s` record the
state of each call (`toSigmaFreeM`). Charges, budgets and costs of indexed programs are those of
the erasure, with the charge read at the recorded state.

`isChargeBound_iff_toSigmaFreeM` identifies the natural-number `IFreeM.IsChargeBound` with the
spent-amount bound of the erasure, so the whole `FreeM` cost API (worst-case costs, handlers,
lenses, loops) applies to indexed programs. `IFreeM.cost` is the worst-case cost of the erasure.
-/

@[expose] public section

universe uI uA uB v w

namespace IPFunctor.IFreeM

variable {I : Type uI} {P : Endo.{uI, uA, uB} I} {X : I → Type v} {s : I}

/-- The indexed natural-number charge bound is the spent-amount charge bound of the erasure. -/
theorem isChargeBound_iff_toSigmaFreeM (x : IFreeM P X s) (c : (s : I) → P.A s → ℕ) (n : ℕ) :
    x.IsChargeBound c n ↔ (toSigmaFreeM P x).IsChargeBound (fun a => c a.1 a.2) n := by
  rw [PFunctor.FreeM.isChargeBound_iff_isRollBound_nat]
  rfl

/-- The worst-case cost of an indexed program: the cost of its erasure, with each call charged at
its state. -/
noncomputable def cost {ω : Type w} [AddCommMonoid ω] [CompleteLattice ω]
    (c : (s : I) → P.A s → ω) (x : IFreeM P X s) : ω :=
  PFunctor.FreeM.cost (fun a : P.sigmaPFunctor.A => c a.1 a.2) (toSigmaFreeM P x)

end IPFunctor.IFreeM
