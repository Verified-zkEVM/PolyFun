/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.PFunctor.Bound

/-!
# Ordinary-import canaries for roll bounds through transformers

Roll bounds of `ExceptT` and `OptionT` computations over `FreeM P` compose through the
transformer's bind, with positions and directions in independent universes. Errors and
failures are leaves, and lifting a free program keeps its bound.
-/

universe uA uB v

namespace PolyFunTest.ModuleAPI.RollBound

open _root_.PFunctor

variable {P : PFunctor.{uA, uB}} {ε α β : Type v}

example {x : ExceptT ε (FreeM P) α} {f : α → ExceptT ε (FreeM P) β} {a b : Nat}
    (hx : x.run.IsTotalRollBound a) (hf : ∀ value, (f value).run.IsTotalRollBound b) :
    (x >>= f).run.IsTotalRollBound (a + b) :=
  FreeM.isTotalRollBound_exceptT_bind hx hf

example {x : OptionT (FreeM P) α} {f : α → OptionT (FreeM P) β} {a b : Nat}
    (hx : x.run.IsTotalRollBound a) (hf : ∀ value, (f value).run.IsTotalRollBound b) :
    (x >>= f).run.IsTotalRollBound (a + b) :=
  FreeM.isTotalRollBound_optionT_bind hx hf

/-- The general form takes the same combination as `FreeM.isRollBound_bind`. -/
example {x : ExceptT ε (FreeM P) α} {f : α → ExceptT ε (FreeM P) β} {a b : Nat}
    (hx : x.run.IsRollBound a (fun _ budget => 0 < budget) (fun _ budget => budget - 1))
    (hf : ∀ value,
      (f value).run.IsRollBound b (fun _ budget => 0 < budget) (fun _ budget => budget - 1)) :
    (x >>= f).run.IsRollBound (a + b) (fun _ budget => 0 < budget)
      (fun _ budget => budget - 1) :=
  FreeM.isRollBound_exceptT_bind (· + ·) (by grind) (by grind) hx hf

example (error : ε) (value : α) (n : Nat) :
    (throw error : ExceptT ε (FreeM P) α).run.IsTotalRollBound n ∧
      (pure value : ExceptT ε (FreeM P) α).run.IsTotalRollBound n :=
  ⟨FreeM.isTotalRollBound_exceptT_throw error n, FreeM.isTotalRollBound_exceptT_pure value n⟩

example (value : α) (n : Nat) :
    (failure : OptionT (FreeM P) α).run.IsTotalRollBound n ∧
      (pure value : OptionT (FreeM P) α).run.IsTotalRollBound n :=
  ⟨FreeM.isTotalRollBound_optionT_failure n, FreeM.isTotalRollBound_optionT_pure value n⟩

example (x : FreeM P α) (n : Nat) :
    (ExceptT.lift x : ExceptT ε (FreeM P) α).run.IsTotalRollBound n ↔ x.IsTotalRollBound n :=
  FreeM.isTotalRollBound_exceptT_lift_iff x n

example (x : FreeM P α) (n : Nat) :
    (OptionT.lift x : OptionT (FreeM P) α).run.IsTotalRollBound n ↔ x.IsTotalRollBound n :=
  FreeM.isTotalRollBound_optionT_lift_iff x n

end PolyFunTest.ModuleAPI.RollBound
