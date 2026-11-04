/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.PFunctor.Charge
import PolyFun.PFunctor.Free.Cost

/-!
# Ordinary-import canaries for charges and charge bounds

A charge pulled back along a lens is the composite lens, and a charge bound unfolds call by
call. Both are definitional, and these examples check that they stay so through ordinary
imports, with positions and directions in independent universes.
-/

universe uA uB uA₂ uB₂ uE w v

namespace PolyFunTest.ModuleAPI.Charge

open _root_.PFunctor

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {ω : Type w} {α : Type v}

example (m : Lens Q (C.{w, uE} ω)) (l : Lens P Q) :
    (m ∘ₗ l).toCharge = m.toCharge ∘ l.toFunA :=
  rfl

example [Add ω] [LE ω] [Zero ω] (c : P.A → ω) (B s : ω) (a : P.A) (r : P.B a → FreeM P α) :
    (FreeM.liftBind a r).IsChargeBound c B s ↔
      s + c a ≤ B ∧ ∀ b, (r b).IsChargeBound c B (s + c a) :=
  Iff.rfl

example [Add ω] [LE ω] [Zero ω] (c : P.A → ω) (B s : ω) (x : α) :
    (FreeM.pure x : FreeM P α).IsChargeBound c B s ↔ s ≤ B :=
  Iff.rfl

end PolyFunTest.ModuleAPI.Charge
