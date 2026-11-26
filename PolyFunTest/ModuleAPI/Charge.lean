/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.PFunctor.Charge
import PolyFun.PFunctor.Free.Cost
import PolyFun.PFunctor.Free.Cost.Count
import PolyFun.PFunctor.Free.Cost.Value
import PolyFun.PFunctor.Free.Cost.Measured

/-!
# Ordinary-import canaries for charges and charge bounds

A charge pulled back along a lens is the composite lens. A charge bound unfolds call by call,
and the worst-case cost folds the charge reading. Precomposing a measured program with an input
map runs the program on the mapped input. The examples check these definitional equations through
ordinary imports. The counting example uses the public conversion from a program budget to
a path length bound. Positions, directions, inputs, results and costs can lie in independent
universes.
-/

universe uA uB uA₂ uB₂ uE w v

namespace PolyFunTest.ModuleAPI.Charge

open _root_.PFunctor

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {ω : Type w} {α : Type v}

example (c : Q.A → ω) (l : Lens P Q) :
    ((Lens.toConst c : Lens Q (C.{w, uE} ω)) ∘ₗ l).toFunA = c ∘ l.toFunA :=
  rfl

example [Add ω] [LE ω] [Zero ω] (c : P.A → ω) (B s : ω) (a : P.A) (r : P.B a → FreeM P α) :
    (FreeM.liftBind a r).IsChargeBound c B s ↔
      s + c a ≤ B ∧ ∀ b, (r b).IsChargeBound c B (s + c a) :=
  Iff.rfl

example [Add ω] [LE ω] [Zero ω] (c : P.A → ω) (B s : ω) (x : α) :
    (FreeM.pure x : FreeM P α).IsChargeBound c B s ↔ s ≤ B :=
  Iff.rfl

example [Add ω] [CompleteLattice ω] (c : P.A → ω) (x : FreeM P α) (k : α → ω) :
    FreeM.costWith c x k = FreeM.wpFold (OpSpec.charge c) x k :=
  rfl

example [Add ω] [Zero ω] [CompleteLattice ω] (c : P.A → ω) (x : FreeM P α) :
    FreeM.cost c x = FreeM.costWith c x fun _ => 0 :=
  rfl

example {Input Input' Result : Type v} (M : FreeM.MeasuredProgram Input Result ω)
    (g : Input' → Input) (i : Input') : (M.contramap g).run i = M.run (g i) :=
  rfl

example {Input : Type uA} {Result : Type v} [AddMonoid ω] [PartialOrder ω] [CountCost ω]
    {f : Input → Result} (b : FreeM.BudgetedProgram f ω) (v : b.program.View)
    (p : FreeM.Path (b.program.program v)) (hc : ∀ a, b.program.cost a ≠ 0) :
    FreeM.Path.length (b.program.program v) p ≤ CountCost.total b.budget :=
  b.costAtMost.countAtMost.length_le_total hc v p

end PolyFunTest.ModuleAPI.Charge
