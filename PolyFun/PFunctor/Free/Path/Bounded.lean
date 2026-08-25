/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Bound
public import PolyFun.PFunctor.Free.Path.Execution

/-!
# Roll bounds for completed paths through free polynomial programs

This file connects the syntactic length of a completed typed path to the
branchwise total-roll bound on its source program. The result is entirely
structural: a certificate that every branch performs at most `bound` rolls
also bounds the length of every path through that program.
-/

@[expose] public section

universe uA uB v

namespace PFunctor.FreeM.Path

variable {P : PFunctor.{uA, uB}} {α : Type v}

/- Lean compares path indices over `liftBind` at implicit transparency. -/
attribute [local implicit_reducible] FreeM.bind

/-- Every completed path through a totally roll-bounded program has length at
most the certified bound. -/
theorem length_le_of_isTotalRollBound (program : FreeM P α) {bound : Nat}
    (hbound : program.IsTotalRollBound bound) (path : Path program) :
    length program path ≤ bound := by
  induction program generalizing bound with
  | pure result =>
      exact Nat.zero_le bound
  | lift_bind position next ih =>
      rcases path with ⟨answer, tail⟩
      rw [isTotalRollBound_lift_bind_iff] at hbound
      change length (next answer) tail + 1 ≤ bound
      have htail : length (next answer) tail ≤ bound - 1 :=
        ih answer (hbound.2 answer) tail
      omega

end PFunctor.FreeM.Path
