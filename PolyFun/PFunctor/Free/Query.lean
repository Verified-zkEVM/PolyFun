/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Cslib.Algorithms.Lean.Query.Bounds
public import PolyFun.PFunctor.Free.Path.Bounded

/-!
# Deterministic query counts for polynomial programs

A fixed oracle selects a path through a polynomial program. Its length is the query count of the
same program in CSLib's indexed query language. A total roll bound therefore supplies a uniform
query bound over all fixed oracles.
-/

public section

universe u v w

namespace PFunctor.FreeM

variable {P : PFunctor.{u, v}} {α : Type w}

/-- Interpret each operation as a CSLib query returning its original answer. -/
def toQueryProgram (program : P.FreeM α) : Cslib.FreeM P.Obj α :=
  program.foldFreeM Cslib.FreeM.pure (fun a => Cslib.FreeM.liftBind (PFunctor.Obj.mk a id))

@[simp] theorem toQueryProgram_pure (x : α) :
    (pure x : P.FreeM α).toQueryProgram = Cslib.FreeM.pure x := by
  simp [toQueryProgram]

theorem toQueryProgram_liftBind (a : P.A) (next : P.B a → P.FreeM α) :
    (FreeM.liftBind a next).toQueryProgram =
      Cslib.FreeM.liftBind (PFunctor.Obj.mk a id) (fun b => (next b).toQueryProgram) := by
  simp [toQueryProgram]

/-- A fixed oracle makes one query per operation on the path its answers select. -/
theorem countQueries_toQueryProgram {α : Type v} (oracle : {β : Type v} → P.Obj β → β)
    (program : P.FreeM α) :
    program.toQueryProgram.countQueries oracle =
      Path.length program (Path.ofHandler (fun a => oracle (PFunctor.Obj.mk a id)) program) := by
  induction program with
  | pure => rfl
  | lift_bind a next ih =>
    change 1 + (next (oracle (PFunctor.Obj.mk a id))).toQueryProgram.countQueries oracle =
      Path.length _ _ + 1
    rw [ih, Nat.add_comm]
    simp

/-- A monotone bound on the number of rolls at each input size bounds the number of queries
for every fixed oracle and every input up to that size. -/
theorem queryUpperBound_of_isTotalRollBound {α : Type v} {X : Type*} (family : X → P.FreeM α)
    {size : X → ℕ} {bound : ℕ → ℕ} (hmono : Monotone bound)
    (hbound : ∀ x, (family x).IsTotalRollBound (bound (size x))) :
    Cslib.Query.UpperBound (fun x => (family x).toQueryProgram) size bound :=
  Cslib.Query.UpperBound.of_pointwise hmono fun oracle x => by
    rw [countQueries_toQueryProgram]
    exact Path.length_le_of_isTotalRollBound _ (hbound x) _

end PFunctor.FreeM
