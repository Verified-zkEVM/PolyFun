/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Semantics.Correspondence
public import PolyFun.ITree.Transition
public import Examples.Tutorials.ScopedExecution

/-! # Ordinary-import checks for the scoped execution tutorial -/

open Control.Semantics Control.Transition

public section

namespace PolyFunTest.ScopedExecution

open Examples.ScopedPrograms IPFunctor.ScopedSignature

/-- Nested lets whose body reads the outer binding. -/
def nested : Expr [] .nat :=
  .letE (.literal 4) (.letE (.literal 7) (.add (.var .zero) (.var (.succ .zero))))

/-- Fragment evidence for `nested`. -/
def nestedSupported : FirstOrder nested :=
  .letE (.literal 4) (.letE (.literal 7) (.add (.var .zero) (.var (.succ .zero))))

example : FirstOrder.runFree (FirstOrder.compile nestedSupported Env.empty) = 11 :=
  FirstOrder.compile_correct nestedSupported Env.empty

example (n : Nat) :
    Executes FirstOrder.step (FirstOrder.compile (FirstOrder.sumSupported n) Env.empty)
      ((sumTo n).denote algebra Env.empty) := by
  rw [← FirstOrder.compile_correct (FirstOrder.sumSupported n) Env.empty]
  exact FirstOrder.executes _

example (pre : Nat → Prop) (post : Nat → Nat → Prop) :
    DataContract (Function.Embedding.refl Nat) (Function.Embedding.refl Nat)
      FirstOrder.sumCertificate.meaning pre post ↔
      ∀ n, pre n → post n ((sumTo n).denote algebra Env.empty) :=
  FirstOrder.sumCertificate.contract_iff pre post

end PolyFunTest.ScopedExecution
