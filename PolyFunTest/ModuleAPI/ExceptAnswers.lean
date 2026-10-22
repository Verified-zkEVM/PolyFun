/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Except

/-! # Ordinary-import checks for explicit exceptional answers -/

public section

open PFunctor

universe uA uB uε uα uβ u v

example {P : PFunctor.{uA, uB}} {ε : Type uε} {α : Type uα} {β : Type uβ}
    (program : FreeM P α) (next : α → FreeM P β) :
    FreeM.withExcept (ε := ε) (program.bind next) =
      (FreeM.withExcept program).bind (fun
        | .error error => .pure (.error error)
        | .ok value => FreeM.withExcept (next value)) :=
  FreeM.withExcept_bind program next

example {P : PFunctor.{uA, u}} {ε α : Type u} {m : Type u → Type v} [Monad m]
    (handler : Handler (ExceptT ε m) P) (program : FreeM P α) :
    program.withExcept.liftM handler.exceptAnswers = (program.liftM handler).run :=
  FreeM.liftM_withExcept handler program

namespace PolyFunTest.ExceptAnswers

/-- The answer type depends on the operation. -/
abbrev signature : PFunctor.{0, 0} := ⟨Bool, fun | true => Bool | false => Nat⟩

private def handler : Handler (ExceptT String (StateM Nat)) signature := fun
  | true => ExceptT.mk fun count => (.error "stopped", count + 1)
  | false => ExceptT.mk fun count => (.ok 7, count + 1)

private def client : FreeM signature Nat := do
  let n ← FreeM.lift false
  let _ ← FreeM.lift true
  let m ← FreeM.lift false
  pure (n + m)

/-- The failed second operation increments state, while the third is never interpreted. -/
example : Id.run (((client.liftM handler).run).run 0) = (.error "stopped", 2) := rfl

/-- The explicit-answer view has the same retained failure state. -/
example : Id.run ((client.withExcept.liftM handler.exceptAnswers).run 0) =
    (.error "stopped", 2) := by
  rw [FreeM.liftM_withExcept]
  rfl

end PolyFunTest.ExceptAnswers
