/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Free

/-!
# Lifting finite programs into resumptions and interaction trees

`FreeM p` lifts into `Resumption p`, which lifts into `ITree p`. A `do` block in `ITree p` runs
`FreeM p` programs without annotation. `Resumption p` is an abbreviation of an M-type, so the
elaborator does not see it as a monad application, and lifts into it are written with `liftM`.
The composite lift is `FreeM.toITree`, and the lawful lifts induce the bundled monad morphisms
`FreeM.toResumptionHom` and `FreeM.toITreeHom`.
-/

@[expose] public section

universe uA uB uα

namespace PolyFunTest.ITree.MonadLiftExamples

open _root_.PFunctor

variable {E : PFunctor.{uA, uB}} {α : Type uα}

example (program : FreeM E α) (k : α → _root_.ITree E α) : _root_.ITree E α := do
  let value ← program
  k value

example (program : FreeM E α) (k : α → Resumption E α) : Resumption E α := do
  let value ← liftM program
  k value

example (computation : Resumption E α) : _root_.ITree E α := liftM computation

example (program : FreeM E α) : (liftM program : _root_.ITree E α) = program.toITree := rfl

example : MonadHom.ofLift (FreeM E) (Resumption E) = FreeM.toResumptionHom := rfl

example : MonadHom.ofLift (FreeM E) (_root_.ITree E) = FreeM.toITreeHom := rfl

end PolyFunTest.ITree.MonadLiftExamples
