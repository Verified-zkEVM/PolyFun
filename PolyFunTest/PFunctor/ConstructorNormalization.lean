/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Path.Execution

/-!
# Free-constructor normalization through ordinary imports

Maps, binds and folds preserve the query-constructor normal form, including named operations
whose result universe differs from the direction universe. Path indices remain valid during
the same simplification pass.
-/

public section

open PFunctor

universe uA uB uX

example {P : PFunctor.{uA, uB}} {X : Type uX} (a : P.A) (next : P.B a → FreeM P X) :
    (FreeM.lift a).bind next = FreeM.liftBind a next := by simp

example {P : PFunctor.{uA, uB}} {X Y : Type uX}
    (a : P.A) (next : P.B a → FreeM P X) (f : X → Y) :
    f <$> FreeM.liftBind a next = FreeM.liftBind a (fun b => f <$> next b) := by simp

example {P : PFunctor.{uA, uB}} {X : Type uB}
    (a : P.A) (next : P.B a → FreeM P X) (choose : (a : P.A) → P.B a) :
    FreeM.Path.length (FreeM.lift a >>= next)
      (FreeM.Path.ofHandler choose (FreeM.lift a >>= next)) =
        FreeM.Path.length (next (choose a))
          (FreeM.Path.ofHandler choose (next (choose a))) + 1 := by
  simp

/-! ## Concrete position and direction families

Specializing a polynomial changes the hidden type argument of a sigma path constructor. The
simplifier must still find constructor equations after that type projection has reduced.
-/

example {I : Type uA} {D : I → Type uB} {X : Type uX}
    (a : I) (next : D a → FreeM ⟨I, D⟩ X) (choose : (a : I) → D a) :
    FreeM.Path.positions (FreeM.liftBind (P := ⟨I, D⟩) a next)
      (FreeM.Path.ofHandler choose (FreeM.liftBind (P := ⟨I, D⟩) a next)) =
        a :: FreeM.Path.positions (next (choose a))
          (FreeM.Path.ofHandler choose (next (choose a))) := by simp

example {I : Type uA} {D : I → Type uB} {X : Type uX}
    (a : I) (next : D a → FreeM ⟨I, D⟩ X) (choose : (a : I) → D a) :
    FreeM.Path.length (FreeM.liftBind (P := ⟨I, D⟩) a next)
      (FreeM.Path.ofHandler choose (FreeM.liftBind (P := ⟨I, D⟩) a next)) =
        FreeM.Path.length (next (choose a))
          (FreeM.Path.ofHandler choose (next (choose a))) + 1 := by simp

example {I : Type uA} {D : I → Type uB} {X : Type uX}
    (a : I) (next : D a → FreeM ⟨I, D⟩ X) (choose : (a : I) → D a) :
    FreeM.output (FreeM.liftBind (P := ⟨I, D⟩) a next)
      (FreeM.Path.ofHandler choose (FreeM.liftBind (P := ⟨I, D⟩) a next)) =
        FreeM.output (next (choose a))
          (FreeM.Path.ofHandler choose (next (choose a))) := by simp
