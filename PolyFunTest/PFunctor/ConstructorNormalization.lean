/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Path.Execution

/-!
# Free-constructor normal form through ordinary imports

Upstream simplification presents an operation node as `(FreeM.lift a).bind next`, or as
`FreeM.lift a >>= next` when results and directions share a universe. Maps, folds, handler
evaluation and path observations all reduce through those spellings in one ordinary `simp`
call, starting from either the constructor or the normal form, including for concrete
position and direction families whose sigma path types have already reduced.
-/

public section

open PFunctor

universe uA uB uX uY

/-! ## The two normal forms -/

example {P : PFunctor.{uA, uB}} {X : Type uX} (a : P.A) (next : P.B a → FreeM P X) :
    FreeM.liftBind a next = (FreeM.lift a).bind next := by simp

example {P : PFunctor.{uA, uB}} {X : Type uB} (a : P.A) (next : P.B a → FreeM P X) :
    FreeM.liftBind a next = FreeM.lift a >>= next := by simp

/-! ## Maps and folds through a node -/

example {P : PFunctor.{uA, uB}} {X Y : Type uX}
    (a : P.A) (next : P.B a → FreeM P X) (f : X → Y) :
    f <$> FreeM.liftBind a next = (FreeM.lift a).bind (fun b => f <$> next b) := by simp

example {P : PFunctor.{uA, uB}} {X : Type uX} {Y : Type uY}
    (a : P.A) (next : P.B a → FreeM P X) (f : X → Y) :
    FreeM.map f (FreeM.liftBind a next) =
      (FreeM.lift a).bind (fun b => FreeM.map f (next b)) := by simp

example {P : PFunctor.{uA, uB}} {m : Type uB → Type uX} [Monad m] [LawfulMonad m]
    {X : Type uB} (s : (a : P.A) → m (P.B a)) (a : P.A) (next : P.B a → FreeM P X) :
    FreeM.liftM s (FreeM.liftBind a next) = s a >>= fun b => FreeM.liftM s (next b) := by
  simp

/-! ## Path observations in both spellings -/

example {P : PFunctor.{uA, uB}} {X : Type uB}
    (a : P.A) (next : P.B a → FreeM P X) (choose : (a : P.A) → P.B a) :
    FreeM.Path.length (FreeM.lift a >>= next)
      (FreeM.Path.ofHandler choose (FreeM.lift a >>= next)) =
        FreeM.Path.length (next (choose a))
          (FreeM.Path.ofHandler choose (next (choose a))) + 1 := by
  simp

example {P : PFunctor.{uA, uB}} {X : Type uX}
    (a : P.A) (next : P.B a → FreeM P X) (choose : (a : P.A) → P.B a) :
    FreeM.Path.length ((FreeM.lift a).bind next)
      (FreeM.Path.ofHandler choose ((FreeM.lift a).bind next)) =
        FreeM.Path.length (next (choose a))
          (FreeM.Path.ofHandler choose (next (choose a))) + 1 := by
  simp

/-! ## Concrete position and direction families

Specializing a polynomial reduces the hidden type argument of a sigma path constructor. The
constructor equations leave the path as a variable and project on the right, so `simp` still
finds them after that reduction, whichever spelling the node arrives in. -/

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

example {I : Type uA} {D : I → Type uB} {X : Type uB}
    (a : I) (next : D a → FreeM ⟨I, D⟩ X) (choose : (a : I) → D a) :
    FreeM.output (FreeM.liftBind (P := ⟨I, D⟩) a next)
      (FreeM.Path.ofHandler choose (FreeM.liftBind (P := ⟨I, D⟩) a next)) =
        FreeM.output (next (choose a))
          (FreeM.Path.ofHandler choose (next (choose a))) := by simp
