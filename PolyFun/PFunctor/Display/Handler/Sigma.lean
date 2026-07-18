/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Handler
public import PolyFun.PFunctor.Handler

/-!
# Indexed coproducts of displayed handlers

The base `PFunctor.Handler.sigma` operation combines an indexed family of
monadic handlers. This file lifts that operation to displayed handler witnesses
over `Display.sigma`. These are the multi-input composition primitives used by
`PFunctor.Wiring`.
-/

@[expose] public section

universe uI uA uA' uB uB' uC uD uC' uD'

namespace PFunctor

namespace Display
namespace Handler

/-- Combine displayed handlers over an indexed family into one displayed
handler from `Display.sigma`. -/
def sigma {I : Type uI} {P : I → PFunctor.{uA, uB}}
    {Q : PFunctor.{uA', uB'}}
    (S : (i : I) → Display.{uA, uB, uC, uD} (P i))
    (T : Display.{uA', uB', uC', uD'} Q)
    {f : (i : I) → (a : (P i).A) → FreeM Q ((P i).B a)}
    (df : (i : I) → Display.Handler (S i) T (f i)) :
    Display.Handler (Display.sigma S) T (PFunctor.Handler.sigma f) :=
  fun a c => df a.1 a.2 c

@[simp]
theorem sigma_apply {I : Type uI} {P : I → PFunctor.{uA, uB}}
    {Q : PFunctor.{uA', uB'}}
    (S : (i : I) → Display.{uA, uB, uC, uD} (P i))
    (T : Display.{uA', uB', uC', uD'} Q)
    {f : (i : I) → (a : (P i).A) → FreeM Q ((P i).B a)}
    (df : (i : I) → Display.Handler (S i) T (f i))
    (i : I) (a : (P i).A) (c : (S i).position a) :
    sigma S T df ⟨i, a⟩ c = df i a c :=
  rfl

/-- The displayed handler for one coproduct injection. -/
def sigmaInj {I : Type uI} {P : I → PFunctor.{uA, uB}}
    (S : (i : I) → Display.{uA, uB, uC, uD} (P i)) (i : I) :
    Display.Handler (S i) (Display.sigma S)
      (fun a => FreeM.lift (P := PFunctor.sigma P) ⟨i, a⟩) :=
  fun a c => Display.Handler.id (Display.sigma S) ⟨i, a⟩ c

@[simp]
theorem sigmaInj_apply {I : Type uI} {P : I → PFunctor.{uA, uB}}
    (S : (i : I) → Display.{uA, uB, uC, uD} (P i))
    (i : I) (a : (P i).A) (c : (S i).position a) :
    sigmaInj S i a c =
      ⟨c, fun b d => (Display.sigma S).leaf ((S i).direction a c) b d⟩ :=
  rfl

end Handler
end Display
end PFunctor
