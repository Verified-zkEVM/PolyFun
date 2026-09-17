/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Data.PFunctor.Free.Loops

/-!
# Canaries for the staged free-monad API

These examples exercise compositional mapping and folding, the fold's universal property,
handler fusion, and transport of loops through monadic interpretation. Concrete signatures
include dependent finite response types.
-/

public section

open PFunctor

/-- A single-position interface with boolean responses. -/
abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

/-- The functor equation fires on a constructor-spelled goal. -/
example (f : Nat → Nat) (cont : Bool → FreeM coinP Nat) :
    FreeM.map f (FreeM.liftBind PUnit.unit cont) =
      FreeM.liftBind PUnit.unit fun b => FreeM.map f (cont b) := by
  rw [FreeM.map_liftBind]

/-- Folding a node composes the sequencing law with the single-operation law. -/
example (onValue : Nat → Nat) (onEffect : (a : coinP.A) → (coinP.B a → Nat) → Nat)
    (a : coinP.A) (cont : coinP.B a → FreeM coinP Nat) :
    FreeM.foldFreeM onValue onEffect ((FreeM.lift a).bind cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  rw [FreeM.foldFreeM_bind, FreeM.foldFreeM_lift]

example (onValue : Nat → Nat) (onEffect : (a : coinP.A) → (coinP.B a → Nat) → Nat)
    (a : coinP.A) (cont : Bool → FreeM coinP Nat) :
    FreeM.foldFreeM onValue onEffect (FreeM.lift a >>= cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  rw [← FreeM.bind_eq_bind, FreeM.foldFreeM_bind, FreeM.foldFreeM_lift]

example (onValue : Nat → Nat) (onEffect : (a : coinP.A) → (coinP.B a → Nat) → Nat)
    (a : coinP.A) (cont : Bool → FreeM coinP Nat) :
    FreeM.foldFreeM onValue onEffect (FreeM.liftBind a cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  rw [FreeM.foldFreeM_liftBind]

/-- The same equations on a generic interface, where the response type stays a projection. -/
example {P : PFunctor.{0, 0}} (onValue : Nat → Nat) (onEffect : (a : P.A) → (P.B a → Nat) → Nat)
    (a : P.A) (cont : P.B a → FreeM P Nat) :
    FreeM.foldFreeM onValue onEffect ((FreeM.lift a).bind cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  rw [FreeM.foldFreeM_bind, FreeM.foldFreeM_lift]

example {P : PFunctor.{0, 0}} (onValue : Nat → Nat) (onEffect : (a : P.A) → (P.B a → Nat) → Nat)
    (a : P.A) (cont : P.B a → FreeM P Nat) :
    FreeM.foldFreeM onValue onEffect (FreeM.lift a >>= cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  rw [← FreeM.bind_eq_bind, FreeM.foldFreeM_bind, FreeM.foldFreeM_lift]

/-- Interpretation through a handler is the fold into the target monad's algebra. -/
example (s : (a : coinP.A) → Option (coinP.B a)) :
    (fun x : FreeM coinP Nat => x.liftM s) =
      FreeM.foldFreeM pure fun a k => s a >>= k :=
  FreeM.foldFreeM_unique _ _ _ (fun _ => rfl) fun a cont => FreeM.liftM_lift_bind s a cont

/-- Interpretation is natural along a monad morphism (cslib's `map_pfunctorFreeMLiftM`). -/
example (s : (a : coinP.A) → Id (coinP.B a)) (x : FreeM coinP Nat) :
    (fun y : Id Nat => (pure y.run : Option Nat)) (FreeM.liftM s x) =
      FreeM.liftM (fun a => (pure (s a).run : Option (coinP.B a))) x :=
  (Cslib.IsMonadHom.mk' (m := Id) (n := Option) (f := fun {_} y => pure y.run)
    (fun _ => rfl) (fun _ _ => rfl)).map_pfunctorFreeMLiftM s x

/-- Interpretation is itself a monad morphism, so cslib's list transport applies to it. -/
example (s : (a : coinP.A) → Option (coinP.B a)) (l : List Nat) (f : Nat → FreeM coinP Nat) :
    FreeM.liftM s (l.mapM f) = l.mapM fun a => FreeM.liftM s (f a) :=
  FreeM.liftM_mapM s f l

/-- Interpretation commutes with a `for` loop over a list. -/
example (s : (a : coinP.A) → Option (coinP.B a)) (l : List Nat) (init : Nat)
    (f : Nat → Nat → FreeM coinP (ForInStep Nat)) :
    FreeM.liftM s (forIn l init f) = forIn l init fun a b => FreeM.liftM s (f a b) :=
  FreeM.liftM_forIn s l init f

/-- Handler fusion. -/
example (x : FreeM coinP Nat) (first : (a : coinP.A) → FreeM coinP (coinP.B a))
    (second : (a : coinP.A) → Option (coinP.B a)) :
    (x.liftM first).liftM second = x.liftM fun a => (first a).liftM second :=
  FreeM.liftM_comp x first second

/- Dependent response types must not prevent simp from finding the lift equation. -/
example (n : Nat) (onValue : Fin n → Nat)
    (onEffect : (n : Nat) → (Fin n → Nat) → Nat) :
    PFunctor.FreeM.foldFreeM onValue onEffect
      (PFunctor.FreeM.lift (P := ⟨Nat, Fin⟩) n) = onEffect n onValue := by
  simp

/-- Sequencing may raise the result universe without changing the algebra's carrier. -/
example (n : Nat) (onEffect : (n : Nat) → (Fin n → Nat) → Nat) :
    FreeM.foldFreeM ULift.down onEffect
      ((FreeM.lift (P := ⟨Nat, Fin⟩) n).bind
        (fun b => pure (ULift.up b.val : ULift.{1} Nat))) = onEffect n Fin.val := by
  rw [FreeM.foldFreeM_bind, FreeM.foldFreeM_lift]
  rfl
