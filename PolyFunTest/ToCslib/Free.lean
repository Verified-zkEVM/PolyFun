/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.Data.PFunctor.Free.Loops

/-!
# Canaries for the staged free-monad API

These examples pin the behaviour of `ToCslib.Data.PFunctor.Free`: the opt-in case principle
presents nodes in simp normal form, the functor and fold equations fire on constructor-spelled
goals without disabling `liftBind_eq` and on a reducible concrete interface, the catamorphism is
characterised by its universal property (interpretation *is* the fold), interpretation is a
monad morphism in cslib's sense, and it commutes with list loops.
-/

public section

open PFunctor

/-- A single-position interface with boolean responses. -/
abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

/-- `FreeM.cases` produces the `(lift a).bind cont` normal form, on which `simp` continues. -/
example (x : FreeM coinP Nat) : FreeM.map id x = x := by
  cases x using FreeM.cases with
  | pure a => rfl
  | lift_bind a cont => simp

/-- The functor equation fires on a constructor-spelled goal. -/
example (f : Nat → Nat) (cont : Bool → FreeM coinP Nat) :
    FreeM.map f (FreeM.liftBind PUnit.unit cont) =
      FreeM.liftBind PUnit.unit fun b => FreeM.map f (cont b) := by
  simp

/-- The fold equations fire under `simp`, in both the `.bind` and the `>>=` spelling, and
on a constructor-spelled node (which `simp` first normalises). They are stated through
`lift_bind%` / `lift_bind'%`, so they also fire on the reducible interface `coinP`, where the
node's response type `coinP.B a` reduces to `Bool` in `simp`'s index (`docs/wiki/gotchas.md`,
6b); a lemma indexed on the projection `P.B a`, such as cslib's `liftM_lift_bind`, does not. -/
example (onValue : Nat → Nat) (onEffect : (a : coinP.A) → (coinP.B a → Nat) → Nat)
    (a : coinP.A) (cont : coinP.B a → FreeM coinP Nat) :
    FreeM.foldFreeM onValue onEffect ((FreeM.lift a).bind cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  simp

example (onValue : Nat → Nat) (onEffect : (a : coinP.A) → (coinP.B a → Nat) → Nat)
    (a : coinP.A) (cont : Bool → FreeM coinP Nat) :
    FreeM.foldFreeM onValue onEffect (FreeM.lift a >>= cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  simp

example (onValue : Nat → Nat) (onEffect : (a : coinP.A) → (coinP.B a → Nat) → Nat)
    (a : coinP.A) (cont : Bool → FreeM coinP Nat) :
    FreeM.foldFreeM onValue onEffect (FreeM.liftBind a cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  simp

/-- The same equations on a generic interface, where the response type stays a projection. -/
example {P : PFunctor.{0, 0}} (onValue : Nat → Nat) (onEffect : (a : P.A) → (P.B a → Nat) → Nat)
    (a : P.A) (cont : P.B a → FreeM P Nat) :
    FreeM.foldFreeM onValue onEffect ((FreeM.lift a).bind cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  simp

example {P : PFunctor.{0, 0}} (onValue : Nat → Nat) (onEffect : (a : P.A) → (P.B a → Nat) → Nat)
    (a : P.A) (cont : P.B a → FreeM P Nat) :
    FreeM.foldFreeM onValue onEffect (FreeM.lift a >>= cont) =
      onEffect a fun b => FreeM.foldFreeM onValue onEffect (cont b) := by
  simp

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
