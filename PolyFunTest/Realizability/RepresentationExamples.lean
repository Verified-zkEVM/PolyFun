/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Realizability.Instances
public import PolyFun.Realizability.Representation

/-!
# Representation translation and coding examples

These examples pin the ordinary-import surface for representation invariance
and exercise each semantic word-code constructor.
-/

@[expose] public section

namespace PFunctor.RealizabilityRepresentationExamples

open PFunctor
open PFunctor.DynSystem.DynComputation

/-! ## A syntax tree used as a word universe -/

inductive Word where
  | atom : Nat → Word
  | pair : Word → Word → Word
  | inl : Word → Word
  | inr : Word → Word
  | none : Word
  | some : Word → Word
deriving DecidableEq

def pairing : StepClass.CodePairing Word where
  pair := Word.pair
  fst
    | .pair left _ => left
    | word => word
  snd
    | .pair _ right => right
    | word => word
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl

def sumCodec : StepClass.CodeSum Word where
  inl := Word.inl
  inr := Word.inr
  split
    | .inl word => some (Sum.inl word)
    | .inr word => some (Sum.inr word)
    | _ => none
  split_inl _ := rfl
  split_inr _ := rfl

def optionCodec : StepClass.CodeOption Word where
  noneCode := Word.none
  someCode := Word.some
  split
    | .none => some none
    | .some word => some (some word)
    | _ => none
  split_none := rfl
  split_some _ := rfl

def natCode : StepClass.CodeRetract Word Nat where
  encode := Word.atom
  decode
    | .atom value => some value
    | _ => none
  decode_encode _ := rfl

example (left right : Nat) :
    (natCode.prod pairing natCode).decode
      ((natCode.prod pairing natCode).encode (left, right)) = some (left, right) :=
  (natCode.prod pairing natCode).decode_encode (left, right)

example (value : Nat ⊕ Nat) :
    (natCode.sum sumCodec natCode).decode
      ((natCode.sum sumCodec natCode).encode value) = some value :=
  (natCode.sum sumCodec natCode).decode_encode value

example (value : Option Nat) :
    (natCode.option optionCodec).decode
      ((natCode.option optionCodec).encode value) = some value :=
  (natCode.option optionCodec).decode_encode value

def fiberCode (_ : Bool) : StepClass.CodeRetract Word Nat := natCode

def boolCode : StepClass.CodeRetract Word Bool where
  encode
    | false => Word.inl (Word.atom 0)
    | true => Word.inr (Word.atom 0)
  decode
    | .inl (.atom 0) => some false
    | .inr (.atom 0) => some true
    | _ => none
  decode_encode value := by cases value <;> rfl

example (entry : Σ _ : Bool, Nat) :
    (boolCode.sigma pairing fiberCode).decode
      ((boolCode.sigma pairing fiberCode).encode entry) = some entry :=
  (boolCode.sigma pairing fiberCode).decode_encode entry

/-! ## Admissible coding and boundary invariance -/

def natPolyCodable : StepClass.PolyCodable
    (C := StepClass.unconstrained.{0, 0}) (W := Word) (A := Nat)
    PUnit.unit PUnit.unit :=
  StepClass.PolyCodable.ofCodeRetract natCode True.intro True.intro

example : Function.Injective natPolyCodable.encode :=
  natPolyCodable.encode_injective

example {C : StepClass.{0, 0}} {A B : Type} {a a' : C.Str A}
    {b b' : C.Str B} (ha : C.PolyTranslatable a a')
    (hb : C.PolyTranslatable b b') (f : A → B) :
    C.Hom a b f ↔ C.Hom a' b' f :=
  ha.hom_iff hb f

example {C : StepClass.{0, 0}} [C.HasProd] [C.HasSum] [C.HasOption]
    {p : PFunctor.{0, 0}} [DecidableEq p.A] {A B : Type}
    {left right : Boundary C p A B} {program : A → FreeM p B}
    (h : left.PolyTranslatable right) (k : Nat) :
    IsRealizableWithin C left program k ↔
      IsRealizableWithin C right program k :=
  isRealizableWithin_iff_of_boundary_polyTranslatable h k

end PFunctor.RealizabilityRepresentationExamples
