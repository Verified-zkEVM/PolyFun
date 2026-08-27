/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.WordClass

/-!
# Quantitative word-class checks

Compile-time checks for the generic adapter from word-level executable code to quantitative
realizability.
-/

public section

universe u v

namespace PFunctor.StepClass.QuantitativeWordClassTest

variable {W : Type u} {V : WordClass W} (Q : QuantitativeWordClass.{u, v} V)

#check Q.toQuantitativeStepClass
#check QuantitativeWordClass.HasCategory
#check QuantitativeWordClass.HasExactCategory
#check QuantitativeWordClass.toHasCategory
#check QuantitativeWordClass.toHasExactCategory

section Category

variable [Q.HasCategory] [Q.HasExactCategory]

#check Q.identity
#check Q.compose
#check Q.composeOverhead
#check Q.toHasCategory
#check Q.toHasExactCategory

end Category

example {A B : Type u} {a : V.toStepClass.Str A} {b : V.toStepClass.Str B}
    {f : A → B} (code : QuantitativeWordClass.Realizer Q a b f) :
    V.toStepClass.Hom a b f :=
  code.toHom

/-! ## Executable nonconstant backend canary -/

/-- A small word syntax with disjoint sum tags and an injective pairing constructor. -/
inductive TestWord where
  | atom : Nat → TestWord
  | pair : TestWord → TestWord → TestWord
  | left : TestWord → TestWord
  | right : TestWord → TestWord
deriving DecidableEq

namespace TestWord

/-- A nonconstant encoded-size function. -/
@[expose]
def size : TestWord → Nat
  | .atom value => value + 1
  | .pair first second => first.size + second.size + 1
  | .left value => value.size + 1
  | .right value => value.size + 1

end TestWord

/-- Pairing data for the unrestricted test word class. -/
def testPairing : WordPairing (fun _ : TestWord → TestWord ↦ True) where
  pair := .pair
  pair_inj _ _ _ _ h := by cases h; exact ⟨rfl, rfl⟩
  fst
    | .pair left _ => left
    | other => other
  snd
    | .pair _ right => right
    | other => other
  fst_mem := True.intro
  snd_mem := True.intro
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl
  pair_mem _ _ := True.intro

/-- Sum-tagging data for the unrestricted test word class. -/
def testTagging : WordTagging (fun _ : TestWord → TestWord ↦ True) where
  inl := .left
  inr := .right
  inl_mem := True.intro
  inr_mem := True.intro
  inl_inj _ _ h := by cases h; rfl
  inr_inj _ _ h := by cases h; rfl
  inl_ne_inr _ _ h := by cases h
  elim f g
    | .left value => f value
    | .right value => g value
    | other => other
  elim_mem _ _ := True.intro
  elim_inl _ _ _ := rfl
  elim_inr _ _ _ := rfl
  pt := .atom 0
  const_mem := True.intro

/-- Tag-past-pairing rearrangement for the test word syntax. -/
def testDistrib : WordDistrib (fun _ : TestWord → TestWord ↦ True)
    testPairing testTagging where
  distrib
    | .pair (.left value) context => .left (.pair value context)
    | .pair (.right value) context => .right (.pair value context)
    | other => other
  distrib_mem := True.intro
  distrib_inl _ _ := rfl
  distrib_inr _ _ := rfl

/-- Unrestricted qualitative word class used to test the quantitative adapter itself. -/
@[expose]
def testWordClass : WordClass TestWord where
  Mem _ := True
  id_mem := True.intro
  comp_mem _ _ := True.intro
  pairing := testPairing
  tagging := testTagging
  distributor := testDistrib

/-- Test code stores an input-dependent cost while its semantic function remains in the index. -/
structure TestCode (_ : TestWord → TestWord) where
  runCost : TestWord → Nat

/-- A word backend with nonconstant size and input-dependent execution cost. -/
@[expose]
def testQuantitativeWordClass : QuantitativeWordClass testWordClass where
  Code := TestCode
  code_mem _ := True.intro
  size := TestWord.size
  cost code := code.runCost

@[instance_reducible]
def testCategory : testQuantitativeWordClass.HasCategory where
  identity := TestCode.mk fun _ ↦ 0
  compose := fun {f} {_} first second =>
    TestCode.mk fun word ↦ first.runCost word + second.runCost (f word) + 1
  composeOverhead _ _ _ := 1
  cost_compose_le _ _ _ := le_rfl

local instance : testQuantitativeWordClass.HasCategory := testCategory

theorem testExactCategory : testQuantitativeWordClass.HasExactCategory :=
  ⟨fun _ _ _ ↦ rfl⟩

local instance : testQuantitativeWordClass.HasExactCategory := testExactCategory

/-- Natural numbers represented by atom words. -/
@[expose]
def natRep : testWordClass.toStepClass.Str Nat :=
  ⟨TestWord.atom, fun _ _ h ↦ by cases h; rfl⟩

/-- Word implementation of successor, totalized outside the pinned representation. -/
@[expose]
def wordSucc : TestWord → TestWord
  | .atom value => .atom (value + 1)
  | other => other

/-- Word implementation of doubling, totalized outside the pinned representation. -/
@[expose]
def wordDouble : TestWord → TestWord
  | .atom value => .atom (2 * value)
  | other => other

/-- Successor code whose cost depends on the encoded input size. -/
@[expose]
def succRealizer : QuantitativeWordClass.Realizer testQuantitativeWordClass
    natRep natRep Nat.succ where
  function := wordSucc
  code := ⟨fun word ↦ word.size + 2⟩
  realizes _ := rfl

/-- Doubling code with a different input-dependent cost. -/
@[expose]
def doubleRealizer : QuantitativeWordClass.Realizer testQuantitativeWordClass
    natRep natRep (fun value ↦ 2 * value) where
  function := wordDouble
  code := ⟨fun word ↦ word.size + 4⟩
  realizes _ := rfl

/-- The lifted backend executes word-code composition in source-to-target order. -/
@[expose]
def composedRealizer : QuantitativeWordClass.Realizer testQuantitativeWordClass
    natRep natRep ((fun value ↦ 2 * value) ∘ Nat.succ) := by
  letI := testQuantitativeWordClass.toHasCategory
  exact testQuantitativeWordClass.toQuantitativeStepClass.compose succRealizer doubleRealizer

example : testQuantitativeWordClass.toQuantitativeStepClass.size natRep 4 = 5 := rfl

example : testQuantitativeWordClass.toQuantitativeStepClass.cost succRealizer 4 = 7 := rfl

example : composedRealizer.function (.atom 3) = .atom 8 := rfl

example : composedRealizer.realizes 3 = rfl := rfl

/-- Lifted composition charges the first code, the second code on the encoded intermediate
result, and the explicit connection overhead, rather than reversing the two functions. -/
example : testQuantitativeWordClass.toQuantitativeStepClass.cost composedRealizer 3 = 16 := rfl

end PFunctor.StepClass.QuantitativeWordClassTest
