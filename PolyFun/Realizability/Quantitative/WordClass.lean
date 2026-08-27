/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Instances
public import PolyFun.Realizability.Quantitative

/-!
# Quantitative word classes

`StepClass.WordClass` is the qualitative adapter from a conventional class of word functions to
PolyFun realizability. This file supplies its quantitative counterpart. A backend provides
Type-valued code for its admitted word functions, a word-size measure, and code cost. Optional
category mixins add identity and composition with a sound cost bound or an exact equation.
`QuantitativeWordClass.toQuantitativeStepClass` lifts the core data through every injective
representation used by `WordClass.toStepClass`; separate adapters lift the category mixins.

Keeping the executable witness in `Type` is essential. A proof-irrelevant assertion that some
word function is polynomial-time does not retain a program whose run can be charged. Conversely,
this adapter does not call an arbitrary cost annotation "time": a concrete backend still owes an
adequacy theorem relating its `Code` and `cost` to a standard operational model.
-/

@[expose] public section

universe u v

namespace PFunctor
namespace StepClass

variable {W : Type u}

/-- Executable and costed evidence refining a qualitative word-function class.

The semantic function remains an index of `Code`, so every code is correct by construction. The
`code_mem` field forgets executable evidence to the qualitative class. Category structure is kept
separate so a backend can expose costed code before certifying closure under wiring. -/
structure QuantitativeWordClass (V : WordClass W) where
  /-- Type-valued code for an admitted word function. -/
  Code : (W → W) → Type v
  /-- Every code denotes a function admitted by the qualitative word class. -/
  code_mem : ∀ {f : W → W}, Code f → V.Mem f
  /-- Encoded size of a word. -/
  size : W → ℕ
  /-- Exact backend-relative cost of running code on one word. -/
  cost : ∀ {f : W → W}, Code f → W → ℕ

namespace QuantitativeWordClass

variable {V : WordClass W} (Q : QuantitativeWordClass.{u, v} V)

/-- Executable identity and composition for quantitative word code. -/
class HasCategory where
  /-- Code for the identity word function. -/
  identity : Q.Code id
  /-- Sequential composition of word-function code. -/
  compose : ∀ {f g : W → W}, Q.Code f → Q.Code g → Q.Code (g ∘ f)
  /-- Work used to connect two sequential pieces of code. -/
  composeOverhead : ∀ {f g : W → W}, Q.Code f → Q.Code g → W → ℕ
  /-- Sound upper bound for sequentially composed word-function code. -/
  cost_compose_le : ∀ {f g : W → W} (first : Q.Code f) (second : Q.Code g) (word : W),
    Q.cost (compose first second) word ≤
      Q.cost first word + Q.cost second (f word) + composeOverhead first second word

/-- Optional exact-cost refinement of a quantitative word category. -/
class HasExactCategory [Q.HasCategory] : Prop where
  /-- Exact cost equation for sequentially composed word-function code. -/
  cost_compose_eq : ∀ {f g : W → W} (first : Q.Code f) (second : Q.Code g) (word : W),
    Q.cost (HasCategory.compose first second) word =
      Q.cost first word + Q.cost second (f word) +
        HasCategory.composeOverhead first second word

/-- Exact word-category data in one migration-friendly bundle. -/
structure ExactCategory where
  /-- Code for the identity word function. -/
  identity : Q.Code id
  /-- Sequential composition of word-function code. -/
  compose : ∀ {f g : W → W}, Q.Code f → Q.Code g → Q.Code (g ∘ f)
  /-- Exact work used to connect two sequential pieces of code. -/
  composeOverhead : ∀ {f g : W → W}, Q.Code f → Q.Code g → W → ℕ
  /-- Exact cost equation for sequentially composed word-function code. -/
  cost_compose_eq : ∀ {f g : W → W} (first : Q.Code f) (second : Q.Code g) (word : W),
    Q.cost (compose first second) word =
      Q.cost first word + Q.cost second (f word) + composeOverhead first second word

namespace ExactCategory

variable {Q}

/-- Forget exact word-category data to a sound upper-bound category. -/
@[instance_reducible]
def toHasCategory (category : Q.ExactCategory) : Q.HasCategory where
  identity := category.identity
  compose := category.compose
  composeOverhead := category.composeOverhead
  cost_compose_le first second word := Nat.le_of_eq (category.cost_compose_eq first second word)

/-- Recover the optional exact refinement for the category obtained from exact data. -/
theorem toHasExactCategory (category : Q.ExactCategory) :
    letI := category.toHasCategory
    Q.HasExactCategory := by
  let _ := category.toHasCategory
  exact ⟨category.cost_compose_eq⟩

end ExactCategory

/-- Identity word code selected by a category instance. -/
def identity [Q.HasCategory] : Q.Code id := HasCategory.identity

/-- Sequential composition selected by a word-category instance. -/
def compose [Q.HasCategory] {f g : W → W}
    (first : Q.Code f) (second : Q.Code g) : Q.Code (g ∘ f) :=
  HasCategory.compose first second

/-- Connection overhead selected by a word-category instance. -/
def composeOverhead [Q.HasCategory] {f g : W → W}
    (first : Q.Code f) (second : Q.Code g) (word : W) : ℕ :=
  HasCategory.composeOverhead first second word

/-- Word-level code realizing a function between two pinned injective representations. -/
structure Realizer {A B : Type u} (a : V.toStepClass.Str A)
    (b : V.toStepClass.Str B) (f : A → B) where
  /-- The total word function executed by the backend. -/
  function : W → W
  /-- Executable evidence for the word function. -/
  code : Q.Code function
  /-- The word function commutes with the pinned source and target encodings. -/
  realizes : ∀ input, function (a.1 input) = b.1 (f input)

namespace Realizer

variable {Q} {A B : Type u} {a : V.toStepClass.Str A}
  {b : V.toStepClass.Str B} {f : A → B}

/-- Forget executable evidence, retaining membership in the qualitative word class. -/
theorem toHom (code : Realizer Q a b f) : V.toStepClass.Hom a b f :=
  ⟨code.function, Q.code_mem code.code, code.realizes⟩

end Realizer

/-- Lift a quantitative word-function backend through the representations of its word class. -/
def toQuantitativeStepClass : QuantitativeStepClass.{u, u, max u v} V.toStepClass where
  Realizer := fun a b f ↦ Realizer Q a b f
  size := fun rep value ↦ Q.size (rep.1 value)
  cost := @fun _ _ a _ _ code input ↦ Q.cost code.code (a.1 input)
  admissible := fun code ↦ Realizer.toHom code

/-- Lift executable word-category wiring through injective representations. -/
@[instance_reducible]
def toHasCategory [Q.HasCategory] : Q.toQuantitativeStepClass.HasCategory where
  identity := fun _ ↦ ⟨id, Q.identity, fun _ ↦ rfl⟩
  compose := fun first second ↦
    ⟨second.function ∘ first.function, Q.compose first.code second.code, fun input ↦ by
      simp only [Function.comp_apply, first.realizes, second.realizes]⟩
  composeOverhead := @fun _ _ _ a _ _ _ _ first second input ↦
    Q.composeOverhead first.code second.code (a.1 input)
  cost_compose_le := @fun _ _ _ a _ _ _ _ first second input ↦ by
    change Q.cost (Q.compose first.code second.code) _ ≤
      Q.cost first.code _ + Q.cost second.code _ + Q.composeOverhead first.code second.code _
    have h := HasCategory.cost_compose_le first.code second.code (a.1 input)
    rw [first.realizes input] at h
    exact h

/-- Lift an exact word-category equation through injective representations.

The target category instance is explicit so the proof cannot accidentally refine unrelated
composition code installed for the lifted quantitative step class. -/
theorem toHasExactCategory [Q.HasCategory] [Q.HasExactCategory] :
    letI := Q.toHasCategory
    Q.toQuantitativeStepClass.HasExactCategory := by
  let _ := Q.toHasCategory
  refine { cost_compose_eq := ?_ }
  intro A B D a b d f g first second input
  change Q.cost (Q.compose first.code second.code) _ =
    Q.cost first.code _ + Q.cost second.code _ + Q.composeOverhead first.code second.code _
  have h := HasExactCategory.cost_compose_eq first.code second.code (a.1 input)
  rw [first.realizes input] at h
  exact h

@[simp]
theorem toQuantitativeStepClass_size {A : Type u} (rep : V.toStepClass.Str A) (value : A) :
    (@toQuantitativeStepClass W V Q).size rep value = Q.size (rep.1 value) :=
  rfl

@[simp]
theorem toQuantitativeStepClass_cost {A B : Type u} {a : V.toStepClass.Str A}
    {b : V.toStepClass.Str B} {f : A → B} (code : Realizer Q a b f) (input : A) :
    (@toQuantitativeStepClass W V Q).cost code input = Q.cost code.code (a.1 input) :=
  rfl

end QuantitativeWordClass

end StepClass
end PFunctor
