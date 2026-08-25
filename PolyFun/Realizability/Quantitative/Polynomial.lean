/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Finset.Sort
public import PolyFun.Complexity.SecondOrderPolynomial
public import PolyFun.Realizability.Quantitative.Closure

/-!
# Polynomially bounded quantitative realizers

This module packages first-order polynomial work and output-size certificates around the
executable evidence of `QuantitativeStepClass`. The bounds remain relative to a pinned backend
and pinned representations; no unqualified complexity class is defined here.

`PolynomialCategory` records polynomial bounds for identity wiring and composition overhead.
It turns `PolyRealizer`s into a category without assuming that code composition is free.
`StructuralKernel` and `PolynomialStructuralClosure` are explicit values rather than global
instances. They pin the qualitative and executable structural choices and package polynomially
bounded product, sum, optional-value, and distributivity operations together with bidirectional
encoding-size laws.
-/

@[expose] public section

universe u v w

namespace Complexity

/-- An ordinary natural-number polynomial, represented as a second-order polynomial with no
oracle-length symbols. -/
abbrev FirstOrderPolynomial := SecondOrderPolynomial PEmpty.{1}

namespace FirstOrderPolynomial

/-- Evaluate a first-order polynomial at one input size. -/
def eval (polynomial : FirstOrderPolynomial) (inputSize : ℕ) : ℕ :=
  SecondOrderPolynomial.eval PEmpty.elim inputSize polynomial

/-- A constant first-order polynomial. -/
def const (value : ℕ) : FirstOrderPolynomial := SecondOrderPolynomial.const value

/-- The input-size polynomial. -/
def input : FirstOrderPolynomial := SecondOrderPolynomial.input

/-- Addition of first-order polynomials. -/
def add (left right : FirstOrderPolynomial) : FirstOrderPolynomial :=
  SecondOrderPolynomial.add left right

/-- Multiplication of first-order polynomials. -/
def mul (left right : FirstOrderPolynomial) : FirstOrderPolynomial :=
  SecondOrderPolynomial.mul left right

/-- Substitute `inner` for the input variable of `outer`. -/
def comp (outer inner : FirstOrderPolynomial) : FirstOrderPolynomial :=
  SecondOrderPolynomial.comp outer inner

/-- A natural power of a first-order polynomial. -/
def pow (polynomial : FirstOrderPolynomial) : ℕ → FirstOrderPolynomial
  | 0 => const 1
  | exponent + 1 => mul (pow polynomial exponent) polynomial

/-- Translate a Mathlib polynomial with natural coefficients into first-order polynomial syntax.

The finite support is sorted to choose a deterministic syntax tree; evaluation is independent of
that presentation. -/
def ofNatPolynomial (polynomial : Polynomial ℕ) : FirstOrderPolynomial :=
  polynomial.support.sort.foldr (fun exponent rest ↦
    add (mul (const (polynomial.coeff exponent)) (pow input exponent)) rest) (const 0)

@[simp] theorem eval_const (value inputSize : ℕ) : (const value).eval inputSize = value := rfl

@[simp] theorem eval_input (inputSize : ℕ) : input.eval inputSize = inputSize := rfl

@[simp] theorem eval_add (left right : FirstOrderPolynomial) (inputSize : ℕ) :
    (add left right).eval inputSize = left.eval inputSize + right.eval inputSize :=
  rfl

@[simp] theorem eval_mul (left right : FirstOrderPolynomial) (inputSize : ℕ) :
    (mul left right).eval inputSize = left.eval inputSize * right.eval inputSize :=
  rfl

@[simp] theorem eval_comp (outer inner : FirstOrderPolynomial) (inputSize : ℕ) :
    (comp outer inner).eval inputSize = outer.eval (inner.eval inputSize) :=
  SecondOrderPolynomial.eval_comp outer inner PEmpty.elim inputSize

@[simp] theorem eval_pow (polynomial : FirstOrderPolynomial) (exponent inputSize : ℕ) :
    (pow polynomial exponent).eval inputSize = polynomial.eval inputSize ^ exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih => simp [pow, ih, Nat.pow_succ]

@[simp] theorem eval_ofNatPolynomial (polynomial : Polynomial ℕ) (inputSize : ℕ) :
    (ofNatPolynomial polynomial).eval inputSize = polynomial.eval inputSize := by
  rw [Polynomial.eval_eq_sum]
  have hfold (exponents : List ℕ) :
      (exponents.foldr (fun exponent rest ↦
        add (mul (const (polynomial.coeff exponent)) (pow input exponent)) rest)
          (const 0)).eval inputSize =
        (exponents.map fun exponent ↦ polynomial.coeff exponent * inputSize ^ exponent).sum := by
    induction exponents with
    | nil => rfl
    | cons exponent exponents ih => simp [ih]
  rw [ofNatPolynomial, hfold]
  rw [← List.sum_toFinset _ (polynomial.support.sort_nodup (fun a b ↦ a ≤ b))]
  simp [Polynomial.sum_def]

/-- Evaluation of a first-order polynomial is monotone in its input size. -/
theorem eval_monotone (polynomial : FirstOrderPolynomial) : Monotone polynomial.eval :=
  SecondOrderPolynomial.eval_monotone polynomial fun interface ↦ interface.elim

end FirstOrderPolynomial

end Complexity

namespace PFunctor
namespace QuantitativeStepClass

open Complexity
open DynSystem.DynComputation

variable {C : StepClass.{u, v}} (Q : QuantitativeStepClass.{u, v, w} C)

/-! ## Polynomially bounded code -/

/-- Executable code together with first-order polynomial work and output-size certificates. -/
structure PolyRealizer {A B : Type u} (a : C.Str A) (b : C.Str B) (f : A → B) where
  /-- Executable evidence for the represented function. -/
  code : Q.Realizer a b f
  /-- Polynomial upper bound on backend work. -/
  work : FirstOrderPolynomial
  /-- Polynomial upper bound on encoded output size. -/
  outputSize : FirstOrderPolynomial
  /-- Backend work is bounded in the encoded input size. -/
  work_le : ∀ input, Q.cost code input ≤ work.eval (Q.size a input)
  /-- Encoded output size is bounded in the encoded input size. -/
  outputSize_le : ∀ input, Q.size b (f input) ≤ outputSize.eval (Q.size a input)

namespace PolyRealizer

variable {Q} {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
  {f : A → B} {g : B → D}

/-- Forget polynomial certificates, retaining executable quantitative code. -/
def toRealizer (realizer : Q.PolyRealizer a b f) : Q.Realizer a b f :=
  realizer.code

/-- Forget executable and quantitative data, retaining qualitative admissibility. -/
theorem toHom (realizer : Q.PolyRealizer a b f) : C.Hom a b f :=
  Q.admissible realizer.code

end PolyRealizer

/-! ## Polynomial category structure -/

/-- Polynomial bounds for the executable categorical wiring of a quantitative backend. -/
structure PolynomialCategory [Q.HasCategory] where
  /-- Work bound for identity code at each pinned representation. -/
  identityWork : ∀ {A : Type u}, C.Str A → FirstOrderPolynomial
  /-- Identity code obeys its selected work polynomial. -/
  cost_identity_le : ∀ {A : Type u} (a : C.Str A) (input : A),
    Q.cost (Q.identity a) input ≤ (identityWork a).eval (Q.size a input)
  /-- Work polynomial for connecting two concrete pieces of code. -/
  composeOverhead : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D},
    Q.Realizer a b f → Q.Realizer b d g → FirstOrderPolynomial
  /-- Backend connection overhead obeys the selected polynomial. -/
  composeOverhead_le : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B}
    {d : C.Str D} {f : A → B} {g : B → D}
    (first : Q.Realizer a b f) (second : Q.Realizer b d g) (input : A),
    Q.composeOverhead first second input ≤
      (composeOverhead first second).eval (Q.size a input)

namespace PolyRealizer

variable {Q}

/-- Polynomially bounded identity code. -/
def identity [Q.HasCategory] (category : Q.PolynomialCategory)
    {A : Type u} (a : C.Str A) : Q.PolyRealizer a a id where
  code := Q.identity a
  work := category.identityWork a
  outputSize := FirstOrderPolynomial.input
  work_le := category.cost_identity_le a
  outputSize_le := fun _ ↦ le_rfl

/-- Sequential composition of polynomially bounded code.

The work polynomial charges the first code, the second code at the first output-size bound, and
the backend's explicit connection overhead. -/
def comp [Q.HasCategory] (category : Q.PolynomialCategory)
    {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D}
    (first : Q.PolyRealizer a b f) (second : Q.PolyRealizer b d g) :
    Q.PolyRealizer a d (g ∘ f) where
  code := Q.compose first.code second.code
  work := FirstOrderPolynomial.add
    (FirstOrderPolynomial.add first.work
      (FirstOrderPolynomial.comp second.work first.outputSize))
    (category.composeOverhead first.code second.code)
  outputSize := FirstOrderPolynomial.comp second.outputSize first.outputSize
  work_le := fun input ↦ by
    have hsecond : Q.cost second.code (f input) ≤
        second.work.eval (first.outputSize.eval (Q.size a input)) :=
      (second.work_le (f input)).trans
        (second.work.eval_monotone (first.outputSize_le input))
    exact (Q.cost_comp_le first.code second.code input).trans (by
      simpa using Nat.add_le_add
        (Nat.add_le_add (first.work_le input) hsecond)
        (category.composeOverhead_le first.code second.code input))
  outputSize_le := fun input ↦ by
    simpa using (second.outputSize_le (f input)).trans
      (second.outputSize.eval_monotone (first.outputSize_le input))

end PolyRealizer

/-! ## Polynomial output-size recovery -/

/-- A polynomial certificate for recovering a returned payload's encoded size from the encoded
size of its tagged readout.

This is intentionally boundary-local: it requires no global polynomial model and does not add a
separate output-size field to `ExecutionCost`. -/
structure PolyOutputSizeRecovery [C.HasSum] {p : PFunctor.{u, u}} {A B : Type u}
    (bd : Boundary C p A B) where
  /-- First-order polynomial bounding the returned payload size. -/
  polynomial : FirstOrderPolynomial
  /-- Every returned payload obeys the polynomial recovery bound. -/
  output_le : ∀ value : B,
    Q.size bd.out value ≤ polynomial.eval (Q.size bd.head (Sum.inl value))

namespace PolyOutputSizeRecovery

variable {Q} [C.HasSum] {p : PFunctor.{u, u}} {A B : Type u}
  {bd : Boundary C p A B}

/-- Forget that an output-size recovery function is represented by a first-order polynomial. -/
def toOutputSizeRecovery (recovery : Q.PolyOutputSizeRecovery bd) :
    QuantitativeRealization.OutputSizeRecovery (Q := Q) (bd := bd) where
  recover := recovery.polynomial.eval
  monotone := recovery.polynomial.eval_monotone
  output_le := recovery.output_le

end PolyOutputSizeRecovery

/-! ## Explicit structural choices -/

/-- Pinned qualitative and executable structural operations for one backend.

This is an ordinary structure, not a typeclass. Clients install its fields with local `letI`s
only around code that uses the lower-level closure API. -/
structure StructuralKernel where
  /-- Pinned qualitative product representation. -/
  cProd : C.HasProd
  /-- Pinned qualitative sum representation. -/
  cSum : C.HasSum
  /-- Pinned qualitative optional-value representation. -/
  cOption : @StepClass.HasOption C cProd
  /-- Pinned qualitative distributivity law. -/
  cDistributive : @StepClass.IsDistributive C cProd cSum
  /-- Executable product operations. -/
  qProd : @QuantitativeStepClass.HasProd C Q cProd
  /-- Executable sum operations. -/
  qSum : @QuantitativeStepClass.HasSum C Q cSum
  /-- Executable optional-value operations. -/
  qOption : @QuantitativeStepClass.HasOption C Q cProd cOption
  /-- Executable distributivity operation. -/
  qDistributive : @QuantitativeStepClass.IsDistributive C Q cProd cSum

/-- Polynomially bounded structural operations and bidirectional structural size laws.

The operation fields may select any correct backend realizers, but their semantic functions and
representations are fixed by `kernel`. The recovery size bounds prevent products, sums, or options
from hiding an exponentially larger payload behind a short outer encoding. -/
structure PolynomialStructuralClosure [Q.HasCategory] (kernel : Q.StructuralKernel) where
  /-- Polynomially bounded first projection. -/
  fst : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    Q.PolyRealizer (kernel.cProd.prod a b) a Prod.fst
  /-- Polynomially bounded second projection. -/
  snd : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    Q.PolyRealizer (kernel.cProd.prod a b) b Prod.snd
  /-- Polynomially bounded pairing from a common input. -/
  pair : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : A → D}, Q.PolyRealizer a b f → Q.PolyRealizer a d g →
      Q.PolyRealizer a (kernel.cProd.prod b d) fun input ↦ (f input, g input)
  /-- Polynomially bounded left injection. -/
  inl : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    Q.PolyRealizer a (kernel.cSum.sum a b) Sum.inl
  /-- Polynomially bounded right injection. -/
  inr : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    Q.PolyRealizer b (kernel.cSum.sum a b) Sum.inr
  /-- Polynomially bounded case analysis. -/
  elim : ∀ {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → D} {g : B → D}, Q.PolyRealizer a d f → Q.PolyRealizer b d g →
      Q.PolyRealizer (kernel.cSum.sum a b) d (Sum.elim f g)
  /-- Polynomially bounded mapping over optional values. -/
  optionMap : ∀ {A B : Type u} {a : C.Str A} {b : C.Str B} {f : A → B},
    Q.PolyRealizer a b f →
      Q.PolyRealizer (kernel.cOption.option a) (kernel.cOption.option b) (Option.map f)
  /-- Polynomially bounded absent optional value. -/
  optionNone : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B),
    Q.PolyRealizer a (kernel.cOption.option b) fun _ ↦ none
  /-- Polynomially bounded contextual optional bind. -/
  optionBindContext : ∀ {A B E : Type u} {a : C.Str A} {b : C.Str B}
    {e : C.Str E} {k : A × E → Option B},
    Q.PolyRealizer (kernel.cProd.prod a e) (kernel.cOption.option b) k →
      Q.PolyRealizer (kernel.cProd.prod (kernel.cOption.option a) e)
        (kernel.cOption.option b) fun input ↦ input.1.bind fun value ↦ k (value, input.2)
  /-- Polynomially bounded inverse distributivity used by contextual case analysis. -/
  distribute : ∀ {A B E : Type u} (a : C.Str A) (b : C.Str B) (e : C.Str E),
    Q.PolyRealizer (kernel.cProd.prod (kernel.cSum.sum a b) e)
      (kernel.cSum.sum (kernel.cProd.prod a e) (kernel.cProd.prod b e)) fun input ↦
        Sum.elim (fun left ↦ Sum.inl (left, input.2))
          (fun right ↦ Sum.inr (right, input.2)) input.1
  /-- Size polynomial for constructing a represented pair from the sum of component sizes. -/
  prodSize : ∀ {A B : Type u}, C.Str A → C.Str B → FirstOrderPolynomial
  /-- Represented pair size is polynomial in the two component sizes. -/
  size_prod_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (value : A × B),
    Q.size (kernel.cProd.prod a b) value ≤
      (prodSize a b).eval (Q.size a value.1 + Q.size b value.2)
  /-- Recovery polynomial for the left component of a represented pair. -/
  prodLeftSize : ∀ {A B : Type u}, C.Str A → C.Str B → FirstOrderPolynomial
  /-- The left component cannot hide behind a polynomially shorter pair encoding. -/
  size_prod_fst_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (value : A × B),
    Q.size a value.1 ≤ (prodLeftSize a b).eval (Q.size (kernel.cProd.prod a b) value)
  /-- Recovery polynomial for the right component of a represented pair. -/
  prodRightSize : ∀ {A B : Type u}, C.Str A → C.Str B → FirstOrderPolynomial
  /-- The right component cannot hide behind a polynomially shorter pair encoding. -/
  size_prod_snd_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (value : A × B),
    Q.size b value.2 ≤ (prodRightSize a b).eval (Q.size (kernel.cProd.prod a b) value)
  /-- Size polynomial for a left sum injection. -/
  sumLeftSize : ∀ {A B : Type u}, C.Str A → C.Str B → FirstOrderPolynomial
  /-- A left injection has polynomial encoding growth. -/
  size_sum_inl_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (value : A),
    Q.size (kernel.cSum.sum a b) (Sum.inl value) ≤
      (sumLeftSize a b).eval (Q.size a value)
  /-- Size polynomial for a right sum injection. -/
  sumRightSize : ∀ {A B : Type u}, C.Str A → C.Str B → FirstOrderPolynomial
  /-- A right injection has polynomial encoding growth. -/
  size_sum_inr_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (value : B),
    Q.size (kernel.cSum.sum a b) (Sum.inr value) ≤
      (sumRightSize a b).eval (Q.size b value)
  /-- Recovery polynomial for either payload of a represented sum. -/
  sumPayloadSize : ∀ {A B : Type u}, C.Str A → C.Str B → FirstOrderPolynomial
  /-- A left payload cannot hide behind a polynomially shorter sum encoding. -/
  size_sum_getLeft_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (value : A),
    Q.size a value ≤
      (sumPayloadSize a b).eval (Q.size (kernel.cSum.sum a b) (Sum.inl value))
  /-- A right payload cannot hide behind a polynomially shorter sum encoding. -/
  size_sum_getRight_le : ∀ {A B : Type u} (a : C.Str A) (b : C.Str B) (value : B),
    Q.size b value ≤
      (sumPayloadSize a b).eval (Q.size (kernel.cSum.sum a b) (Sum.inr value))
  /-- Size polynomial for an optional payload. -/
  optionSomeSize : ∀ {A : Type u}, C.Str A → FirstOrderPolynomial
  /-- A present optional value has polynomial encoding growth. -/
  size_option_some_le : ∀ {A : Type u} (a : C.Str A) (value : A),
    Q.size (kernel.cOption.option a) (some value) ≤
      (optionSomeSize a).eval (Q.size a value)
  /-- Recovery polynomial for an optional payload. -/
  optionPayloadSize : ∀ {A : Type u}, C.Str A → FirstOrderPolynomial
  /-- A present payload cannot hide behind a polynomially shorter option encoding. -/
  size_option_get_le : ∀ {A : Type u} (a : C.Str A) (value : A),
    Q.size a value ≤
      (optionPayloadSize a).eval (Q.size (kernel.cOption.option a) (some value))

namespace PolynomialStructuralClosure

variable {Q} [Q.HasCategory] {kernel : Q.StructuralKernel}

/-- Recover returned-value size from the tagged readout using the structural sum-payload
polynomial. -/
def polyOutputSizeRecovery (structural : Q.PolynomialStructuralClosure kernel)
    {p : PFunctor.{u, u}} {A B : Type u} (bd : Boundary C p A B) :
    @PolyOutputSizeRecovery C Q kernel.cSum p A B bd := by
  letI := kernel.cProd
  letI := kernel.cSum
  letI := kernel.cOption
  exact {
    polynomial := structural.sumPayloadSize bd.out bd.pos
    output_le := structural.size_sum_getLeft_le bd.out bd.pos }

end PolynomialStructuralClosure

/-- One explicit value collecting the categorical and structural polynomial interface.

The class-valued fields are data. This structure is not itself a typeclass, so two models for the
same backend can coexist without creating global instance ambiguity. -/
structure PolynomialModel where
  /-- Executable categorical wiring used by this model. -/
  category : Q.HasCategory
  /-- Pinned structural representation and executable choices. -/
  kernel : Q.StructuralKernel
  /-- Polynomial bounds for categorical wiring. -/
  polynomialCategory : @PolynomialCategory C Q category
  /-- Polynomially bounded structural operations and size laws. -/
  structural : @PolynomialStructuralClosure C Q category kernel

namespace PolynomialModel

variable {Q}

/-- Use the explicit model's polynomially bounded identity. -/
def identity (model : Q.PolynomialModel) {A : Type u} (a : C.Str A) :
    Q.PolyRealizer a a id := by
  letI := model.category
  exact PolyRealizer.identity model.polynomialCategory a

/-- Use the explicit model's polynomially bounded sequential composition. -/
def comp (model : Q.PolynomialModel)
    {A B D : Type u} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D}
    (first : Q.PolyRealizer a b f) (second : Q.PolyRealizer b d g) :
    Q.PolyRealizer a d (g ∘ f) := by
  letI := model.category
  exact first.comp model.polynomialCategory second

end PolynomialModel

end QuantitativeStepClass
end PFunctor
