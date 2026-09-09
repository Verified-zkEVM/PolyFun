/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Realizability.Quantitative
public import ToCslib.Computability.PolyTime

/-!
# Cslib's single-tape backend for quantitative PolyFun realizability

This module is the narrow adapter between the generic quantitative layer and
cslib. Objects are represented by raw Boolean-string encodings. Quantitative
realizers are `EncPolyTime` witnesses, and their backend-relative work charge is
the witness's certified time polynomial evaluated at the encoded input length.

The qualitative step class intentionally accepts every semantic function: its
purpose is to carry concrete encodings into the generic boundary and trace API.
The quantitative realizer remains the load-bearing executable evidence.
-/

public section

universe u

namespace PFunctor.CslibBackend

open ToCslib.Computability

/-- Raw Boolean-string representations with unconstrained qualitative
admissibility. Concrete quantitative morphisms still require cslib code.

This definition is reducibly exposed so that `encodingStepClass.Str type`
elaborates as the function type `type → List Bool` across module boundaries. -/
@[expose, reducible] def encodingStepClass : StepClass.{u, u} where
  Str type := type → List Bool
  Hom _ _ _ := True
  id_mem _ := trivial
  comp_mem _ _ := trivial

@[instance_reducible] instance instHasProd : encodingStepClass.HasProd where
  prod left right value := left value.1 ++ right value.2
  fst_mem _ _ := trivial
  snd_mem _ _ := trivial
  pair_mem _ _ := trivial

@[simp] theorem prod_apply {A B : Type u} (left : A → List Bool)
    (right : B → List Bool) (value : A × B) :
    instHasProd.prod left right value = left value.1 ++ right value.2 := rfl

@[instance_reducible] instance instHasSum : encodingStepClass.HasSum where
  sum left right := Sum.elim (fun value ↦ false :: left value)
    (fun value ↦ true :: right value)
  inl_mem _ _ := trivial
  inr_mem _ _ := trivial
  elim_mem _ _ := trivial

@[simp] theorem sum_inl {A B : Type u} (left : A → List Bool)
    (right : B → List Bool) (value : A) :
    instHasSum.sum left right (Sum.inl value) = false :: left value := rfl

@[simp] theorem sum_inr {A B : Type u} (left : A → List Bool)
    (right : B → List Bool) (value : B) :
    instHasSum.sum left right (Sum.inr value) = true :: right value := rfl

@[instance_reducible] instance instHasOption : encodingStepClass.HasOption where
  option encoding
    | none => [false]
    | some value => true :: encoding value
  omap_mem _ := trivial
  none_mem _ _ := trivial
  obindCtx_mem _ := trivial
  some_mem _ := trivial

@[simp] theorem option_none {A : Type u} (encoding : A → List Bool) :
    instHasOption.option encoding none = [false] := rfl

@[simp] theorem option_some {A : Type u} (encoding : A → List Bool) (value : A) :
    instHasOption.option encoding (some value) = true :: encoding value := rfl

instance : encodingStepClass.IsDistributive where
  distrib_mem _ _ _ := trivial

/-- Cslib single-tape code as a concrete quantitative backend. The work charge
is a certified operational upper envelope, not an exact step counter.

This definition is reducibly exposed so that its generic `Realizer` family
elaborates as `EncPolyTime`; the named size and cost laws below remain the proof
API. -/
@[expose, reducible] noncomputable def quantitative : QuantitativeStepClass encodingStepClass where
  Realizer source target function := EncPolyTime source target function
  size representation value := (representation value).length
  cost := @fun _ _ source _ _ code input ↦
    code.time.eval (source input).length
  admissible _ := trivial

noncomputable instance : quantitative.HasCategory where
  identity representation := EncPolyTime.id representation
  compose first second := first.comp second
  composeOverhead := @fun _ _ _ source _ _ _ _ first second input ↦
    second.time.eval
      (1 + (source input).length + first.time.eval (source input).length)
  cost_compose_le := @fun _ _ _ source target _ function _ first second input ↦ by
    change (first.comp second).time.eval (source input).length ≤
      first.time.eval (source input).length +
        second.time.eval (target (function input)).length +
        second.time.eval
          (1 + (source input).length + first.time.eval (source input).length)
    rw [EncPolyTime.comp_time_eval]
    omega

@[simp] theorem size_eq_length {type : Type u} (representation : type → List Bool)
    (value : type) : quantitative.size representation value = (representation value).length :=
  rfl

@[simp] theorem cost_eq_time_envelope {source target : Type u}
    {sourceEncoding : source → List Bool} {targetEncoding : target → List Bool}
    {function : source → target}
    (code : EncPolyTime sourceEncoding targetEncoding function) (input : source) :
    quantitative.cost code input = code.time.eval (sourceEncoding input).length :=
  rfl

end PFunctor.CslibBackend
