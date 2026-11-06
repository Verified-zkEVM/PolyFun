/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Samuel Schlesinger
-/

module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
public import PolyFun.Realizability.StepClass

/-!
# Polynomial time as a PolyFun step class

`PolyFunComplexitylib.polyTimeStepClass` represents a type by an injective encoding into bit
strings and admits exactly the maps that complexitylib's tidy multi-tape machines compute in
polynomial time and space (`Turing.MultiTapeTM.ComputableTidilyInPolyTime`). Identity and
composition are complexitylib's closure lemmas.

Products use complexitylib's framed pairing and are available at every universe. complexitylib
states its sum and option lemmas for `Type`, so the sum and option mixins are provided at
universe `0`. Elimination of sums is `ComputableTidilyInPolyTime.sumElim`, whose proof is
complexitylib's private `sumElim` lemma from `Problems/ThreeSAT.lean`.

## Main definitions

* `PolyFunComplexitylib.polyTimeStepClass`: polynomial-time admissibility.
* Instances `HasProd` (every universe), `HasSum` and `HasOption` (universe `0`).
-/

@[expose] public section

universe u

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α β γ : Type} {left : α ↪ List Bool} {right : β ↪ List Bool} {encC : γ ↪ List Bool}

/-- Case analysis on a tagged sum, from polynomial-time branches. -/
theorem sumElim {f : α → γ} {g : β → γ} (hf : ComputableTidilyInPolyTime f left encC)
    (hg : ComputableTidilyInPolyTime g right encC) :
    ComputableTidilyInPolyTime (Sum.elim f g) (encSum left right) encC := by
  let encS := encSum left right
  have hc : ComputableTidilyInPolyTime Sum.isRight encS encBool :=
    ((headD (encA := encBool) false).comp (encode encS)).of_enc_eq fun x => by cases x <;> rfl
  let encR := (Function.Embedding.subtype (Sum.isRight · = true)).trans encS
  let unRight : {x : α ⊕ β // x.isRight = true} → β
    | ⟨.inr b, _⟩ => b
    | ⟨.inl _, h⟩ => by cases h
  have hunRight : ComputableTidilyInPolyTime unRight encR right :=
    (bitsTail.comp (encode encR)).of_enc_eq fun x => by
      rcases x with ⟨a | b, h⟩
      · cases h
      · rfl
  let encL := (Function.Embedding.subtype (Sum.isRight · = false)).trans encS
  let unLeft : {x : α ⊕ β // x.isRight = false} → α
    | ⟨.inl a, _⟩ => a
    | ⟨.inr _, h⟩ => by cases h
  have hunLeft : ComputableTidilyInPolyTime unLeft encL left :=
    (bitsTail.comp (encode encL)).of_enc_eq fun x => by
      rcases x with ⟨a | b, h⟩
      · rfl
      · cases h
  have hR : ComputableTidilyInPolyTime (Sum.elim f g ∘ Subtype.val) encR encC := by
    convert hg.comp hunRight using 1
    funext x
    rcases x with ⟨a | b, hx⟩
    · cases hx
    · rfl
  have hL : ComputableTidilyInPolyTime (Sum.elim f g ∘ Subtype.val) encL encC := by
    convert hf.comp hunLeft using 1
    funext x
    rcases x with ⟨a | b, hx⟩
    · rfl
    · cases hx
  convert hc.ite hR hL using 1
  funext x
  cases x <;> rfl

/-- Case analysis on a tagged sum that also retains a context, from polynomial-time branches. -/
theorem sumElimCtx {ι : Type} {encI : ι ↪ List Bool} {f : α × ι → γ} {g : β × ι → γ}
    (hf : ComputableTidilyInPolyTime f (encPair left encI) encC)
    (hg : ComputableTidilyInPolyTime g (encPair right encI) encC) :
    ComputableTidilyInPolyTime
      (fun x : (α ⊕ β) × ι => Sum.elim (fun l => f (l, x.2)) (fun r => g (r, x.2)) x.1)
      (encPair (encSum left right) encI) encC := by
  let encS := encSum left right
  let encX := encPair encS encI
  have hcS : ComputableTidilyInPolyTime Sum.isRight encS encBool :=
    ((headD (encA := encBool) false).comp (encode encS)).of_enc_eq fun x => by cases x <;> rfl
  have hc : ComputableTidilyInPolyTime (fun x : (α ⊕ β) × ι => x.1.isRight) encX encBool :=
    hcS.comp (fst encS encI)
  let encR := (Function.Embedding.subtype fun x : (α ⊕ β) × ι => x.1.isRight = true).trans encX
  let unRight : {x : (α ⊕ β) × ι // x.1.isRight = true} → β
    | ⟨(.inr b, _), _⟩ => b
    | ⟨(.inl _, _), h⟩ => by cases h
  let encRS := (Function.Embedding.subtype fun s : α ⊕ β => s.isRight = true).trans encS
  have hsumR : ComputableTidilyInPolyTime
      (fun x : {x : (α ⊕ β) × ι // x.1.isRight = true} => (⟨x.1.1, x.2⟩ :
        {s : α ⊕ β // s.isRight = true})) encR encRS :=
    ((fst encS encI).restrict _).of_enc_eq fun _ => rfl
  have hunRight : ComputableTidilyInPolyTime unRight encR right :=
    ((bitsTail.comp (encode encRS)).comp hsumR).of_enc_eq fun x => by
      rcases x with ⟨⟨a | b, i⟩, h⟩
      · cases h
      · rfl
  let encL := (Function.Embedding.subtype fun x : (α ⊕ β) × ι => x.1.isRight = false).trans encX
  let unLeft : {x : (α ⊕ β) × ι // x.1.isRight = false} → α
    | ⟨(.inl a, _), _⟩ => a
    | ⟨(.inr _, _), h⟩ => by cases h
  let encLS := (Function.Embedding.subtype fun s : α ⊕ β => s.isRight = false).trans encS
  have hsumL : ComputableTidilyInPolyTime
      (fun x : {x : (α ⊕ β) × ι // x.1.isRight = false} => (⟨x.1.1, x.2⟩ :
        {s : α ⊕ β // s.isRight = false})) encL encLS :=
    ((fst encS encI).restrict _).of_enc_eq fun _ => rfl
  have hunLeft : ComputableTidilyInPolyTime unLeft encL left :=
    ((bitsTail.comp (encode encLS)).comp hsumL).of_enc_eq fun x => by
      rcases x with ⟨⟨a | b, i⟩, h⟩
      · rfl
      · cases h
  have hR : ComputableTidilyInPolyTime
      ((fun x : (α ⊕ β) × ι => Sum.elim (fun l => f (l, x.2)) (fun r => g (r, x.2)) x.1) ∘
        Subtype.val) encR encC := by
    convert hg.comp (hunRight.prod ((snd encS encI).restrict _)) using 1
    funext x
    rcases x with ⟨⟨a | b, i⟩, hx⟩
    · cases hx
    · rfl
  have hL : ComputableTidilyInPolyTime
      ((fun x : (α ⊕ β) × ι => Sum.elim (fun l => f (l, x.2)) (fun r => g (r, x.2)) x.1) ∘
        Subtype.val) encL encC := by
    convert hf.comp (hunLeft.prod ((snd encS encI).restrict _)) using 1
    funext x
    rcases x with ⟨⟨a | b, i⟩, hx⟩
    · rfl
    · cases hx
  convert hc.ite hR hL using 1
  funext x
  rcases x with ⟨a | b, i⟩ <;> rfl

/-- Mapping an optional value, from a polynomial-time map of its payload. -/
theorem optionMap {f : α → β} (hf : ComputableTidilyInPolyTime f left right) :
    ComputableTidilyInPolyTime (Option.map f) (encOption left) (encOption right) := by
  have h := optionElimWithInput (encA := encOption left) (encB := left) (encC := encOption right)
    (value := id) (fallback := fun _ => none) (body := fun _ a => some (f a)) id'
    (const none) ((optionSome right).comp (hf.comp (snd (encOption left) left)))
  convert h using 1
  funext o
  cases o <;> rfl

/-- Binding an optional value against a polynomial-time continuation that also reads a retained
context. -/
theorem optionBindCtx {ε : Type} {encE : ε ↪ List Bool} {k : α × ε → Option β}
    (hk : ComputableTidilyInPolyTime k (encPair left encE) (encOption right)) :
    ComputableTidilyInPolyTime (fun y : Option α × ε => y.1.bind fun j => k (j, y.2))
      (encPair (encOption left) encE) (encOption right) := by
  have h := optionElimWithInput (encA := encPair (encOption left) encE) (encB := left)
    (encC := encOption right) (value := Prod.fst) (fallback := fun _ => none)
    (body := fun y j => k (j, y.2)) (fst (encOption left) encE) (const none)
    (hk.comp ((snd _ left).prod ((snd (encOption left) encE).comp (fst _ left))))
  convert h using 1
  funext y
  rcases y with ⟨_ | j, e⟩ <;> rfl

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace PolyFunComplexitylib

open PFunctor Turing.MultiTapeTM

/-- Polynomial-time tidy computability as a PolyFun step class: types carry an injective encoding
into bit strings, and admissible maps are tidily computable in polynomial time and space.

It is reducible so that `polyTimeStepClass.Str A` elaborates as the embedding type `A ↪ List Bool`
across module boundaries. -/
abbrev polyTimeStepClass : StepClass.{u, u} where
  Str A := A ↪ List Bool
  Hom ea eb f := ComputableTidilyInPolyTime f ea eb
  id_mem _ := ComputableTidilyInPolyTime.id'
  comp_mem hf hg := hg.comp hf

/-- Products use complexitylib's framed pairing. -/
instance : polyTimeStepClass.{u}.HasProd where
  prod a b := encPair a b
  fst_mem a b := ComputableTidilyInPolyTime.fst a b
  snd_mem a b := ComputableTidilyInPolyTime.snd a b
  pair_mem hf hg := hf.prod hg

/-- Sums use complexitylib's tagged encoding, at universe `0`. -/
instance : polyTimeStepClass.{0}.HasSum where
  sum a b := encSum a b
  inl_mem a b := ComputableTidilyInPolyTime.sumInl a b
  inr_mem a b := ComputableTidilyInPolyTime.sumInr a b
  elim_mem hf hg := ComputableTidilyInPolyTime.sumElim hf hg

/-- Products distribute over sums: case analysis may retain a context. -/
instance : polyTimeStepClass.{0}.IsDistributive where
  distrib_mem a b i := ComputableTidilyInPolyTime.sumElimCtx
    (ComputableTidilyInPolyTime.sumInl (encPair a i) (encPair b i))
    (ComputableTidilyInPolyTime.sumInr (encPair a i) (encPair b i))

/-- Optional values use complexitylib's option encoding, at universe `0`. -/
instance : polyTimeStepClass.{0}.HasOption where
  option a := encOption a
  omap_mem hf := ComputableTidilyInPolyTime.optionMap hf
  none_mem _ _ := ComputableTidilyInPolyTime.const none
  obindCtx_mem hk := ComputableTidilyInPolyTime.optionBindCtx hk
  some_mem a := ComputableTidilyInPolyTime.optionSome a

end PolyFunComplexitylib
