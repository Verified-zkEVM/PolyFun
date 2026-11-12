/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Relator

/-!
# Semantic correspondence on represented inputs

An injective encoding identifies fully represented values inside an arbitrary
semantic carrier. That carrier may also contain errors, divergence, or partial
values. Correspondence on an explicit admissible set transfers total-correctness
contracts without choosing a source language, evaluator, or computation monad.

A language usually obtains a correspondence from three facts. Its fundamental lemma says that
the meaning preserves a relation to a native evaluator. Its representation says that encoded
inputs are related to native representatives and that a representative determines the encoded
output. Totality says that the evaluator returns the representative of the implementation's
result. `CorrespondsOn.of_liftFun` and `CertifiedMeaning.ofLiftFun` combine the three.

A meaning whose results at encoded inputs are all encoded outputs needs no native evaluator.
`CertifiedMeaning.ofDecode` certifies it, with the meaning read back by a left inverse of the
output encoding as its implementation.

Every relation here between a semantic value and a native value takes the semantic value first.
This matches the order of `meaning` and `implementation` and the fundamental lemmas of the
scoped layer. In particular, `RelationalContract` and `RelationalContract.iff_of_liftFun` take
their input and output relations as `D → A → Prop` and `E → B → Prop`.
-/

public section

namespace Control.Semantics

universe uA uB uC uD uE uF uW uW'

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {D : Type uD} {E : Type uE} {F : Type uF} {W : Type uW} {W' : Type uW'}

/-- Total correctness for every semantic representative of each admissible input.
Relations permit partial values and irrelevant components to have many representations. -/
@[expose] def RelationalContract (input : D → A → Prop) (output : E → B → Prop)
    (meaning : D → E) (pre : A → Prop) (post : A → B → Prop) : Prop :=
  ∀ x d, pre x → input d x → ∃ y, output (meaning d) y ∧ post x y

/-- A logical relation transfers contracts when represented outputs determine
a unique native result. Input representations need exist only on the precondition. -/
theorem RelationalContract.iff_of_liftFun
    {input : D → A → Prop} {output : E → B → Prop}
    {meaning : D → E} {implementation : A → B} (pre : A → Prop) (post : A → B → Prop)
    (h : Relator.LiftFun (fun d x => input d x ∧ pre x) output meaning implementation)
    (available : ∀ x, pre x → ∃ d, input d x) (unique : Relator.RightUnique output) :
    RelationalContract input output meaning pre post ↔ ∀ x, pre x → post x (implementation x) := by
  constructor
  · intro hc x hx
    obtain ⟨d, hd⟩ := available x hx
    obtain ⟨y, hy, hp⟩ := hc x d hx hd
    exact unique hy (h ⟨hd, hx⟩) ▸ hp
  · intro hp x d hx hd
    exact ⟨implementation x, h ⟨hd, hx⟩, hp x hx⟩

/-- Total correctness on represented inputs and fully represented outputs. -/
@[expose] def DataContract (input : A ↪ D) (output : B ↪ E) (meaning : D → E)
    (pre : A → Prop) (post : A → B → Prop) : Prop :=
  ∀ x, pre x → ∃ y, meaning (input x) = output y ∧ post x y

/-- Injective encodings are the special case with one semantic representative per value. -/
theorem dataContract_iff_relationalContract (input : A ↪ D) (output : B ↪ E)
    (meaning : D → E) (pre : A → Prop) (post : A → B → Prop) :
    DataContract input output meaning pre post ↔
      RelationalContract (fun d x => input x = d) (fun e y => output y = e)
        meaning pre post := by
  constructor
  · intro h x d hx hd
    obtain ⟨y, hy, hp⟩ := h x hx
    exact ⟨y, hd ▸ hy.symm, hp⟩
  · intro h x hx
    obtain ⟨y, hy, hp⟩ := h x (input x) hx rfl
    exact ⟨y, hy.symm, hp⟩

/-- A semantic function agrees with a native implementation on admissible inputs. -/
@[expose] def CorrespondsOn (input : A ↪ D) (output : B ↪ E) (valid : A → Prop)
    (meaning : D → E) (implementation : A → B) : Prop :=
  ∀ x, valid x → meaning (input x) = output (implementation x)

namespace CorrespondsOn

variable {input : A ↪ D} {output : B ↪ E} {valid : A → Prop}
  {meaning : D → E} {implementation : A → B}

/-- Restrict the admissible inputs. -/
theorem mono (h : CorrespondsOn input output valid meaning implementation)
    {valid' : A → Prop} (hvalid : ∀ x, valid' x → valid x) :
    CorrespondsOn input output valid' meaning implementation := fun x hx => h x (hvalid x hx)

/-- Change the implementation using equality only on admissible inputs. -/
theorem congr (h : CorrespondsOn input output valid meaning implementation)
    {other : A → B} (he : ∀ x, valid x → implementation x = other x) :
    CorrespondsOn input output valid meaning other := by
  intro x hx
  rw [h x hx, he x hx]

/-- Compose correspondences when the first implementation establishes the next domain. -/
theorem comp (h : CorrespondsOn input output valid meaning implementation)
    {final : C ↪ F} {valid' : B → Prop} {meaning' : E → F} {implementation' : B → C}
    (next : CorrespondsOn output final valid' meaning' implementation')
    (admissible : ∀ x, valid x → valid' (implementation x)) :
    CorrespondsOn input final valid (meaning' ∘ meaning) (implementation' ∘ implementation) := by
  intro x hx
  change meaning' (meaning (input x)) = final (implementation' (implementation x))
  rw [h x hx, next _ (admissible x hx)]

/-- Transfer arbitrary preconditions and postconditions through a faithful encoding. -/
theorem contract_iff (h : CorrespondsOn input output valid meaning implementation)
    (pre : A → Prop) (post : A → B → Prop) (admissible : ∀ x, pre x → valid x) :
    DataContract input output meaning pre post ↔ ∀ x, pre x → post x (implementation x) := by
  rw [dataContract_iff_relationalContract]
  apply RelationalContract.iff_of_liftFun pre post
  · intro d x hx
    exact hx.1 ▸ (h x (admissible x hx.2)).symm
  · intro x _
    exact ⟨input x, rfl⟩
  · intro e y y' hy hy'
    exact output.injective (hy.trans hy'.symm)

/-- Equality to a represented result reflects equality of native results. -/
theorem eq_iff (h : CorrespondsOn input output valid meaning implementation)
    (x : A) (hx : valid x) (y : B) :
    meaning (input x) = output y ↔ implementation x = y := by
  rw [h x hx, output.injective.eq_iff]

/-- A meaning that preserves a relation to a native evaluator corresponds to an implementation
on admissible inputs when:
* each admissible input's encoding is related to a native representative (`represents`);
* a native representative of an output determines its encoding (`determines`);
* the evaluator returns the representative of the implementation's result (`total`). -/
theorem of_liftFun {Rin : D → W → Prop} {Rout : E → W' → Prop} {eval : W → W'}
    {nativeIn : A → W} {nativeOut : B → W'} (fundamental : Relator.LiftFun Rin Rout meaning eval)
    (represents : ∀ x, valid x → Rin (input x) (nativeIn x))
    (determines : ∀ y e, Rout e (nativeOut y) → e = output y)
    (total : ∀ x, valid x → eval (nativeIn x) = nativeOut (implementation x)) :
    CorrespondsOn input output valid meaning implementation := by
  intro x hx
  apply determines
  rw [← total x hx]
  exact fundamental (represents x hx)

end CorrespondsOn

/-- An implementation with an all-input semantic correspondence certificate. -/
structure CertifiedMeaning (input : A ↪ D) (output : B ↪ E) where
  /-- A meaning whose carrier may contain unrepresented or partial values. -/
  meaning : D → E
  /-- The native implementation on fully represented inputs. -/
  implementation : A → B
  /-- Every native input has the specified fully represented result. -/
  correct : ∀ x, meaning (input x) = output (implementation x)

namespace CertifiedMeaning

variable {input : A ↪ D} {output : B ↪ E}

/-- An all-input certificate supplies any restricted admissibility profile. -/
theorem correspondsOn (f : CertifiedMeaning input output) (valid : A → Prop) :
    CorrespondsOn input output valid f.meaning f.implementation := fun x _ => f.correct x

/-- The certificate as an equation of functions on native inputs. -/
theorem meaning_comp (f : CertifiedMeaning input output) :
    f.meaning ∘ input = output ∘ f.implementation :=
  funext f.correct

/-- Certify a meaning from a relation to a native evaluator, as in
`CorrespondsOn.of_liftFun`, with every input admissible. -/
@[expose] def ofLiftFun {Rin : D → W → Prop} {Rout : E → W' → Prop} {eval : W → W'}
    {nativeIn : A → W} {nativeOut : B → W'} (meaning : D → E) (implementation : A → B)
    (fundamental : Relator.LiftFun Rin Rout meaning eval)
    (represents : ∀ x, Rin (input x) (nativeIn x))
    (determines : ∀ y e, Rout e (nativeOut y) → e = output y)
    (total : ∀ x, eval (nativeIn x) = nativeOut (implementation x)) :
    CertifiedMeaning input output where
  meaning := meaning
  implementation := implementation
  correct x := CorrespondsOn.of_liftFun (valid := fun _ => True) fundamental
    (fun x _ => represents x) determines (fun x _ => total x) x trivial

/-- The certificate whose implementation is what `meaning` computes at an encoded input, read back
by `decode`, a left inverse of `output`. The premise that every such result is an encoded output
enters only the proof of correctness. -/
@[expose] def ofDecode (meaning : D → E) (decode : E → B)
    (decode_output : ∀ y, decode (output y) = y)
    (represented : ∀ x, ∃ y, meaning (input x) = output y) : CertifiedMeaning input output where
  meaning := meaning
  implementation x := decode (meaning (input x))
  correct x := by obtain ⟨y, hy⟩ := represented x; rw [hy, decode_output]

@[simp] theorem ofDecode_meaning (meaning : D → E) (decode : E → B)
    (decode_output : ∀ y, decode (output y) = y)
    (represented : ∀ x, ∃ y, meaning (input x) = output y) :
    (ofDecode meaning decode decode_output represented).meaning = meaning := rfl

@[simp] theorem ofDecode_implementation (meaning : D → E) (decode : E → B)
    (decode_output : ∀ y, decode (output y) = y)
    (represented : ∀ x, ∃ y, meaning (input x) = output y) :
    (ofDecode meaning decode decode_output represented).implementation =
      fun x => decode (meaning (input x)) := rfl

/-- Replace the implementation by a pointwise equal function. -/
@[expose] def congr (f : CertifiedMeaning input output) {g : A → B}
    (h : ∀ x, f.implementation x = g x) : CertifiedMeaning input output where
  meaning := f.meaning
  implementation := g
  correct x := h x ▸ f.correct x

@[simp] theorem congr_meaning (f : CertifiedMeaning input output) {g : A → B}
    (h : ∀ x, f.implementation x = g x) : (f.congr h).meaning = f.meaning := rfl

@[simp] theorem congr_implementation (f : CertifiedMeaning input output) {g : A → B}
    (h : ∀ x, f.implementation x = g x) : (f.congr h).implementation = g := rfl

/-- Compose total certificates through their common represented boundary. -/
@[expose] def comp {final : C ↪ F} (g : CertifiedMeaning output final)
    (f : CertifiedMeaning input output) : CertifiedMeaning input final where
  meaning := g.meaning ∘ f.meaning
  implementation := g.implementation ∘ f.implementation
  correct x := by
    change g.meaning (f.meaning (input x)) = final (g.implementation (f.implementation x))
    rw [f.correct, g.correct]

/-- The meaning of a composite certificate is the composite meaning. -/
theorem comp_meaning {final : C ↪ F} (g : CertifiedMeaning output final)
    (f : CertifiedMeaning input output) : (g.comp f).meaning = g.meaning ∘ f.meaning := rfl

/-- The implementation of a composite certificate is the composite implementation. -/
theorem comp_implementation {final : C ↪ F} (g : CertifiedMeaning output final)
    (f : CertifiedMeaning input output) :
    (g.comp f).implementation = g.implementation ∘ f.implementation := rfl

/-- Transfer a native contract through an all-input certificate. -/
theorem contract_iff (f : CertifiedMeaning input output)
    (pre : A → Prop) (post : A → B → Prop) :
    DataContract input output f.meaning pre post ↔ ∀ x, pre x → post x (f.implementation x) :=
  (f.correspondsOn pre).contract_iff pre post (fun _ hx => hx)

end CertifiedMeaning
end Control.Semantics
