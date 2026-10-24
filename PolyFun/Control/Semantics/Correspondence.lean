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
-/

public section

namespace Control.Semantics

universe uA uB uC uD uE uF

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {D : Type uD} {E : Type uE} {F : Type uF}

/-- Total correctness for every semantic representative of each admissible input.
Relations permit partial values and irrelevant components to have many representations. -/
@[expose] def RelationalContract (input : A → D → Prop) (output : B → E → Prop)
    (meaning : D → E) (pre : A → Prop) (post : A → B → Prop) : Prop :=
  ∀ x d, pre x → input x d → ∃ y, output y (meaning d) ∧ post x y

/-- A logical relation transfers contracts when represented outputs determine
a unique native result. Input representations need exist only on the precondition. -/
theorem RelationalContract.iff_of_liftFun
    {input : A → D → Prop} {output : B → E → Prop}
    {meaning : D → E} {implementation : A → B} (pre : A → Prop) (post : A → B → Prop)
    (h : Relator.LiftFun (fun x d => pre x ∧ input x d) output implementation meaning)
    (available : ∀ x, pre x → ∃ d, input x d) (unique : Relator.LeftUnique output) :
    RelationalContract input output meaning pre post ↔ ∀ x, pre x → post x (implementation x) := by
  constructor
  · intro hc x hx
    obtain ⟨d, hd⟩ := available x hx
    obtain ⟨y, hy, hp⟩ := hc x d hx hd
    exact unique hy (h ⟨hx, hd⟩) ▸ hp
  · intro hp x d hx hd
    exact ⟨implementation x, h ⟨hx, hd⟩, hp x hx⟩

/-- Total correctness on represented inputs and fully represented outputs. -/
@[expose] def DataContract (input : A ↪ D) (output : B ↪ E) (meaning : D → E)
    (pre : A → Prop) (post : A → B → Prop) : Prop :=
  ∀ x, pre x → ∃ y, meaning (input x) = output y ∧ post x y

/-- Injective encodings are the special case with one semantic representative per value. -/
theorem dataContract_iff_relationalContract (input : A ↪ D) (output : B ↪ E)
    (meaning : D → E) (pre : A → Prop) (post : A → B → Prop) :
    DataContract input output meaning pre post ↔
      RelationalContract (fun x d => input x = d) (fun y e => output y = e)
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
  · intro x d hx
    exact hx.2 ▸ (h x (admissible x hx.1)).symm
  · intro x _
    exact ⟨input x, rfl⟩
  · intro x y d hx hy
    exact output.injective (hx.trans hy.symm)

/-- Equality to a represented result reflects equality of native results. -/
theorem eq_iff (h : CorrespondsOn input output valid meaning implementation)
    (x : A) (hx : valid x) (y : B) :
    meaning (input x) = output y ↔ implementation x = y := by
  rw [h x hx, output.injective.eq_iff]

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

/-- Transfer a native contract through an all-input certificate. -/
theorem contract_iff (f : CertifiedMeaning input output)
    (pre : A → Prop) (post : A → B → Prop) :
    DataContract input output f.meaning pre post ↔ ∀ x, pre x → post x (f.implementation x) :=
  (f.correspondsOn pre).contract_iff pre post (fun _ hx => hx)

end CertifiedMeaning
end Control.Semantics
