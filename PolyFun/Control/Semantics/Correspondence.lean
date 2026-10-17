/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Logic.Embedding.Basic

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

/-- Total correctness on represented inputs and fully represented outputs. -/
@[expose] def DataContract (input : A ↪ D) (output : B ↪ E) (meaning : D → E)
    (pre : A → Prop) (post : A → B → Prop) : Prop :=
  ∀ x, pre x → ∃ y, meaning (input x) = output y ∧ post x y

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
  constructor
  · intro hc x hx
    obtain ⟨y, hy, hp⟩ := hc x hx
    have he : implementation x = y := output.injective ((h x (admissible x hx)).symm.trans hy)
    exact he.symm ▸ hp
  · intro hp x hx
    exact ⟨implementation x, h x (admissible x hx), hp x hx⟩

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
