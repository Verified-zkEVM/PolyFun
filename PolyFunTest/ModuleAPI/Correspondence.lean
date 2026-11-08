/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Semantics.Correspondence

/-! # Ordinary-import checks for represented-data contracts -/

open Control.Semantics

public section

namespace PolyFunTest.Correspondence

/-- Successful values represented inside a carrier that also has failure. -/
def represented : Nat ↪ Option Nat := ⟨some, Option.some_injective Nat⟩

private def increment : CertifiedMeaning represented represented where
  meaning := Option.map (· + 1)
  implementation := (· + 1)
  correct _ := rfl

example (x : Nat) : (increment.comp increment).meaning (some x) = some (x + 1 + 1) :=
  (increment.comp increment).correct x

/-- A certificate is an equation of functions on native inputs. -/
example : increment.meaning ∘ represented = represented ∘ (· + 1) := increment.meaning_comp

/-- The projections of a composite certificate are composites. -/
example : (increment.comp increment).meaning = Option.map (· + 1) ∘ Option.map (· + 1) :=
  CertifiedMeaning.comp_meaning increment increment

/-- Replacing the implementation by a pointwise equal function keeps the meaning. -/
example : (increment.congr (g := (1 + ·)) (Nat.add_comm · 1)).implementation = (1 + ·) ∧
    (increment.congr (g := (1 + ·)) (Nat.add_comm · 1)).meaning = increment.meaning :=
  ⟨CertifiedMeaning.congr_implementation _ _, CertifiedMeaning.congr_meaning _ _⟩

/-- A meaning certified from its relation to a native evaluator: a semantic value is related to
the native number it holds, and that number determines the encoded output. -/
private def incrementByRelation : CertifiedMeaning represented represented :=
  CertifiedMeaning.ofLiftFun (Rin := fun d w => d = some w) (Rout := fun e w => e = some w)
    (eval := (· + 1)) (nativeIn := id) (nativeOut := id) (Option.map (· + 1)) (· + 1)
    (fun _ _ h => h ▸ rfl) (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl)

/-- The certified meaning and implementation are the ones supplied. -/
example (x : Nat) : incrementByRelation.meaning (some x) = some (x + 1) ∧
    incrementByRelation.implementation x = x + 1 := ⟨rfl, rfl⟩

/-- A meaning certified by reading its results back: every encoded input has an encoded result,
and `Option.getD` with any default is a left inverse of `some`. -/
private def incrementByDecode : CertifiedMeaning represented represented :=
  CertifiedMeaning.ofDecode (Option.map (· + 1)) (·.getD 0) (fun _ => rfl)
    (fun x => ⟨x + 1, rfl⟩)

/-- Its implementation is the meaning, read back, and computes by unfolding. -/
example (x : Nat) : incrementByDecode.implementation x = x + 1 := rfl

example : incrementByDecode.meaning = Option.map (· + 1) ∧
    incrementByDecode.implementation = fun x => (Option.map (· + 1) (some x)).getD 0 :=
  ⟨CertifiedMeaning.ofDecode_meaning .., CertifiedMeaning.ofDecode_implementation ..⟩

/-- The certificate transfers contracts like any other. -/
example (x : Nat) : incrementByDecode.meaning (represented x) = represented (x + 1) :=
  incrementByDecode.correct x

example (pre : Nat → Prop) (post : Nat → Nat → Prop) :
    DataContract represented represented increment.meaning pre post ↔
      ∀ x, pre x → post x (x + 1) := increment.contract_iff pre post

-- Unrepresented failure cannot satisfy total correctness, even for a trivial postcondition.
example : ¬ DataContract represented represented (fun _ => none)
    (fun x => x = 0) (fun _ _ => True) := by
  intro h
  obtain ⟨_, he, _⟩ := h 0 rfl
  cases he

example {valid valid' : Nat → Prop} {f g : Nat → Nat}
    {m n : Option Nat → Option Nat}
    (hf : CorrespondsOn represented represented valid m f)
    (hg : CorrespondsOn represented represented valid' n g)
    (domain : ∀ x, valid x → valid' (f x)) :
    CorrespondsOn represented represented valid (n ∘ m) (g ∘ f) := hf.comp hg domain

/-- A value represented with an irrelevant flag: every native input has two semantic
representatives, so the representation is a relation rather than an embedding. -/
def flagged (d : Nat × Bool) (x : Nat) : Prop := d.1 = x

/-- Contracts transfer through the relation with `Relator.LiftFun`, using one representative
per admissible input and an output relation that determines the native result. The semantic
value comes first in both relations. -/
example (pre : Nat → Prop) (post : Nat → Nat → Prop) :
    RelationalContract flagged (fun e y => e = some y) (fun d : Nat × Bool => some (d.1 + 1))
      pre post ↔ ∀ x, pre x → post x (x + 1) :=
  RelationalContract.iff_of_liftFun pre post
    (fun _ _ hdx => by simp only [flagged] at hdx; simp [hdx.1])
    (fun x _ => ⟨(x, false), rfl⟩)
    (fun _ _ _ hy hy' => Option.some_injective _ (hy.symm.trans hy'))

end PolyFunTest.Correspondence
