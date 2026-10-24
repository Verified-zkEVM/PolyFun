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

example (pre : Nat → Prop) (post : Nat → Nat → Prop) :
    DataContract represented represented increment.meaning pre post ↔
      ∀ x, pre x → post x (x + 1) := increment.contract_iff pre post

/-- A pointwise equal implementation carries the same certificate. -/
example (pre : Nat → Prop) (post : Nat → Nat → Prop) :
    DataContract represented represented increment.meaning pre post ↔
      ∀ x, pre x → post x x.succ :=
  (increment.congr (g := Nat.succ) fun _ => rfl).contract_iff pre post

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
def flagged (x : Nat) (d : Nat × Bool) : Prop := d.1 = x

/-- Contracts transfer through the relation with `Relator.LiftFun`, using one representative
per admissible input and a left-unique output relation. -/
example (pre : Nat → Prop) (post : Nat → Nat → Prop) :
    RelationalContract flagged (fun y e => e = some y) (fun d : Nat × Bool => some (d.1 + 1))
      pre post ↔ ∀ x, pre x → post x (x + 1) :=
  RelationalContract.iff_of_liftFun pre post
    (fun _ _ hxd => by simp only [flagged] at hxd; simp [hxd.2])
    (fun x _ => ⟨(x, false), rfl⟩)
    (fun _ _ _ hy hy' => Option.some_injective _ (hy.symm.trans hy'))

end PolyFunTest.Correspondence
