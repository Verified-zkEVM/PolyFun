/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.ResultRel
meta import PolyFun.Control.Domain.ResultRel

/-!
# Results without an order

`DomainResult.bindPlain`, `ifValue` and `Fin.mOfFn` in `DomainResult.monad` compute on results
over natural numbers, by `rfl` and as compiled code. `Fin.mOfFn` collects from left to right, so the
first result that is not a value is the outcome, whether it is bottom or an error, and compiled code
collects 64 results quickly.

`DomainResult.Approx` lets bottom on the right approximate every result, which `LiftRel` does not,
and an error approximates only the same error. `approx_bind` carries approximation through a
continuous `bind` on the left and `bindPlain` on the right.
-/

public section

open OmegaCompletePartialOrder

namespace PolyFunTest.DomainSequencing

/-- Results with string errors. -/
abbrev Res (α : Type) := DomainResult String α

/-- The successor, as a continuation. -/
def succ (n : ℕ) : Res ℕ := .value (n + 1)

/-! ## Sequencing -/

/-- `bindPlain` passes bottom and errors through; `ifValue` gives bottom at an error. -/
example : DomainResult.bindPlain (.value 2 : Res ℕ) succ = .value 3 ∧
    DomainResult.bindPlain (⊥ : Res ℕ) succ = ⊥ ∧
    DomainResult.bindPlain (.error "e" : Res ℕ) succ = .error "e" ∧
    DomainResult.ifValue (.value 2 : Res ℕ) succ = .value 3 ∧
    DomainResult.ifValue (.error "e" : Res ℕ) succ = ⊥ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Element `i` of a family: a value at `0`, then the given results. -/
def family (second third : Res ℕ) (i : Fin 3) : Res ℕ :=
  if i.val = 0 then .value 7 else if i.val = 1 then second else third

/-- Collecting values returns them. -/
example : DomainResult.map List.ofFn
    (@Fin.mOfFn _ DomainResult.monad _ 3 (family (.value 8) (.value 9))) = .value [7, 8, 9] := rfl

/-- An error before bottom is the outcome. -/
example : @Fin.mOfFn _ DomainResult.monad _ 3 (family (.error "second") ⊥) = .error "second" :=
  rfl

/-- Bottom before an error is the outcome. -/
example : @Fin.mOfFn _ DomainResult.monad _ 3 (family ⊥ (.error "third")) = ⊥ := rfl

/-- A collected value fixes every element. -/
example {f : Fin 2 → Res ℕ} {g : Fin 2 → ℕ} (h : @Fin.mOfFn _ DomainResult.monad _ 2 f = .value g) :
    f 1 = .value (g 1) :=
  DomainResult.mOfFn_eq_value_iff.mp h 1

/-- `toOption` reads exactly the returned value. -/
example {d : Res ℕ} (h : DomainResult.toOption d = some 4) : d = .value 4 :=
  DomainResult.toOption_eq_some_iff.mp h

/-- info: some [7, 8, 9] -/
#guard_msgs in
#eval (DomainResult.toOption (@Fin.mOfFn _ DomainResult.monad _ 3
  (family (.value 8) (.value 9)))).map List.ofFn

/-- The sum of `0, …, n - 1`, collected and then read back. Compiled code reads a collected
function in time linear in its index, so this takes time polynomial in `n`. -/
def collectedSum (n : ℕ) : Option ℕ :=
  (DomainResult.toOption (@Fin.mOfFn _ DomainResult.monad _ n fun i => (.value i.val : Res ℕ))).map
    fun f => (List.ofFn f).sum

/-- info: some 2016 -/
#guard_msgs in
#eval collectedSum 64

/-! ## Approximation -/

/-- A semantic number and a native one agree. -/
abbrev Agree (x : DiscreteOrder ℕ) (n : ℕ) : Prop := x = ⟨n⟩

/-- Bottom approximates a value, which `LiftRel` does not relate to bottom. -/
example : DomainResult.Approx Agree (.value ⟨3⟩ : Res (DiscreteOrder ℕ)) (⊥ : Res ℕ) ∧
    ¬DomainResult.LiftRel (· = ·) Agree (.value ⟨3⟩ : Res (DiscreteOrder ℕ)) (⊥ : Res ℕ) :=
  ⟨trivial, id⟩

/-- An error approximates only the same error. -/
example : DomainResult.Approx Agree (.error "e" : Res (DiscreteOrder ℕ)) (.error "e" : Res ℕ) ∧
    ¬DomainResult.Approx Agree (⊥ : Res (DiscreteOrder ℕ)) (.error "e" : Res ℕ) :=
  ⟨rfl, fun h => DomainResult.error_ne_bot "e" h.symm⟩

/-- A value approximates a related value. -/
example : DomainResult.Approx Agree (.value ⟨3⟩ : Res (DiscreteOrder ℕ)) (.value 3 : Res ℕ) :=
  DomainResult.approx_value_value.mpr rfl

/-- Away from bottom, approximation is the lifted relation with equal errors. -/
example {d : Res (DiscreteOrder ℕ)} {r : Res ℕ} (h : DomainResult.Approx Agree d r)
    (hr : r ≠ ⊥) : DomainResult.LiftRel (· = ·) Agree d r :=
  (DomainResult.approx_iff.mp h).resolve_left hr

/-- The semantic successor, continuous because its domain is discrete. -/
noncomputable def succD : DiscreteOrder ℕ →𝒄 Res (DiscreteOrder ℕ) :=
  DiscreteOrder.continuousMap fun n => .value ⟨n + 1⟩

/-- The continuous `bind` is `bindPlain` with the same continuation. -/
example (d : Res (DiscreteOrder ℕ)) :
    DomainResult.bind succD d = DomainResult.bindPlain d succD :=
  DomainResult.bind_eq_bindPlain succD d

/-- The successors of approximated numbers are approximated. -/
example {d : Res (DiscreteOrder ℕ)} {r : Res ℕ} (h : DomainResult.Approx Agree d r) :
    DomainResult.Approx Agree (DomainResult.bind succD d) (DomainResult.bindPlain r succ) :=
  DomainResult.approx_bind h fun _ _ hxn => by
    subst hxn
    exact DomainResult.approx_value_value.mpr rfl

end PolyFunTest.DomainSequencing
