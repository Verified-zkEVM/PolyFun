/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.ITree.Domain
import PolyFun.Control.Domain.Pointed

/-!
# Public partial-result canaries

Ordinary imports expose lifted results with distinct errors and bottom. A visible
algebra may supply a lifted value without demanding a continuation; continuous
interpretation must retain it.
-/

public section

open OmegaCompletePartialOrder

example {P : PFunctor} {α : Type} (ret : α → DomainResult Unit (DiscreteOrder Nat))
    (a : P.A) (next : P.B a → PFunctor.Resumption P α) :
    PFunctor.Resumption.denote ret (fun _ => .const (.value ⟨7⟩))
      (.query a next) = .value ⟨7⟩ := by
  rw [PFunctor.Resumption.denote_query]
  rfl

/-- An error is a defined outcome: it is neither bottom nor below a value. -/
example (e : Unit) (x : DiscreteOrder Nat) :
    DomainResult.error (α := DiscreteOrder Nat) e ≠ ⊥ ∧
      ¬DomainResult.error e ≤ DomainResult.value x :=
  ⟨DomainResult.error_ne_bot e, DomainResult.not_error_le_value e x⟩

/-- Sequencing is strict in bottom and propagates the first error. -/
example (f : DiscreteOrder Nat →𝒄 DomainResult Unit (DiscreteOrder Nat)) (e : Unit) :
    DomainResult.bind f ⊥ = ⊥ ∧ DomainResult.bind f (.error e) = .error e :=
  ⟨DomainResult.bind_bot f, DomainResult.bind_error f e⟩
