/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.ITree.Domain
import PolyFun.Control.Domain.Result
import PolyFun.IPFunctor.Scoped.DomainRelation

/-!
# Public continuous-domain API canaries

Ordinary imports expose partial results, fixed-point equations and positional
environment comparison. A visible algebra may supply a lifted value without
demanding a continuation; continuous interpretation must retain it.
-/

public section

open OmegaCompletePartialOrder

universe uA uB uD

example {P : PFunctor} {α : Type} (ret : α → DomainResult Unit (DiscreteOrder Nat))
    (a : P.A) (next : P.B a → PFunctor.Resumption P α) :
    PFunctor.Resumption.denote ret (fun _ => .const (.value ⟨7⟩))
      (.query a next) = .value ⟨7⟩ := by
  rw [PFunctor.Resumption.denote_query]
  rfl

example {D : Type uD} [OmegaCompletePartialOrder D] [OrderBot D]
    (f : D →𝒄 D) : f f.fix = f.fix := f.map_fix

/-- Sort collapse preserves a failure at one position and bottom at another. -/
example :
    let D := fun _ : Bool => PointedDomain.ofType (DomainResult Unit (DiscreteOrder Nat))
    let E := fun _ : Unit => PointedDomain.ofType (DomainResult Unit (DiscreteOrder Nat))
    let η : IPFunctor.ScopedDomain.Env D [true, false] :=
      IPFunctor.ScopedDomain.Env.cons D (DomainResult.error ())
        (IPFunctor.ScopedDomain.Env.cons D ⊥ (IPFunctor.ScopedDomain.Env.empty D))
    let ζ := IPFunctor.ScopedDomain.Env.reindex D E (fun _ => ()) (fun _ => rfl) η
    ζ () .zero = DomainResult.error () ∧ ζ () (.succ .zero) = ⊥ := by
  constructor <;> rfl

/-- Positional comparison is usable across independent sort universes and arbitrary casts. -/
example {S : Type uA} {T : Type uB} {D : S → PointedDomain} {E : T → PointedDomain}
    {Γ Γ' : List S} {Δ Δ' : List T} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (η : IPFunctor.ScopedDomain.Env D Γ) (ζ : IPFunctor.ScopedDomain.Env E Δ)
    (h : IPFunctor.ScopedDomain.Env.Pointwise η ζ) :
    IPFunctor.ScopedDomain.Env.Pointwise (hΓ ▸ η) (hΔ ▸ ζ) := by
  apply IPFunctor.ScopedDomain.Env.Pointwise.cast_left
  exact fun {_ _} x y he => IPFunctor.ScopedDomain.Env.Pointwise.cast_right hΔ h x y he
