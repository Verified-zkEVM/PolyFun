/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.ITree.Domain
import PolyFun.Control.Domain.Pointed
import PolyFun.IPFunctor.Scoped.DomainRelation

/-!
# Public partial-result canaries

Ordinary imports expose lifted results with distinct errors and bottom, and
positional relations between continuous environments. A visible algebra may supply a
lifted value without demanding a continuation; continuous interpretation must
retain it.
-/

public section

open OmegaCompletePartialOrder

universe uA uB

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
  apply IPFunctor.ScopedDomain.Env.Forall₂.cast_left
  exact IPFunctor.ScopedDomain.Env.Forall₂.cast_right hΔ h

/-- A family of maps can cross universes of domains, which an equation of domains cannot. -/
example {S T : Type} {D : S → PointedDomain.{uA}} {E : T → PointedDomain.{uB}} (f : S → T)
    (t : ∀ a, D a →𝒄 E (f a)) {Γ : List S} (η : IPFunctor.ScopedDomain.Env D Γ) {a : S}
    (x : IPFunctor.ScopedVar Γ a) :
    IPFunctor.ScopedDomain.Env.map D E f t η (f a) (x.map f) = t a (η a x) := by
  simp only [IPFunctor.ScopedDomain.Env.map_apply]

/-- Identity normalization needs no equation of domains. -/
example {S : Type} {D : S → PointedDomain} {Γ : List S} (η : IPFunctor.ScopedDomain.Env D Γ) :
    IPFunctor.ScopedDomain.Env.map D D id (fun _ => ContinuousHom.id) η =
      (List.map_id Γ).symm ▸ η :=
  IPFunctor.ScopedDomain.Env.map_id D η

/-- The fixed-point law applies to relations that are not functions: here, approximation. -/
example {S T : Type} {X : PointedDomain} (f : S → T) {Γ : List S} {Δ : List T} {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → IPFunctor.ScopedDomain.Env (fun _ => X) (Ξ ++ Γ) →𝒄 X)
    (rhs' : (j : Fin (Ξ.map f).length) →
      IPFunctor.ScopedDomain.Env (fun _ => X) (Ξ.map f ++ Δ) →𝒄 X)
    (η : IPFunctor.ScopedDomain.Env (fun _ => X) Γ)
    (ζ : IPFunctor.ScopedDomain.Env (fun _ => X) Δ)
    (h : ∀ ξ ψ, IPFunctor.ScopedDomain.Env.Forall₂ (fun _ _ x y => x ≤ y) ξ ψ →
      ∀ i j, i.val = j.val → rhs i (IPFunctor.ScopedDomain.Env.append _ ξ η) ≤
        rhs' j (IPFunctor.ScopedDomain.Env.append _ ψ ζ)) :
    IPFunctor.ScopedDomain.Env.Forall₂ (fun _ _ x y => x ≤ y)
      (IPFunctor.ScopedDomain.Env.fixGroup _ rhs η)
      (IPFunctor.ScopedDomain.Env.fixGroup _ rhs' ζ) :=
  IPFunctor.ScopedDomain.Env.fixGroup_forall₂ f (fun _ => le_rfl)
    (fun _ _ hc => ωSup_le_ωSup_of_le fun n => ⟨n, hc n⟩) rhs rhs' η ζ h
