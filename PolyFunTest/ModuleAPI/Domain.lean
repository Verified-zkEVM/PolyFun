/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.ITree.Domain
public import PolyFun.Control.Domain.Pointed
public import PolyFun.IPFunctor.Scoped.DomainRelation

/-!
# Public partial-result canaries

Ordinary imports expose lifted results with distinct errors and bottom, and
positional relations between continuous environments. A visible algebra may supply a
lifted value without demanding a continuation; continuous interpretation must
retain it. Environment values need only an order on each sort, so a family of
computation types is used directly, without bundling it as pointed domains.
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
    let η : IPFunctor.ScopedSignature.Env (fun a => D a) [true, false] :=
      IPFunctor.ScopedSignature.Env.cons (DomainResult.error ())
        (IPFunctor.ScopedSignature.Env.cons ⊥ IPFunctor.ScopedSignature.Env.empty)
    let ζ := IPFunctor.ScopedSignature.Env.transport (E := E) (fun _ => ()) (fun _ => rfl) η
    ζ () .zero = DomainResult.error () ∧ ζ () (.succ .zero) = ⊥ := by
  constructor <;> rfl

/-- Positional comparison is usable across independent sort universes and arbitrary casts. -/
example {S : Type uA} {T : Type uB} {V : S → Type} {W : T → Type}
    {Γ Γ' : List S} {Δ Δ' : List T} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (η : IPFunctor.ScopedSignature.Env V Γ) (ζ : IPFunctor.ScopedSignature.Env W Δ)
    (h : IPFunctor.ScopedSignature.Env.Pointwise η ζ) :
    IPFunctor.ScopedSignature.Env.Pointwise (hΓ ▸ η) (hΔ ▸ ζ) := by
  apply IPFunctor.ScopedSignature.Env.Forall₂.cast_left
  exact IPFunctor.ScopedSignature.Env.Forall₂.cast_right hΔ h

/-- A family of maps can cross universes of values, which an equation of domains cannot. -/
example {S T : Type} {V : S → Type uA} {W : T → Type uB}
    [∀ a, OmegaCompletePartialOrder (V a)] [∀ b, OmegaCompletePartialOrder (W b)] (f : S → T)
    (t : ∀ a, V a →𝒄 W (f a)) {Γ : List S} (η : IPFunctor.ScopedSignature.Env V Γ) {a : S}
    (x : IPFunctor.ScopedVar Γ a) :
    IPFunctor.ScopedSignature.Env.map f t η (f a) (x.map f) = t a (η a x) := by
  simp only [IPFunctor.ScopedSignature.Env.map_apply]

/-- Identity normalization needs no equation of domains. -/
example {S : Type} {V : S → Type} [∀ a, OmegaCompletePartialOrder (V a)] {Γ : List S}
    (η : IPFunctor.ScopedSignature.Env V Γ) :
    IPFunctor.ScopedSignature.Env.map id (fun _ => ContinuousHom.id) η =
      (List.map_id Γ).symm ▸ η :=
  IPFunctor.ScopedSignature.Env.map_id η

/-- The fixed-point law applies to relations that are not functions: here, approximation. -/
example {S T : Type} {X : Type} [OmegaCompletePartialOrder X] [OrderBot X] (f : S → T)
    {Γ : List S} {Δ : List T} {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → IPFunctor.ScopedSignature.Env (fun _ => X) (Ξ ++ Γ) →𝒄 X)
    (rhs' : (j : Fin (Ξ.map f).length) →
      IPFunctor.ScopedSignature.Env (fun _ => X) (Ξ.map f ++ Δ) →𝒄 X)
    (η : IPFunctor.ScopedSignature.Env (fun _ => X) Γ)
    (ζ : IPFunctor.ScopedSignature.Env (fun _ => X) Δ)
    (h : ∀ ξ ψ, IPFunctor.ScopedSignature.Env.Forall₂ (fun _ _ x y => x ≤ y) ξ ψ →
      ∀ i j, i.val = j.val → rhs i (IPFunctor.ScopedSignature.Env.append ξ η) ≤
        rhs' j (IPFunctor.ScopedSignature.Env.append ψ ζ)) :
    IPFunctor.ScopedSignature.Env.Forall₂ (fun _ _ x y => x ≤ y)
      (IPFunctor.ScopedSignature.Env.fixGroup rhs η)
      (IPFunctor.ScopedSignature.Env.fixGroup rhs' ζ) :=
  IPFunctor.ScopedSignature.Env.fixGroup_forall₂ f (fun _ => le_rfl)
    (fun _ _ hc => ωSup_le_ωSup_of_le fun n => ⟨n, hc n⟩) rhs rhs' η ζ h

/-! ## Recursive groups -/

namespace PolyFunTest.RecursiveGroup

open IPFunctor IPFunctor.ScopedSignature

/-- One sort of partial numbers, used directly as an unbundled family of computations. -/
abbrev Num : Unit → Type := fun _ => DomainResult Unit (DiscreteOrder Nat)

/-- Read one binding position of an environment. -/
noncomputable def lookup {Γ : List Unit} (x : ScopedVar Γ ()) : Env Num Γ →𝒄 Num () :=
  .ofFun fun η => η () x

/-- The first binding reads the second, and the second reads the ambient binding. -/
noncomputable def chain : (i : Fin ([(), ()] : List Unit).length) →
    Env Num ([(), ()] ++ [()]) →𝒄 Num ([(), ()] : List Unit)[i] :=
  fun i => if i.val = 0 then lookup (.succ .zero) else lookup (.succ (.succ .zero))

/-- The second binding reads past the whole group to the ambient binding. -/
example (v : Num ()) : Env.fixGroup chain (Env.single v) () (.succ .zero) = v := by
  rw [Env.fixGroup_unfold]
  rfl

/-- The first binding reads the second inside the group, and so reaches the ambient binding. -/
example (v : Num ()) : Env.fixGroup chain (Env.single v) () .zero = v := by
  rw [Env.fixGroup_unfold]
  change Env.fixGroup chain (Env.single v) () (.succ .zero) = v
  rw [Env.fixGroup_unfold]
  rfl

/-- A binding defined as itself. -/
noncomputable def selfReference : (i : Fin ([()] : List Unit).length) →
    Env Num ([()] ++ []) →𝒄 Num ([()] : List Unit)[i] :=
  fun _ => lookup .zero

/-- A self-recursive singleton carries no information, so the least fixed point is bottom. -/
example : Env.fixGroup selfReference (Env.empty (V := Num)) () .zero = ⊥ := by
  refine le_antisymm (Env.fixGroup_le selfReference Env.empty ⊥ ?_ () .zero) bot_le
  intro _ x
  cases x with
  | zero => exact le_rfl
  | succ x => cases x

/-! ## One-variable binders -/

/-- Extension is continuous in the new value and the environment, by `fun_prop`. -/
example {S : Type} {V : S → Type} [∀ a, OmegaCompletePartialOrder (V a)] {Γ : List S} {a : S}
    {α : Type} [OmegaCompletePartialOrder α] (f : α →𝒄 V a) (g : α →𝒄 Env V Γ) :
    ωScottContinuous fun t => Env.cons (f t) (g t) := by
  fun_prop

/-- A meaning of a one-variable body, as a continuous function of that variable. -/
example (v : Num ()) : Env.bindOne (lookup .zero) v = v := by
  rw [Env.bindOne_apply]
  rfl

/-- A lazy binding passes its value to the body without forcing it. -/
example : Env.bindOne (E := Num ()) (.const (.value ⟨3⟩)) (⊥ : Num ()) = .value ⟨3⟩ := rfl

/-- A one-variable body that returns its own variable has bottom as least fixed point. -/
example : ContinuousHom.fixContinuous (Env.bindOne (lookup (Γ := [()]) .zero)) = ⊥ := by
  refine le_antisymm (ContinuousHom.fix_le _ ?_) bot_le
  rw [Env.bindOne_apply]
  exact le_rfl

end PolyFunTest.RecursiveGroup
