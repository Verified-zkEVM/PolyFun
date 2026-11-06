/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Transport
public import PolyFun.Control.Domain.Pointed

/-!
# Continuous environments for scoped syntax

Lookup uses binding positions. Mapping environments along a sort map therefore
permits distinct source sorts to become equal, as happens when substituting type
parameters.
-/

public section

open OmegaCompletePartialOrder

namespace IPFunctor.ScopedDomain

variable {S T : Type*} (D : S → PointedDomain) {Γ Δ : List S}

/-- One suspended semantic value for each binding position. -/
abbrev Env (Γ : List S) := ∀ a, ScopedVar Γ a → D a

namespace Env

/-- Read an environment along a map of binding positions. -/
@[expose] noncomputable def rename (ρ : ScopedSignature.Renaming Γ Δ) :
    Env D Δ →𝒄 Env D Γ := .ofFun (fun η a x => η a (ρ x)) (by fun_prop)

@[simp] theorem rename_apply (ρ : ScopedSignature.Renaming Γ Δ)
    (η : Env D Δ) {a : S} (x : ScopedVar Γ a) : rename D ρ η a x = η a (ρ x) := rfl

@[simp] theorem rename_id (η : Env D Γ) : rename D (fun x => x) η = η := rfl

/-- Environment lookup reverses composition of variable maps. -/
theorem rename_rename {Θ : List S} (ρ : ScopedSignature.Renaming Γ Δ)
    (τ : ScopedSignature.Renaming Δ Θ) (η : Env D Θ) :
    rename D ρ (rename D τ η) = rename D (fun x => τ (ρ x)) η := rfl

/-- Context transport preserves lookup at the corresponding binding position. -/
theorem cast_apply {Δ : List S} (h : Γ = Δ) (η : Env D Γ) {a : S} (x : ScopedVar Γ a) :
    (h ▸ η) a (h ▸ x) = η a x := by
  cases h
  rfl

/-- Assemble a typed environment from its finite list of binding positions. -/
@[expose] def ofFin : {Ξ : List S} → ((i : Fin Ξ.length) → D Ξ[i]) → Env D Ξ
  | _ :: _, f, _, .zero => f 0
  | _ :: _, f, _, .succ x => ofFin (fun i => f i.succ) _ x

/-- Assembling environments is continuous in all their components. -/
@[expose] noncomputable def ofFinContinuous {Ξ : List S} :
    ((i : Fin Ξ.length) → D Ξ[i]) →𝒄 Env D Ξ := .ofFun (ofFin D) (by
  apply ωScottContinuous.of_apply₂
  intro a
  apply ωScottContinuous.of_apply₂
  intro x
  induction x with
  | zero => exact ωScottContinuous.apply 0
  | succ x ih => exact ih.comp (by fun_prop))

/-- The unique environment of an empty context. -/
@[expose] def empty : Env D [] := fun _ x => nomatch x

/-- Add a value at the nearest binding position. -/
@[expose] def cons {a : S} (x : D a) (η : Env D Γ) : Env D (a :: Γ) :=
  fun _ v => match v with
  | .zero => x
  | .succ v => η _ v

/-- Extend an environment with a whole block of bindings. -/
@[expose] def append : {Ξ : List S} → Env D Ξ → Env D Γ → Env D (Ξ ++ Γ)
  | [], _, η => η
  | a :: _, ξ, η => cons D (ξ a .zero) (append (fun b v => ξ b (.succ v)) η)

/-- Protecting a fresh variable preserves its value under environment lookup. -/
theorem rename_cons (ρ : ScopedSignature.Renaming Γ Δ) {a : S}
    (x : D a) (η : Env D Δ) :
    rename D (ρ.lift a) (cons D x η) = cons D x (rename D ρ η) := by
  funext b v
  cases v <;> rfl

/-- The fresh block is unchanged when the ambient environment is renamed. -/
theorem rename_append (ρ : ScopedSignature.Renaming Γ Δ) {Ξ : List S}
    (ξ : Env D Ξ) (η : Env D Δ) :
    rename D (ρ.liftMany Ξ) (append D ξ η) = append D ξ (rename D ρ η) := by
  induction Ξ with
  | nil => rfl
  | cons a Ξ ih =>
      change rename D (ScopedSignature.Renaming.lift (ρ.liftMany Ξ) a) (cons D _ _) = _
      rw [rename_cons, ih]
      rfl

/-- Adding one binding is jointly continuous. -/
@[expose] noncomputable def consContinuous {a : S} :
    (D a × Env D Γ) →𝒄 Env D (a :: Γ) := .ofFun (fun p => cons D p.1 p.2) (by
  apply ωScottContinuous.of_apply₂
  intro b
  apply ωScottContinuous.of_apply₂
  intro x
  cases x <;> simp only [cons] <;> fun_prop)

/-- Appending a finite block of bindings is jointly continuous. -/
@[expose] noncomputable def appendContinuous {Ξ : List S} :
    (Env D Ξ × Env D Γ) →𝒄 Env D (Ξ ++ Γ) := .ofFun (fun p => append D p.1 p.2) (by
  induction Ξ with
  | nil => exact Prod.ωScottContinuous_snd
  | cons a Ξ ih =>
      change ωScottContinuous (fun p : Env D (a :: Ξ) × Env D Γ => consContinuous D
        (p.1 a .zero, append D (fun b v => p.1 b (.succ v)) p.2))
      apply (consContinuous D).ωScottContinuous.comp
      apply Prod.ωScottContinuous.prodMk
      · fun_prop
      · have h : ωScottContinuous (fun p : Env D (a :: Ξ) × Env D Γ =>
            (((fun b v => p.1 b (.succ v)) : Env D Ξ), p.2)) := by fun_prop
        exact ih.comp h)

/-- Apply a family of continuous maps at every binding position. The sort map need
not be injective, and the two families of domains may lie in different universes. -/
@[expose] noncomputable def map (E : T → PointedDomain) (f : S → T)
    (t : ∀ a, D a →𝒄 E (f a)) : Env D Γ →𝒄 Env E (Γ.map f) :=
  .ofFun (fun η _ x => ScopedVar.mapLookup f (V := fun b => E b)
    (fun {a} v => t a (η a v)) x) (by
      apply ωScottContinuous.of_apply₂
      intro b
      apply ωScottContinuous.of_apply₂
      intro x
      induction x using ScopedVar.map_inductionOn with
      | h a x =>
          simp only [ScopedVar.mapLookup_map]
          fun_prop)

@[simp] theorem map_apply (E : T → PointedDomain) (f : S → T)
    (t : ∀ a, D a →𝒄 E (f a)) (η : Env D Γ) {a : S} (x : ScopedVar Γ a) :
    map D E f t η (f a) (x.map f) = t a (η a x) :=
  ScopedVar.mapLookup_map f (V := fun b => E b) _ x

/-- The identity family at the identity sort map performs only context normalization. -/
theorem map_id (η : Env D Γ) :
    map D D id (fun _ => ContinuousHom.id) η = (List.map_id Γ).symm ▸ η := by
  funext a x
  induction x using ScopedVar.map_inductionOn id with
  | h a x =>
      rw [map_apply, ScopedVar.map_id, cast_apply]
      rfl

/-- Mapping retains the nearest binding and maps the older positions. -/
theorem map_cons (E : T → PointedDomain) (f : S → T)
    (t : ∀ a, D a →𝒄 E (f a)) {a : S} (x : D a) (η : Env D Γ) :
    map D E f t (cons D x η) = cons E (t a x) (map D E f t η) := by
  funext b v
  cases v <;> rfl

/-- Changing sorts commutes with changing binding positions, even for noninjective maps. -/
theorem map_rename (E : T → PointedDomain) (f : S → T)
    (t : ∀ a, D a →𝒄 E (f a)) (ρ : ScopedSignature.Renaming Γ Δ) (η : Env D Δ) :
    map D E f t (rename D ρ η) =
      rename E (ScopedSignature.Renaming.map f ρ) (map D E f t η) := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => simp only [map_apply, rename_apply, ScopedSignature.Renaming.map_apply]

/-- Consecutive maps compose at each original binding position. The two contexts are
equal only propositionally, so the law compares lookups; `ScopedVar.map_inductionOn`
shows that these positions exhaust both contexts. -/
theorem map_map {U : Type*} (E : T → PointedDomain) (F : U → PointedDomain)
    (f : S → T) (g : T → U) (t : ∀ a, D a →𝒄 E (f a)) (u : ∀ b, E b →𝒄 F (g b))
    (η : Env D Γ) {a : S} (x : ScopedVar Γ a) :
    map E F g u (map D E f t η) (g (f a)) ((x.map f).map g) =
      map D F (g ∘ f) (fun a => (u (f a)).comp (t a)) η (g (f a)) (x.map (g ∘ f)) := by
  rw [map_apply, map_apply]
  exact (map_apply D F (g ∘ f) (fun a => (u (f a)).comp (t a)) η x).symm

/-- A strict family maps the empty information state to itself. -/
theorem map_bot (E : T → PointedDomain) (f : S → T)
    (t : ∀ a, D a →𝒄 E (f a)) (ht : ∀ a, t a ⊥ = ⊥) :
    map D E f t (⊥ : Env D Γ) = ⊥ := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => simp only [map_apply, Pi.bot_apply, ht]

/-- Map binding positions along an equation of their domains. -/
@[expose] noncomputable def reindex (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) : Env D Γ →𝒄 Env E (Γ.map f) :=
  map D E f (fun a => PointedDomain.cast (h a).symm)

/-- Tie a finite, possibly heterogeneous recursive group by one least fixed point.
Every right-hand side sees the entire group and the ambient environment. -/
@[expose] noncomputable def fixGroup {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i]) :
    Env D Γ →𝒄 Env D Ξ :=
  ContinuousHom.fixContinuous.comp (.ofFun (fun η =>
    ContinuousHom.ofFun (fun ξ => ofFinContinuous D
      (fun i => rhs i (appendContinuous D (ξ, η))))))

/-- Unfold all declarations in a recursive group simultaneously. -/
theorem fixGroup_unfold {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i]) (η : Env D Γ) :
    fixGroup D rhs η = ofFin D (fun i => rhs i (append D (fixGroup D rhs η) η)) :=
  (ContinuousHom.map_fix (ContinuousHom.ofFun (fun ξ => ofFinContinuous D
    (fun i => rhs i (appendContinuous D (ξ, η)))))).symm

/-- A group denotes the least simultaneous prefixed point. -/
theorem fixGroup_le {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i]) (η : Env D Γ) (ξ : Env D Ξ)
    (h : ofFin D (fun i => rhs i (append D ξ η)) ≤ ξ) : fixGroup D rhs η ≤ ξ :=
  ContinuousHom.fix_le _ h

/-- Equal group transformers have equal simultaneous least fixed points.
The ambient environments may differ; the whole recursive block is compared at once. -/
theorem fixGroup_congr {Θ Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (i : Fin Ξ.length) → Env D (Ξ ++ Θ) →𝒄 D Ξ[i])
    (η : Env D Γ) (η' : Env D Θ)
    (h : ∀ ξ i, rhs i (append D ξ η) = rhs' i (append D ξ η')) :
    fixGroup D rhs η = fixGroup D rhs' η' := by
  change ContinuousHom.fix _ = ContinuousHom.fix _
  congr 1
  apply ContinuousHom.ext
  intro ξ
  exact congrArg (ofFin D) (funext (h ξ))

/-- Renaming the ambient variables commutes with tying a recursive group. -/
theorem fixGroup_rename {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (ρ : ScopedSignature.Renaming Γ Δ) (η : Env D Δ) :
    fixGroup D rhs (rename D ρ η) =
      fixGroup D (fun i => (rhs i).comp (rename D (ρ.liftMany Ξ))) η := by
  apply fixGroup_congr
  intro ξ i
  simp only [ContinuousHom.comp_apply, rename_append]

/-- A strict continuous transport commuting with whole-group unfolding preserves
the simultaneous least fixed point. The target may use different sorts and bindings. -/
theorem fixGroup_fusion (E : T → PointedDomain) {Ξ : List S} {Ψ Λ : List T}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (i : Fin Ψ.length) → Env E (Ψ ++ Λ) →𝒄 E Ψ[i])
    (η : Env D Γ) (η' : Env E Λ) (transport : Env D Ξ →𝒄 Env E Ψ)
    (hbot : transport ⊥ = ⊥)
    (hstep : ∀ ξ, transport (ofFin D (fun i => rhs i (append D ξ η))) =
      ofFin E (fun i => rhs' i (append E (transport ξ) η'))) :
    transport (fixGroup D rhs η) = fixGroup E rhs' η' :=
  ContinuousHom.fix_fusion _ _ transport hbot hstep

/-- A strict family of continuous maps commuting with whole-group unfolding maps one
simultaneous least fixed point to the other. -/
theorem fixGroup_map (E : T → PointedDomain) (f : S → T) (t : ∀ a, D a →𝒄 E (f a))
    (ht : ∀ a, t a ⊥ = ⊥) {Ξ : List S} {Λ : List T}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (i : Fin (Ξ.map f).length) → Env E (Ξ.map f ++ Λ) →𝒄 E (Ξ.map f)[i])
    (η : Env D Γ) (η' : Env E Λ)
    (hstep : ∀ ξ, map D E f t (ofFin D (fun i => rhs i (append D ξ η))) =
      ofFin E (fun i => rhs' i (append E (map D E f t ξ) η'))) :
    map D E f t (fixGroup D rhs η) = fixGroup E rhs' η' :=
  fixGroup_fusion D E rhs rhs' η η' (map D E f t) (map_bot D E f t ht) hstep

end Env
end IPFunctor.ScopedDomain
