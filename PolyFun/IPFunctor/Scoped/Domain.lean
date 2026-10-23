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

Lookup uses binding positions. Reindexing therefore permits distinct source
sorts to become equal, as happens when substituting type parameters.
-/

public section

open OmegaCompletePartialOrder

namespace IPFunctor.ScopedDomain

variable {S T : Type*} {D : S → PointedDomain} {Γ Δ : List S}

/-- One suspended semantic value for each binding position. -/
abbrev Env (D : S → PointedDomain) (Γ : List S) := ∀ a, ScopedVar Γ a → D a

namespace Env

/-- Read an environment along a map of binding positions. -/
@[expose] noncomputable def rename (ρ : ScopedSignature.Renaming Γ Δ) :
    Env D Δ →𝒄 Env D Γ := .ofFun (fun η a x => η a (ρ x)) (by fun_prop)

@[simp] theorem rename_apply (ρ : ScopedSignature.Renaming Γ Δ)
    (η : Env D Δ) {a : S} (x : ScopedVar Γ a) : rename ρ η a x = η a (ρ x) := rfl

@[simp] theorem rename_id (η : Env D Γ) : rename (fun x => x) η = η := rfl

/-- Environment lookup reverses composition of variable maps. -/
theorem rename_rename {Θ : List S} (ρ : ScopedSignature.Renaming Γ Δ)
    (τ : ScopedSignature.Renaming Δ Θ) (η : Env D Θ) :
    rename ρ (rename τ η) = rename (fun x => τ (ρ x)) η := rfl

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
    ((i : Fin Ξ.length) → D Ξ[i]) →𝒄 Env D Ξ := .ofFun (ofFin) (by
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

@[simp] theorem cons_zero {a : S} (x : D a) (η : Env D Γ) : cons x η a .zero = x := rfl

@[simp] theorem cons_succ {a b : S} (x : D a) (η : Env D Γ) (v : ScopedVar Γ b) :
    cons x η b (.succ v) = η b v := rfl

/-- Extend an environment with a whole block of bindings. -/
@[expose] def append : {Ξ : List S} → Env D Ξ → Env D Γ → Env D (Ξ ++ Γ)
  | [], _, η => η
  | a :: _, ξ, η => cons (ξ a .zero) (append (fun b v => ξ b (.succ v)) η)

/-- Protecting a fresh variable preserves its value under environment lookup. -/
theorem rename_cons (ρ : ScopedSignature.Renaming Γ Δ) {a : S}
    (x : D a) (η : Env D Δ) :
    rename (ρ.lift a) (cons x η) = cons x (rename ρ η) := by
  funext b v
  cases v <;> rfl

/-- The fresh block is unchanged when the ambient environment is renamed. -/
theorem rename_append (ρ : ScopedSignature.Renaming Γ Δ) {Ξ : List S}
    (ξ : Env D Ξ) (η : Env D Δ) :
    rename (ρ.liftMany Ξ) (append ξ η) = append ξ (rename ρ η) := by
  induction Ξ with
  | nil => rfl
  | cons a Ξ ih =>
      change rename (ScopedSignature.Renaming.lift (ρ.liftMany Ξ) a) (cons _ _) = _
      rw [rename_cons, ih]
      rfl

/-- Adding one binding is jointly continuous. -/
@[expose] noncomputable def consContinuous {a : S} :
    (D a × Env D Γ) →𝒄 Env D (a :: Γ) := .ofFun (fun p => cons p.1 p.2) (by
  apply ωScottContinuous.of_apply₂
  intro b
  apply ωScottContinuous.of_apply₂
  intro x
  cases x <;> simp only [cons] <;> fun_prop)

@[simp] theorem consContinuous_apply {a : S} (p : D a × Env D Γ) :
    consContinuous p = cons p.1 p.2 := rfl

/-- Appending a finite block of bindings is jointly continuous. -/
@[expose] noncomputable def appendContinuous {Ξ : List S} :
    (Env D Ξ × Env D Γ) →𝒄 Env D (Ξ ++ Γ) := .ofFun (fun p => append p.1 p.2) (by
  induction Ξ with
  | nil => exact Prod.ωScottContinuous_snd
  | cons a Ξ ih =>
      change ωScottContinuous (fun p : Env D (a :: Ξ) × Env D Γ => consContinuous
        (p.1 a .zero, append (fun b v => p.1 b (.succ v)) p.2))
      apply (consContinuous).ωScottContinuous.comp
      apply Prod.ωScottContinuous.prodMk
      · fun_prop
      · have h : ωScottContinuous (fun p : Env D (a :: Ξ) × Env D Γ =>
            (((fun b v => p.1 b (.succ v)) : Env D Ξ), p.2)) := by fun_prop
        exact ih.comp h)

/-- Reindex binding positions while transporting their domains. -/
@[expose] noncomputable def reindex (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) : Env D Γ →𝒄 Env E (Γ.map f) :=
  .ofFun (fun η _ x => ScopedVar.mapLookup f (V := fun b => E b)
    (fun {a} v => PointedDomain.cast (h a).symm (η a v)) x) (by
      apply ωScottContinuous.of_apply₂
      intro b
      apply ωScottContinuous.of_apply₂
      intro x
      induction x using ScopedVar.map_inductionOn with
      | h a x =>
          simp only [ScopedVar.mapLookup_map]
          fun_prop)

@[simp] theorem reindex_map (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) (η : Env D Γ) {a : S} (x : ScopedVar Γ a) :
    reindex E f h η (f a) (x.map f) = PointedDomain.cast (h a).symm (η a x) :=
  ScopedVar.mapLookup_map f (V := fun b => E b) _ x

/-- Reindexing by identity performs only context normalization. -/
theorem reindex_id (η : Env D Γ) :
    reindex D id (fun _ => rfl) η = (List.map_id Γ).symm ▸ η := by
  funext a x
  induction x using ScopedVar.map_inductionOn id with
  | h a x =>
      rw [reindex_map, ScopedVar.map_id, cast_apply]
      rfl

/-- Transport retains the nearest binding and reindexes the older positions. -/
theorem reindex_cons (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) {a : S} (x : D a) (η : Env D Γ) :
    reindex E f h (cons x η) =
      cons (PointedDomain.cast (h a).symm x) (reindex E f h η) := by
  funext b v
  cases v <;> rfl

/-- Changing sorts commutes with changing binding positions, even for noninjective maps. -/
theorem reindex_rename (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) (ρ : ScopedSignature.Renaming Γ Δ) (η : Env D Δ) :
    reindex E f h (rename ρ η) =
      rename (ScopedSignature.Renaming.map f ρ) (reindex E f h η) := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => simp only [reindex_map, rename_apply, ScopedSignature.Renaming.map_apply]

/-- Consecutive environment transports compose, retaining each binding position. -/
theorem reindex_reindex {U : Type*} (E : T → PointedDomain) (F : U → PointedDomain)
    (f : S → T) (g : T → U) (h : ∀ a, E (f a) = D a) (k : ∀ a, F (g a) = E a)
    (η : Env D Γ) :
    (List.map_map ▸ reindex F g k (reindex E f h η)) =
      reindex F (g ∘ f) (fun a => (k (f a)).trans (h a)) η := by
  funext b x
  induction x using ScopedVar.map_inductionOn (g ∘ f) with
  | h a x =>
      rw [← ScopedVar.map_map f g x, cast_apply]
      simp only [ScopedVar.map_map, Function.comp_apply, reindex_map,
        PointedDomain.cast_cast]
      exact (reindex_map F (g ∘ f) _ η x).symm

/-- Environment transport maps the empty information state to itself. -/
@[simp] theorem reindex_bot (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) : reindex E f h (⊥ : Env D Γ) = ⊥ := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => simp only [reindex_map, Pi.bot_apply, PointedDomain.cast_bot]

/-- Tie a finite, possibly heterogeneous recursive group by one least fixed point.
Every right-hand side sees the entire group and the ambient environment. -/
@[expose] noncomputable def fixGroup {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i]) :
    Env D Γ →𝒄 Env D Ξ :=
  ContinuousHom.fixContinuous.comp (.ofFun (fun η =>
    ContinuousHom.ofFun (fun ξ => ofFinContinuous
      (fun i => rhs i (appendContinuous (ξ, η))))))

/-- Unfold all declarations in a recursive group simultaneously. -/
theorem fixGroup_unfold {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i]) (η : Env D Γ) :
    fixGroup rhs η = ofFin (fun i => rhs i (append (fixGroup rhs η) η)) :=
  (ContinuousHom.map_fix (ContinuousHom.ofFun (fun ξ => ofFinContinuous
    (fun i => rhs i (appendContinuous (ξ, η)))))).symm

/-- A group denotes the least simultaneous prefixed point. -/
theorem fixGroup_le {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i]) (η : Env D Γ) (ξ : Env D Ξ)
    (h : ofFin (fun i => rhs i (append ξ η)) ≤ ξ) : fixGroup rhs η ≤ ξ :=
  ContinuousHom.fix_le _ h

/-- Equal group transformers have equal simultaneous least fixed points.
The ambient environments may differ; the whole recursive block is compared at once. -/
theorem fixGroup_congr {Θ Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (i : Fin Ξ.length) → Env D (Ξ ++ Θ) →𝒄 D Ξ[i])
    (η : Env D Γ) (η' : Env D Θ)
    (h : ∀ ξ i, rhs i (append ξ η) = rhs' i (append ξ η')) :
    fixGroup rhs η = fixGroup rhs' η' := by
  change ContinuousHom.fix _ = ContinuousHom.fix _
  congr 1
  apply ContinuousHom.ext
  intro ξ
  exact congrArg (ofFin) (funext (h ξ))

/-- Renaming the ambient variables commutes with tying a recursive group. -/
theorem fixGroup_rename {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (ρ : ScopedSignature.Renaming Γ Δ) (η : Env D Δ) :
    fixGroup rhs (rename ρ η) =
      fixGroup (fun i => (rhs i).comp (rename (ρ.liftMany Ξ))) η := by
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
    (hstep : ∀ ξ, transport (ofFin (fun i => rhs i (append ξ η))) =
      ofFin (fun i => rhs' i (append (transport ξ) η'))) :
    transport (fixGroup rhs η) = fixGroup rhs' η' :=
  ContinuousHom.fix_fusion _ _ transport hbot hstep

end Env
end IPFunctor.ScopedDomain
