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

When every value type is an omega-complete partial order, environments are ordered
pointwise, and extension, append, renaming and positional maps are continuous. A
finite recursive group of bindings denotes one simultaneous least fixed point.

Lookup uses binding positions, so mapping environments along a sort map permits
distinct source sorts to become equal, as happens when substituting type parameters.
-/

public section

open OmegaCompletePartialOrder

universe u v w z z' z''

namespace IPFunctor.ScopedSignature.Env

variable {S : Type u} {T : Type v} {V : S → Type z} [∀ a, OmegaCompletePartialOrder (V a)]
  {Γ Δ : List S}

/-- Reading an environment through a renaming is continuous. -/
@[expose] noncomputable def renameContinuous (ρ : Renaming Γ Δ) : Env V Δ →𝒄 Env V Γ :=
  .ofFun (fun η a x => η a (ρ a x)) (by fun_prop)

@[simp] theorem renameContinuous_apply (ρ : Renaming Γ Δ) (η : Env V Δ) :
    renameContinuous ρ η = rename ρ η := rfl

theorem renameContinuous_apply_apply (ρ : Renaming Γ Δ) (η : Env V Δ) {a : S}
    (x : ScopedVar Γ a) : renameContinuous ρ η a x = η a (ρ a x) := rfl

theorem renameContinuous_id (η : Env V Γ) : renameContinuous (fun _ x => x) η = η := rfl

/-- Reading through two renamings reads through their composite. -/
theorem renameContinuous_renameContinuous {Θ : List S} (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ)
    (η : Env V Θ) :
    renameContinuous ρ (renameContinuous τ η) = renameContinuous (rename ρ τ) η := rfl

/-- Protecting a fresh variable preserves its value. -/
theorem renameContinuous_cons (ρ : Renaming Γ Δ) {a : S} (x : V a) (η : Env V Δ) :
    renameContinuous (ρ.lift a) (cons x η) = cons x (renameContinuous ρ η) :=
  rename_cons ρ x η

/-- The fresh block is unchanged when the ambient environment is renamed. -/
theorem renameContinuous_append (ρ : Renaming Γ Δ) {Ξ : List S} (ξ : Env V Ξ) (η : Env V Δ) :
    renameContinuous (ρ.liftMany Ξ) (append ξ η) = append ξ (renameContinuous ρ η) :=
  rename_append ρ ξ η

/-- Assembling environments is continuous in all their components. -/
@[expose] noncomputable def ofFinContinuous {Ξ : List S} :
    ((i : Fin Ξ.length) → V Ξ[i]) →𝒄 Env V Ξ := .ofFun ofFin (by
  apply ωScottContinuous.of_apply₂
  intro a
  apply ωScottContinuous.of_apply₂
  intro x
  induction x with
  | zero => exact ωScottContinuous.apply 0
  | succ x ih => exact ih.comp (by fun_prop))

/-- Adding one binding is jointly continuous. -/
@[expose] noncomputable def consContinuous {a : S} :
    (V a × Env V Γ) →𝒄 Env V (a :: Γ) := .ofFun (fun p => cons p.1 p.2) (by
  apply ωScottContinuous.of_apply₂
  intro b
  apply ωScottContinuous.of_apply₂
  intro x
  cases x <;> simp only [cons] <;> fun_prop)

@[simp] theorem consContinuous_apply {a : S} (p : V a × Env V Γ) :
    consContinuous p = cons p.1 p.2 := rfl

/-- Adding a binding is continuous in the new value and the environment together. -/
@[fun_prop] theorem ωScottContinuous_cons {α : Type w} [OmegaCompletePartialOrder α] {a : S}
    {f : α → V a} {g : α → Env V Γ} (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    ωScottContinuous fun t => cons (f t) (g t) :=
  consContinuous.ωScottContinuous.comp (Prod.ωScottContinuous.prodMk hf hg)

/-- A one-variable environment is continuous in its value. -/
@[fun_prop] theorem ωScottContinuous_single {α : Type w} [OmegaCompletePartialOrder α] {a : S}
    {f : α → V a} (hf : ωScottContinuous f) : ωScottContinuous fun t => single (f t) := by
  simp only [single_eq_cons]
  fun_prop

/-- A meaning in a one-variable environment, as a continuous function of that variable.
This is the semantic counterpart of a constructor argument binding one variable. -/
@[expose] noncomputable def bindOne {a : S} {E : Type w} [OmegaCompletePartialOrder E] :
    (Env V [a] →𝒄 E) →𝒄 (V a →𝒄 E) :=
  .ofFun (fun f => f.comp (.ofFun single (by fun_prop))) (by
    apply ContinuousHom.ωScottContinuous_of_apply
    intro x
    change ωScottContinuous fun f : Env V [a] →𝒄 E => f (single x)
    fun_prop)

@[simp] theorem bindOne_apply {a : S} {E : Type w} [OmegaCompletePartialOrder E]
    (f : Env V [a] →𝒄 E) (x : V a) : bindOne f x = f (cons x empty) := rfl

/-- Appending a finite block of bindings is jointly continuous. -/
@[expose] noncomputable def appendContinuous {Ξ : List S} :
    (Env V Ξ × Env V Γ) →𝒄 Env V (Ξ ++ Γ) := .ofFun (fun p => append p.1 p.2) (by
  induction Ξ with
  | nil => exact Prod.ωScottContinuous_snd
  | cons a Ξ ih =>
      change ωScottContinuous (fun p : Env V (a :: Ξ) × Env V Γ => consContinuous
        (p.1 a .zero, append (fun b v => p.1 b (.succ v)) p.2))
      apply consContinuous.ωScottContinuous.comp
      apply Prod.ωScottContinuous.prodMk
      · fun_prop
      · have h : ωScottContinuous (fun p : Env V (a :: Ξ) × Env V Γ =>
            (((fun b v => p.1 b (.succ v)) : Env V Ξ), p.2)) := by fun_prop
        exact ih.comp h)

/-! ## Positional maps -/

variable {W : T → Type z'} [∀ b, OmegaCompletePartialOrder (W b)]

/-- Apply a family of continuous maps at every binding position. The sort map need
not be injective, and the two families of values may lie in different universes. -/
@[expose] noncomputable def map (f : S → T) (t : ∀ a, V a →𝒄 W (f a)) :
    Env V Γ →𝒄 Env W (Γ.map f) :=
  .ofFun (fun η => reindex f fun a x => t a (η a x)) (by
      apply ωScottContinuous.of_apply₂
      intro b
      apply ωScottContinuous.of_apply₂
      intro x
      induction x using ScopedVar.map_inductionOn with
      | h a x =>
          simp only [reindex_map]
          fun_prop)

@[simp] theorem map_apply (f : S → T) (t : ∀ a, V a →𝒄 W (f a)) (η : Env V Γ) {a : S}
    (x : ScopedVar Γ a) : map f t η (f a) (x.map f) = t a (η a x) :=
  reindex_map f (V := W) _ x

/-- The identity family at the identity sort map performs only context normalization. -/
theorem map_id (η : Env V Γ) :
    map id (fun _ => ContinuousHom.id) η = (List.map_id Γ).symm ▸ η := by
  funext a x
  induction x using ScopedVar.map_inductionOn id with
  | h a x =>
      rw [map_apply, ScopedVar.map_id, cast_apply]
      rfl

/-- Mapping retains the nearest binding and maps the older positions. -/
theorem map_cons (f : S → T) (t : ∀ a, V a →𝒄 W (f a)) {a : S} (x : V a) (η : Env V Γ) :
    map f t (cons x η) = cons (t a x) (map f t η) := by
  funext b v
  cases v <;> rfl

/-- Changing sorts commutes with changing binding positions, even for noninjective maps. -/
theorem map_rename (f : S → T) (t : ∀ a, V a →𝒄 W (f a)) (ρ : Renaming Γ Δ) (η : Env V Δ) :
    map f t (rename ρ η) = rename (Renaming.map f ρ) (map f t η) :=
  reindex_rename f ρ fun a x => t a (η a x)

/-- Changing sorts commutes with continuously changing binding positions. -/
theorem map_renameContinuous (f : S → T) (t : ∀ a, V a →𝒄 W (f a)) (ρ : Renaming Γ Δ)
    (η : Env V Δ) :
    map f t (renameContinuous ρ η) = renameContinuous (Renaming.map f ρ) (map f t η) :=
  map_rename f t ρ η

/-- Consecutive maps compose at each original binding position. The two contexts are
equal only propositionally, so the law compares lookups; `ScopedVar.map_inductionOn`
shows that these positions exhaust both contexts. -/
theorem map_map {U : Type w} {X : U → Type z''} [∀ c, OmegaCompletePartialOrder (X c)]
    (f : S → T) (g : T → U) (t : ∀ a, V a →𝒄 W (f a)) (u : ∀ b, W b →𝒄 X (g b))
    (η : Env V Γ) {a : S} (x : ScopedVar Γ a) :
    map g u (map f t η) (g (f a)) ((x.map f).map g) =
      map (g ∘ f) (fun a => (u (f a)).comp (t a)) η (g (f a)) (x.map (g ∘ f)) := by
  rw [map_apply, map_apply]
  exact (map_apply (g ∘ f) (fun a => (u (f a)).comp (t a)) η x).symm

/-- A strict family maps the empty information state to itself. -/
theorem map_bot [∀ a, OrderBot (V a)] [∀ b, OrderBot (W b)]
    (f : S → T) (t : ∀ a, V a →𝒄 W (f a)) (ht : ∀ a, t a ⊥ = ⊥) :
    map f t (⊥ : Env V Γ) = ⊥ := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => simp only [map_apply, Pi.bot_apply, ht]

/-- Map binding positions along an equation of their pointed domains. -/
@[expose] noncomputable def transport {D : S → PointedDomain.{z}} (E : T → PointedDomain.{z})
    (f : S → T) (h : ∀ a, E (f a) = D a) :
    Env (fun a => D a) Γ →𝒄 Env (fun b => E b) (Γ.map f) :=
  map f fun a => PointedDomain.cast (h a).symm

/-! ## Recursive groups -/

variable [∀ a, OrderBot (V a)]

/-- Tie a finite, possibly heterogeneous recursive group by one least fixed point.
Every right-hand side sees the entire group and the ambient environment. -/
@[expose] noncomputable def fixGroup {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env V (Ξ ++ Γ) →𝒄 V Ξ[i]) :
    Env V Γ →𝒄 Env V Ξ :=
  ContinuousHom.fixContinuous.comp (.ofFun (fun η =>
    ContinuousHom.ofFun (fun ξ => ofFinContinuous
      (fun i => rhs i (appendContinuous (ξ, η))))))

/-- Unfold all declarations in a recursive group simultaneously. -/
theorem fixGroup_unfold {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env V (Ξ ++ Γ) →𝒄 V Ξ[i]) (η : Env V Γ) :
    fixGroup rhs η = ofFin (fun i => rhs i (append (fixGroup rhs η) η)) :=
  (ContinuousHom.map_fix (ContinuousHom.ofFun (fun ξ => ofFinContinuous
    (fun i => rhs i (appendContinuous (ξ, η)))))).symm

/-- A group denotes the least simultaneous prefixed point. -/
theorem fixGroup_le {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env V (Ξ ++ Γ) →𝒄 V Ξ[i]) (η : Env V Γ) (ξ : Env V Ξ)
    (h : ofFin (fun i => rhs i (append ξ η)) ≤ ξ) : fixGroup rhs η ≤ ξ :=
  ContinuousHom.fix_le _ h

/-- Equal group transformers have equal simultaneous least fixed points.
The ambient environments may differ; the whole recursive block is compared at once. -/
theorem fixGroup_congr {Θ Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env V (Ξ ++ Γ) →𝒄 V Ξ[i])
    (rhs' : (i : Fin Ξ.length) → Env V (Ξ ++ Θ) →𝒄 V Ξ[i])
    (η : Env V Γ) (η' : Env V Θ)
    (h : ∀ ξ i, rhs i (append ξ η) = rhs' i (append ξ η')) :
    fixGroup rhs η = fixGroup rhs' η' := by
  change ContinuousHom.fix _ = ContinuousHom.fix _
  congr 1
  apply ContinuousHom.ext
  intro ξ
  exact congrArg ofFin (funext (h ξ))

/-- Renaming the ambient variables commutes with tying a recursive group. -/
theorem fixGroup_rename {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env V (Ξ ++ Γ) →𝒄 V Ξ[i])
    (ρ : Renaming Γ Δ) (η : Env V Δ) :
    fixGroup rhs (rename ρ η) =
      fixGroup (fun i => (rhs i).comp (renameContinuous (ρ.liftMany Ξ))) η := by
  apply fixGroup_congr
  intro ξ i
  simp only [ContinuousHom.comp_apply, renameContinuous_apply, rename_append]

/-- Continuously renaming the ambient variables commutes with tying a recursive group. -/
theorem fixGroup_renameContinuous {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env V (Ξ ++ Γ) →𝒄 V Ξ[i])
    (ρ : Renaming Γ Δ) (η : Env V Δ) :
    fixGroup rhs (renameContinuous ρ η) =
      fixGroup (fun i => (rhs i).comp (renameContinuous (ρ.liftMany Ξ))) η :=
  fixGroup_rename rhs ρ η

variable [∀ b, OrderBot (W b)]

/-- A strict continuous transport commuting with whole-group unfolding preserves
the simultaneous least fixed point. The target may use different sorts and bindings. -/
theorem fixGroup_fusion {Ξ : List S} {Ψ Λ : List T}
    (rhs : (i : Fin Ξ.length) → Env V (Ξ ++ Γ) →𝒄 V Ξ[i])
    (rhs' : (i : Fin Ψ.length) → Env W (Ψ ++ Λ) →𝒄 W Ψ[i])
    (η : Env V Γ) (η' : Env W Λ) (φ : Env V Ξ →𝒄 Env W Ψ)
    (hbot : φ ⊥ = ⊥)
    (hstep : ∀ ξ, φ (ofFin (fun i => rhs i (append ξ η))) =
      ofFin (fun i => rhs' i (append (φ ξ) η'))) :
    φ (fixGroup rhs η) = fixGroup rhs' η' :=
  ContinuousHom.fix_fusion _ _ φ hbot hstep

/-- A strict family of continuous maps commuting with whole-group unfolding maps one
simultaneous least fixed point to the other. -/
theorem fixGroup_map (f : S → T) (t : ∀ a, V a →𝒄 W (f a))
    (ht : ∀ a, t a ⊥ = ⊥) {Ξ : List S} {Λ : List T}
    (rhs : (i : Fin Ξ.length) → Env V (Ξ ++ Γ) →𝒄 V Ξ[i])
    (rhs' : (i : Fin (Ξ.map f).length) → Env W (Ξ.map f ++ Λ) →𝒄 W (Ξ.map f)[i])
    (η : Env V Γ) (η' : Env W Λ)
    (hstep : ∀ ξ, map f t (ofFin (fun i => rhs i (append ξ η))) =
      ofFin (fun i => rhs' i (append (map f t ξ) η'))) :
    map f t (fixGroup rhs η) = fixGroup rhs' η' :=
  fixGroup_fusion rhs rhs' η η' (map f t) (map_bot f t ht) hstep

end IPFunctor.ScopedSignature.Env

/-! ## Deprecated aliases -/

namespace IPFunctor.ScopedDomain

/-- One suspended semantic value for each binding position of a family of pointed domains. -/
@[deprecated ScopedSignature.Env +typeChanged (since := "2026-11-07")]
abbrev Env {S : Type u} (D : S → PointedDomain.{z}) (Γ : List S) : Type (max u z) :=
  ScopedSignature.Env (fun a => D a) Γ

namespace Env

@[deprecated (since := "2026-11-07")] alias rename := ScopedSignature.Env.renameContinuous
@[deprecated (since := "2026-11-07")] alias rename_apply :=
  ScopedSignature.Env.renameContinuous_apply_apply
@[deprecated (since := "2026-11-07")] alias rename_id := ScopedSignature.Env.renameContinuous_id
@[deprecated (since := "2026-11-07")] alias rename_rename :=
  ScopedSignature.Env.renameContinuous_renameContinuous
@[deprecated (since := "2026-11-07")] alias cast_apply := ScopedSignature.Env.cast_apply
@[deprecated (since := "2026-11-07")] alias ofFin := ScopedSignature.Env.ofFin
@[deprecated (since := "2026-11-07")] alias ofFinContinuous :=
  ScopedSignature.Env.ofFinContinuous
@[deprecated (since := "2026-11-07")] alias empty := ScopedSignature.Env.empty
@[deprecated (since := "2026-11-07")] alias cons := ScopedSignature.Env.cons
@[deprecated (since := "2026-11-07")] alias append := ScopedSignature.Env.append
@[deprecated (since := "2026-11-07")] alias rename_cons :=
  ScopedSignature.Env.renameContinuous_cons
@[deprecated (since := "2026-11-07")] alias rename_append :=
  ScopedSignature.Env.renameContinuous_append
@[deprecated (since := "2026-11-07")] alias consContinuous := ScopedSignature.Env.consContinuous
@[deprecated (since := "2026-11-07")] alias appendContinuous :=
  ScopedSignature.Env.appendContinuous
@[deprecated (since := "2026-11-07")] alias map := ScopedSignature.Env.map
@[deprecated (since := "2026-11-07")] alias map_apply := ScopedSignature.Env.map_apply
@[deprecated (since := "2026-11-07")] alias map_id := ScopedSignature.Env.map_id
@[deprecated (since := "2026-11-07")] alias map_cons := ScopedSignature.Env.map_cons
@[deprecated (since := "2026-11-07")] alias map_rename :=
  ScopedSignature.Env.map_renameContinuous
@[deprecated (since := "2026-11-07")] alias map_map := ScopedSignature.Env.map_map
@[deprecated (since := "2026-11-07")] alias map_bot := ScopedSignature.Env.map_bot
@[deprecated (since := "2026-11-07")] alias reindex := ScopedSignature.Env.transport
@[deprecated (since := "2026-11-07")] alias fixGroup := ScopedSignature.Env.fixGroup
@[deprecated (since := "2026-11-07")] alias fixGroup_unfold := ScopedSignature.Env.fixGroup_unfold
@[deprecated (since := "2026-11-07")] alias fixGroup_le := ScopedSignature.Env.fixGroup_le
@[deprecated (since := "2026-11-07")] alias fixGroup_congr := ScopedSignature.Env.fixGroup_congr
@[deprecated (since := "2026-11-07")] alias fixGroup_rename :=
  ScopedSignature.Env.fixGroup_renameContinuous
@[deprecated (since := "2026-11-07")] alias fixGroup_fusion := ScopedSignature.Env.fixGroup_fusion
@[deprecated (since := "2026-11-07")] alias fixGroup_map := ScopedSignature.Env.fixGroup_map

end Env

end IPFunctor.ScopedDomain
