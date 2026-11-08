/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.FamilyMapSubstitution
public import PolyFun.IPFunctor.Scoped.Substitution
import PolyFun.IPFunctor.Scoped.FamilyMapCongr

/-!
# Two-level binding families

A stacked family is a value-level language whose parameter contexts are the contexts
`Θ : List K` of a type-level `ScopedSignature τ`, and whose sorts are type-level terms of one
kind `k₀`. A head is a *shape*, finite data with no types, together with *annotations*: an
environment of type-level terms, one per slot, each under its own type binders. Only the shape
decides the children and the type parameters each child binds, so substituting type parameters
leaves a head's children unchanged.

A head is *checked*: `Stacked.Op Θ s` consists of the annotated heads whose computed result
sort is `s` and whose annotations satisfy the side condition `WF`, which can carry, for
example, the evidence of a coercion between two types. The language supplies the binders,
child sorts and result sort of each shape as functions of its annotations, with one
substitution equation for each. This file derives:

* `toFamily`: the `ScopedFamily`. A child that binds no type parameter keeps its parent's
  value context exactly; a child below type binders weakens every ambient sort.
* `paramHom`: type-parameter substitution as a family `Hom`.
* `reindexAction` and `reindexAction_lawful`, so `subst_subst`, `map_subst` and the rest of
  the value-substitution algebra apply to every stacked family.
-/

public section

universe u v w x y

namespace IPFunctor.ScopedSignature

variable {K : Type u}

/-- Head shapes of a stacked family: finite data with no type annotations. -/
structure Heads (K : Type u) where
  /-- Head shapes. -/
  Shape : Type x
  /-- Children of a shape. -/
  Arg : Shape → Type y
  /-- Type parameters bound on entering a child, nearest first. -/
  tbind : (h : Shape) → Arg h → List K
  /-- Annotation slots: the type binders over each slot, and the slot's kind. -/
  slots : Shape → List (List K × K)

namespace Heads

variable (H : Heads.{u, x, y} K) (τ : ScopedSignature.{u, v, w} K)

/-- The annotations of a shape at parameter context `Θ`: an environment of slot terms, each
under the slot's own type binders. -/
abbrev Ann (h : H.Shape) (Θ : List K) :=
  Env (fun j : List K × K => τ.Term (j.1 ++ Θ) j.2) (H.slots h)

/-- An annotated head: a shape with its annotations. -/
abbrev Code (Θ : List K) := (h : H.Shape) × H.Ann τ h Θ

variable {H τ}

/-- Substitute type parameters in every annotation, protecting each slot's own binders. -/
@[expose] def Ann.subst {h : H.Shape} {Θ Θ' : List K} (θ : τ.Substitution Θ Θ')
    (a : H.Ann τ h Θ) : H.Ann τ h Θ' :=
  fun j x => (a j x).subst (Substitution.liftMany θ j.1)

/-- Successive substitutions of annotations compose. -/
theorem Ann.subst_subst {h : H.Shape} {Θ Θ' Θ'' : List K} (θ : τ.Substitution Θ Θ')
    (θ' : τ.Substitution Θ' Θ'') (a : H.Ann τ h Θ) :
    Ann.subst θ' (Ann.subst θ a) = Ann.subst (fun c x => (θ c x).subst θ') a := by
  funext j x
  simp only [Ann.subst, Term.subst_subst]
  congr 1
  funext c y
  exact (Substitution.liftMany_comp θ θ' j.1 y).symm

end Heads

/-- A two-level binding family over the type-level signature `τ`, with value sorts of kind
`k₀` and heads `H`. The language gives the value binders, child sorts and result sort of a
shape as functions of its annotations, a side condition `WF` on annotations, and one
substitution equation for each. -/
structure Stacked (τ : ScopedSignature.{u, v, w} K) (k₀ : K) (H : Heads.{u, x, y} K) where
  /-- Value variables bound in a child, nearest first. -/
  binders : {Θ : List K} → (h : H.Shape) → H.Ann τ h Θ → (p : H.Arg h) →
    List (τ.Term (H.tbind h p ++ Θ) k₀)
  /-- Result sort of a child. -/
  sort : {Θ : List K} → (h : H.Shape) → H.Ann τ h Θ → (p : H.Arg h) →
    τ.Term (H.tbind h p ++ Θ) k₀
  /-- Result sort of a head. -/
  result : {Θ : List K} → (h : H.Shape) → H.Ann τ h Θ → τ.Term Θ k₀
  /-- Side condition on annotations, such as the evidence of a coercion. -/
  WF : {Θ : List K} → (h : H.Shape) → H.Ann τ h Θ → Prop
  /-- Substitution commutes with the value binders of each child. -/
  binders_subst : ∀ {Θ Θ' : List K} (θ : τ.Substitution Θ Θ') (h : H.Shape)
    (a : H.Ann τ h Θ) (p : H.Arg h),
    (binders h a p).map (·.subst (Substitution.liftMany θ (H.tbind h p))) =
      binders h (Heads.Ann.subst θ a) p
  /-- Substitution commutes with the sort of each child. -/
  sort_subst : ∀ {Θ Θ' : List K} (θ : τ.Substitution Θ Θ') (h : H.Shape)
    (a : H.Ann τ h Θ) (p : H.Arg h),
    (sort h a p).subst (Substitution.liftMany θ (H.tbind h p)) = sort h (Heads.Ann.subst θ a) p
  /-- Substitution commutes with the result sort. -/
  result_subst : ∀ {Θ Θ' : List K} (θ : τ.Substitution Θ Θ') (h : H.Shape)
    (a : H.Ann τ h Θ), (result h a).subst θ = result h (Heads.Ann.subst θ a)
  /-- Substitution preserves the side condition. -/
  WF_subst : ∀ {Θ Θ' : List K} (θ : τ.Substitution Θ Θ') (h : H.Shape)
    (a : H.Ann τ h Θ), WF h a → WF h (Heads.Ann.subst θ a)

namespace Stacked

variable {τ : ScopedSignature.{u, v, w} K} {k₀ : K}

/-! ## Entering a block of type binders -/

/-- How the ambient value context enters below a block of type binders: kept exactly when the
block is empty, and weakened otherwise. -/
@[expose] def enter {Θ : List K} :
    (Ξ : List K) → ScopedFamily.Ambient (fun Θ => τ.Term Θ k₀) Θ (Ξ ++ Θ)
  | [] => .keep
  | k :: Ξ => .map (·.subst (Substitution.weakenMany (σ := τ) (k :: Ξ)))

@[simp] theorem enter_nil {Θ : List K} :
    (enter [] : ScopedFamily.Ambient (fun Θ => τ.Term Θ k₀) Θ ([] ++ Θ)) = .keep := rfl

/-- Substituting type parameters commutes with entering a block of type binders. -/
theorem enter_sort_subst {Θ Θ' : List K} (θ : τ.Substitution Θ Θ') (Ξ : List K)
    (s : τ.Term Θ k₀) :
    ((enter (k₀ := k₀) Ξ).sort s).subst (Substitution.liftMany θ Ξ) =
      (enter (k₀ := k₀) Ξ).sort (s.subst θ) := by
  cases Ξ with
  | nil => rfl
  | cons => exact Term.subst_weakenMany_liftMany θ _ s

variable {H : Heads.{u, x, y} K} (S : Stacked τ k₀ H)

/-! ## The family -/

/-- A checked head: its annotations give the result sort `s` and satisfy the side
condition. -/
abbrev Op (Θ : List K) (s : τ.Term Θ k₀) :=
  {c : H.Code τ Θ // S.result c.1 c.2 = s ∧ S.WF c.1 c.2}

/-- The binding family. Only type binders change the parameter context; a child below type
binders weakens the ambient sorts, and every other child keeps them. -/
@[expose] def toFamily : ScopedFamily (List K) (fun Θ => τ.Term Θ k₀) where
  Op Θ s := S.Op Θ s
  Arg o := H.Arg o.1.1
  world {Θ} {_} o p := H.tbind o.1.1 p ++ Θ
  ambient o p := enter (H.tbind o.1.1 p)
  binders o p := S.binders o.1.1 o.1.2 p
  sort o p := S.sort o.1.1 o.1.2 p

/-- A node whose result sort is computed from its head, so the check is definitional. -/
@[expose] def node {Θ : List K} {Γ : List (τ.Term Θ k₀)} (h : H.Shape) (a : H.Ann τ h Θ)
    (wf : S.WF h a)
    (args : (p : H.Arg h) → S.toFamily.Term (H.tbind h p ++ Θ)
      (S.binders h a p ++ (enter (k₀ := k₀) (H.tbind h p)).context Γ) (S.sort h a p)) :
    S.toFamily.Term Θ Γ (S.result h a) :=
  ScopedFamily.Term.node (σ := S.toFamily)
    (⟨⟨h, a⟩, rfl, wf⟩ : S.Op Θ (S.result h a)) args

/-- Substitute type parameters in a checked head. -/
@[expose] def Op.subst {Θ Θ' : List K} {s : τ.Term Θ k₀} (θ : τ.Substitution Θ Θ')
    (o : S.Op Θ s) : S.Op Θ' (s.subst θ) :=
  ⟨⟨o.1.1, Heads.Ann.subst θ o.1.2⟩, by rw [← S.result_subst, o.2.1], S.WF_subst θ _ _ o.2.2⟩

/-- Type-parameter substitution as a family homomorphism, from the per-shape equations. -/
@[expose] def paramHom : S.toFamily.Hom S.toFamily (fun Θ Θ' => τ.Substitution Θ Θ')
    (fun θ s => s.subst θ) where
  op := fun {_ _} θ {_} o => Op.subst S θ o
  arg := fun {_ _} _ {_} _ p => p
  next := fun {_ _} θ {_} o p => Substitution.liftMany θ (H.tbind o.1.1 p)
  binders := fun {_ _} θ {_} o p => S.binders_subst θ o.1.1 o.1.2 p
  reindex := fun {_ _} θ {_} o p b => enter_sort_subst θ (H.tbind o.1.1 p) b
  sort := fun {_ _} θ {_} o p => S.sort_subst θ o.1.1 o.1.2 p

/-! ## The reindexing action -/

/-- Move existing syntax below a block of type binders: unchanged for an empty block, and
weakened by `paramHom` otherwise. -/
@[expose] def enterTerm {Θ : List K} {Γ : List (τ.Term Θ k₀)} {b : τ.Term Θ k₀} :
    (Ξ : List K) → S.toFamily.Term Θ Γ b →
      S.toFamily.Term (Ξ ++ Θ) ((enter Ξ).context Γ) ((enter Ξ).sort b)
  | [], t => t
  | k :: Ξ, t => t.map S.paramHom (Substitution.weakenMany (k :: Ξ))

/-- Entering a child: keep the syntax, or weaken it below the child's type binders. -/
@[expose] def reindexAction : S.toFamily.ReindexAction :=
  fun {_ _} o p {_ _} t => S.enterTerm (H.tbind o.1.1 p) t

theorem op_heq {Θ : List K} {s₁ s₂ : τ.Term Θ k₀} (hs : s₁ = s₂) {o₁ : S.Op Θ s₁}
    {o₂ : S.Op Θ s₂} (hc : o₁.1 = o₂.1) : HEq o₁ o₂ := by
  subst hs
  exact heq_of_eq (Subtype.ext hc)

/-- Successive type-parameter substitutions compose on whole terms. -/
theorem map_map_heq {Θ Θ' Θ'' : List K} (θ : τ.Substitution Θ Θ') (θ' : τ.Substitution Θ' Θ'')
    {Γ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀} (t : S.toFamily.Term Θ Γ s) :
    HEq ((t.map S.paramHom θ).map S.paramHom θ') (t.map S.paramHom (θ'.comp θ)) := by
  apply (ScopedFamily.Term.cast_heq _ _ _).symm.trans
  apply (heq_of_eq (ScopedFamily.Term.map_map S.paramHom S.paramHom θ θ' t)).trans
  apply ScopedFamily.Term.map_congr (S.paramHom.comp S.paramHom) S.paramHom
    (fun {_ b c} μ ν => b = c ∧ HEq (μ.2.2.comp μ.2.1) ν) ?_ ?_ ?_ ?_ ?_ ⟨rfl, HEq.rfl⟩ t
  · intro _ _ _ _ _ hr
    exact hr.1
  · rintro _ _ _ μ _ ⟨rfl, hμ⟩
    cases eq_of_heq hμ
    exact heq_of_eq (funext fun s => Term.subst_subst s μ.2.1 μ.2.2)
  · rintro _ _ _ μ _ ⟨rfl, hμ⟩ _ o
    cases eq_of_heq hμ
    exact op_heq S (Term.subst_subst _ _ _)
      (Sigma.ext rfl (heq_of_eq (Heads.Ann.subst_subst _ _ _)))
  · intro _ _ _ _ _ _ _ _ _ _ he
    exact eq_of_heq he
  · rintro _ _ _ μ _ ⟨rfl, hμ⟩ _ o p q he
    cases eq_of_heq hμ
    cases eq_of_heq he
    refine ⟨rfl, heq_of_eq ?_⟩
    funext c x
    exact (Substitution.liftMany_comp μ.2.1 μ.2.2 _ x).symm

theorem enterTerm_var {Θ : List K} {Γ : List (τ.Term Θ k₀)} {b : τ.Term Θ k₀} (Ξ : List K)
    (x : ScopedVar Γ b) :
    S.enterTerm Ξ (ScopedFamily.Term.var x) =
      ScopedFamily.Term.var (σ := S.toFamily) ((enter Ξ).var x) := by
  cases Ξ <;> rfl

theorem enterTerm_rename {Θ : List K} {Γ Δ : List (τ.Term Θ k₀)} {b : τ.Term Θ k₀}
    (Ξ : List K) (ρ : Renaming Γ Δ) (t : S.toFamily.Term Θ Γ b) :
    S.enterTerm Ξ (t.rename ρ) =
      ScopedFamily.Term.rename (σ := S.toFamily) ((enter Ξ).mapRenaming ρ) (S.enterTerm Ξ t) := by
  cases Ξ with
  | nil => rfl
  | cons => exact ScopedFamily.Term.map_rename S.paramHom _ ρ t

/-- Entering a block of type binders commutes with type-parameter substitution. -/
theorem enterTerm_map_heq {Θ Θ' : List K} {Γ : List (τ.Term Θ k₀)} {b : τ.Term Θ k₀}
    (Ξ : List K) (θ : τ.Substitution Θ Θ') (t : S.toFamily.Term Θ Γ b) :
    HEq ((S.enterTerm Ξ t).map S.paramHom (Substitution.liftMany θ Ξ))
      (S.enterTerm Ξ (t.map S.paramHom θ)) := by
  cases Ξ with
  | nil => rfl
  | cons k Ξ =>
    change HEq ((t.map S.paramHom (Substitution.weakenMany (k :: Ξ))).map S.paramHom
        (Substitution.liftMany θ (k :: Ξ)))
      ((t.map S.paramHom θ).map S.paramHom (Substitution.weakenMany (k :: Ξ)))
    apply (map_map_heq S _ _ t).trans
    apply HEq.trans ?_ (map_map_heq S _ _ t).symm
    have h : (Substitution.liftMany θ (k :: Ξ)).comp (Substitution.weakenMany (σ := τ) (k :: Ξ)) =
        (Substitution.weakenMany (k :: Ξ)).comp θ := by
      funext c x
      exact Substitution.liftMany_weakenMany θ _ x
    rw [h]

/-- Entering a child commutes with type-parameter substitution. -/
theorem paramHom_preservesReindex :
    S.paramHom.PreservesReindex S.reindexAction S.reindexAction :=
  fun {_ _} θ {_} o p {_ _} t => S.enterTerm_map_heq (H.tbind o.1.1 p) θ t

theorem paramHom_preservesSubstitution :
    S.paramHom.PreservesSubstitution S.reindexAction S.reindexAction :=
  ScopedFamily.Hom.PreservesReindex.preservesSubstitution S.paramHom S.reindexAction
    S.reindexAction S.paramHom_preservesReindex

theorem enterTerm_subst {Θ : List K} {Γ Δ : List (τ.Term Θ k₀)} {b : τ.Term Θ k₀}
    (Ξ : List K) (θ : S.toFamily.Substitution Γ Δ) (t : S.toFamily.Term Θ Γ b) :
    S.enterTerm Ξ (t.subst S.reindexAction θ) =
      (S.enterTerm Ξ t).subst S.reindexAction
        ((enter Ξ).env fun _ x => S.enterTerm Ξ (θ _ x)) := by
  cases Ξ with
  | nil => rfl
  | cons =>
    exact ScopedFamily.Term.map_subst S.paramHom S.reindexAction S.reindexAction
      S.paramHom_preservesSubstitution _ θ t

/-- The derived action satisfies the whole value-substitution algebra. -/
theorem reindexAction_lawful : ScopedFamily.ReindexAction.Lawful S.toFamily S.reindexAction where
  vars o p _ _ x := S.enterTerm_var (H.tbind o.1.1 p) x
  rename o p _ _ _ ρ t := S.enterTerm_rename (H.tbind o.1.1 p) ρ t
  subst o p _ _ _ θ t := S.enterTerm_subst (H.tbind o.1.1 p) θ t

/-- Value substitutions compose in every stacked family. -/
theorem subst_subst {Θ : List K} {Γ Δ Λ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀}
    (t : S.toFamily.Term Θ Γ s) (θ : S.toFamily.Substitution Γ Δ)
    (θ' : S.toFamily.Substitution Δ Λ) :
    (t.subst S.reindexAction θ).subst S.reindexAction θ' =
      t.subst S.reindexAction (fun a x => (θ a x).subst S.reindexAction θ') :=
  ScopedFamily.Term.subst_subst S.reindexAction S.reindexAction_lawful t θ θ'

/-- Type-parameter substitution and value substitution commute in every stacked family. -/
theorem map_subst {Θ Θ' : List K} {Γ Δ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀}
    (μ : τ.Substitution Θ Θ') (θ : S.toFamily.Substitution Γ Δ) (t : S.toFamily.Term Θ Γ s) :
    (t.subst S.reindexAction θ).map S.paramHom μ =
      (t.map S.paramHom μ).subst S.reindexAction (θ.map S.paramHom μ) :=
  ScopedFamily.Term.map_subst S.paramHom S.reindexAction S.reindexAction
    S.paramHom_preservesSubstitution μ θ t

/-- Closing a body commutes with entering its nearest value binder. -/
theorem substOne_subst_lift {Θ : List K} {Γ Δ : List (τ.Term Θ k₀)} {a b : τ.Term Θ k₀}
    (body : S.toFamily.Term Θ (a :: Γ) b) (θ : S.toFamily.Substitution Γ Δ)
    (value : S.toFamily.Term Θ Δ a) :
    (body.subst S.reindexAction (ScopedFamily.Substitution.lift θ a)).substOne
        S.reindexAction value =
      body.subst S.reindexAction (Env.cons value θ) :=
  ScopedFamily.Term.substOne_subst_lift S.reindexAction S.reindexAction_lawful body θ value

end Stacked

end IPFunctor.ScopedSignature
