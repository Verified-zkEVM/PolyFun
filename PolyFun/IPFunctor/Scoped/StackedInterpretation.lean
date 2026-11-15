/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Stacked
public import PolyFun.IPFunctor.Scoped.Domain
public import PolyFun.IPFunctor.Scoped.EnvRelation
public import PolyFun.IPFunctor.Scoped.Interpretation

/-!
# Interpretations of two-level binding families

A model of a stacked family interprets its type level (`tyAlg`). It gives value-level typing
rules as functions of *evaluated* annotations (`bindersV`, `sortV`, `resultV`) and a
value-level side condition `WFV`. One coherence equation per rule relates the value-level
typing to the syntactic one, in the type-level meanings `Den`. A language whose coercions
change a type to one with the same carrier states that carrier equation in `WFV`, and its
interpretation of the coercion casts there.

The two kinds of interpretation follow the signature-level names. An ordinary
`Model.Interp V` and a continuous `Model.DomainInterp D` see a head only through its
evaluated annotations. They receive each child as a function, respectively a continuous
function, of the child's type arguments and fresh value binders. `Model.denote` and
`Model.denoteDomain` fold them at every type assignment. Because heads are seen only through
their evaluated annotations:

* `denoteDomain_map`: substituting type parameters in the syntax commutes with the continuous
  meaning, for every interpretation, with no obligation per head;
* `denoteDomain_related`: a continuous and an ordinary interpretation that relate their
  results at every evaluated head give related meanings for every term, at every type
  assignment, in environments related by `Env.LiftRel`.

Both folds are exposed, so a meaning computes definitionally on a concrete term.
`denote_stackedNode` and `denoteDomain_stackedNode` state one step of that computation; a large
meaning is better computed by rewriting with them than by one `rfl`.
-/

public section

open OmegaCompletePartialOrder

universe u v w x y d e e'

namespace IPFunctor.ScopedSignature

variable {K : Type u} {τ : ScopedSignature.{u, v, w} K}

/-! ## Evaluated annotations -/

namespace Heads

variable {H : Heads.{u, x, y} K}

/-- Evaluated annotations: each slot as a function of its own type binders. -/
abbrev AnnV (H : Heads.{u, x, y} K) (Den : K → Type d) (h : H.Shape) :=
  Env (fun j : List K × K => Env Den j.1 → Den j.2) (H.slots h)

/-- Evaluate every annotation at a type assignment. -/
@[expose] def evalAnn {Den : K → Type d} (alg : τ.Interpretation Den) {h : H.Shape}
    {Θ : List K} (a : H.Ann τ h Θ) (ρ : Env Den Θ) : H.AnnV Den h :=
  fun j x ξ => (a j x).denote alg (Env.append ξ ρ)

/-- Evaluating substituted annotations evaluates at the substituted assignment. -/
theorem evalAnn_subst {Den : K → Type d} (alg : τ.Interpretation Den) {h : H.Shape}
    {Θ Θ' : List K} (θ : τ.Substitution Θ Θ') (a : H.Ann τ h Θ) (ρ' : Env Den Θ') :
    evalAnn alg (Ann.subst θ a) ρ' = evalAnn alg a (Term.substitutionEnv alg θ ρ') := by
  funext j x ξ
  simp only [evalAnn, Ann.subst, Term.denote_subst, Term.substitutionEnv_liftMany]

end Heads

namespace Stacked

variable {k₀ : K} {H : Heads.{u, x, y} K}

/-- A model of a stacked family: type-level meanings, and value-level typing on evaluated
annotations, coherent with the syntactic typing. -/
structure Model (S : Stacked τ k₀ H) where
  /-- Meanings of type-level kinds. -/
  Den : K → Type d
  /-- The type-level interpretation. -/
  tyAlg : τ.Interpretation Den
  /-- Value-level side condition, such as the carrier equation of a coercion. -/
  WFV : (h : H.Shape) → H.AnnV Den h → Prop
  /-- Value-level binder types. -/
  bindersV : (h : H.Shape) → H.AnnV Den h → (p : H.Arg h) → Env Den (H.tbind h p) →
    List (Den k₀)
  /-- Value-level child types. -/
  sortV : (h : H.Shape) → H.AnnV Den h → (p : H.Arg h) → Env Den (H.tbind h p) → Den k₀
  /-- Value-level result types. -/
  resultV : (h : H.Shape) → H.AnnV Den h → Den k₀
  /-- The syntactic side condition gives the value-level one. -/
  wf_coh : ∀ {Θ : List K} (h : H.Shape) (a : H.Ann τ h Θ) (ρ : Env Den Θ), S.WF h a →
    WFV h (Heads.evalAnn tyAlg a ρ)
  /-- Binder types agree with the syntax. -/
  binders_coh : ∀ {Θ : List K} (h : H.Shape) (a : H.Ann τ h Θ) (ρ : Env Den Θ) (p : H.Arg h)
    (ξ : Env Den (H.tbind h p)), S.WF h a →
    (S.binders h a p).map (fun s => s.denote tyAlg (Env.append ξ ρ)) =
      bindersV h (Heads.evalAnn tyAlg a ρ) p ξ
  /-- Child types agree with the syntax. -/
  sort_coh : ∀ {Θ : List K} (h : H.Shape) (a : H.Ann τ h Θ) (ρ : Env Den Θ) (p : H.Arg h)
    (ξ : Env Den (H.tbind h p)), S.WF h a →
    (S.sort h a p).denote tyAlg (Env.append ξ ρ) = sortV h (Heads.evalAnn tyAlg a ρ) p ξ
  /-- Result types agree with the syntax. -/
  result_coh : ∀ {Θ : List K} (h : H.Shape) (a : H.Ann τ h Θ) (ρ : Env Den Θ), S.WF h a →
    (S.result h a).denote tyAlg ρ = resultV h (Heads.evalAnn tyAlg a ρ)

namespace Model

variable {S : Stacked τ k₀ H} (M : Model.{u, v, w, x, y, d} S)

/-! ## Environments of a child -/

/-- Move a value environment below a block of type binders. Below no binders it is
unchanged; below a non-empty block each value is transported along the weakening of its
sort. -/
@[expose] def ambientEnv (V : M.Den k₀ → Type e) {Θ : List K} {Γ : List (τ.Term Θ k₀)} :
    (Ξ : List K) → (ξ : Env M.Den Ξ) → (ρ : Env M.Den Θ) →
      Env (fun s => V (s.denote M.tyAlg ρ)) Γ →
      Env (fun s => V (s.denote M.tyAlg (Env.append ξ ρ))) ((enter (k₀ := k₀) Ξ).context Γ)
  | [], _, _, η => η
  | k :: Ξ, ξ, ρ, η => (enter (k₀ := k₀) (k :: Ξ)).env
      (V := fun s => V (s.denote M.tyAlg (Env.append ξ ρ)))
      fun s x => cast (congrArg V (Term.denote_weakenMany M.tyAlg s ξ ρ).symm) (η s x)

/-- `ambientEnv` as a continuous map. -/
@[expose] noncomputable def ambientEnvContinuous (D : M.Den k₀ → Type e)
    [∀ d, OmegaCompletePartialOrder (D d)] {Θ : List K} {Γ : List (τ.Term Θ k₀)} :
    (Ξ : List K) → (ξ : Env M.Den Ξ) → (ρ : Env M.Den Θ) →
      Env (fun s => D (s.denote M.tyAlg ρ)) Γ →𝒄
        Env (fun s => D (s.denote M.tyAlg (Env.append ξ ρ))) ((enter (k₀ := k₀) Ξ).context Γ)
  | [], _, _ => ContinuousHom.id
  | k :: Ξ, ξ, ρ => Env.map (·.subst (Substitution.weakenMany (k :: Ξ)))
      (W := fun s => D (s.denote M.tyAlg (Env.append ξ ρ)))
      fun s => ContinuousHom.ofEq D (Term.denote_weakenMany M.tyAlg s ξ ρ).symm

theorem ambientEnvContinuous_apply (D : M.Den k₀ → Type e)
    [∀ d, OmegaCompletePartialOrder (D d)] {Θ : List K} {Γ : List (τ.Term Θ k₀)} (Ξ : List K)
    (ξ : Env M.Den Ξ) (ρ : Env M.Den Θ) (η : Env (fun s => D (s.denote M.tyAlg ρ)) Γ) :
    M.ambientEnvContinuous D Ξ ξ ρ η = M.ambientEnv D Ξ ξ ρ η := by
  cases Ξ <;> rfl

/-- Read the fresh value binders of a child through the binder coherence equation. -/
@[expose] def binderEnv (V : M.Den k₀ → Type e) {Θ : List K} {h : H.Shape}
    (a : H.Ann τ h Θ) (wf : S.WF h a) (ρ : Env M.Den Θ) (p : H.Arg h)
    (ξ : Env M.Den (H.tbind h p)) (ηb : Env V (M.bindersV h (Heads.evalAnn M.tyAlg a ρ) p ξ)) :
    Env (fun s => V (s.denote M.tyAlg (Env.append ξ ρ))) (S.binders h a p) :=
  fun _ x => Env.castCtx (M.binders_coh h a ρ p ξ wf).symm ηb _
    (x.map fun s => s.denote M.tyAlg (Env.append ξ ρ))

/-- `binderEnv` as a continuous map. -/
@[expose] noncomputable def binderEnvContinuous (D : M.Den k₀ → Type e)
    [∀ d, OmegaCompletePartialOrder (D d)] {Θ : List K} {h : H.Shape}
    (a : H.Ann τ h Θ) (wf : S.WF h a) (ρ : Env M.Den Θ) (p : H.Arg h)
    (ξ : Env M.Den (H.tbind h p)) :
    Env D (M.bindersV h (Heads.evalAnn M.tyAlg a ρ) p ξ) →𝒄
      Env (fun s => D (s.denote M.tyAlg (Env.append ξ ρ))) (S.binders h a p) :=
  .ofFun (M.binderEnv D a wf ρ p ξ) (by
    apply ωScottContinuous.of_apply₂
    intro s
    apply ωScottContinuous.of_apply₂
    intro y
    change ωScottContinuous fun ηb => Env.castCtxContinuous _ ηb _ _
    fun_prop)

/-! ## Ordinary interpretations -/

/-- An ordinary interpretation of the value level into a family of types. It sees each head
only through its evaluated annotations and value-level side condition. -/
abbrev Interp (V : M.Den k₀ → Type e') :=
  ∀ (h : H.Shape) (v : H.AnnV M.Den h), M.WFV h v →
    ((p : H.Arg h) → (ξ : Env M.Den (H.tbind h p)) →
      Env V (M.bindersV h v p ξ) → V (M.sortV h v p ξ)) → V (M.resultV h v)

/-- Ordinary meanings of terms: for each type assignment, a function of the value
environment. -/
abbrev Sem (V : M.Den k₀ → Type e') (j : ScopedFamily.Judgment (fun Θ => τ.Term Θ k₀)) :=
  (ρ : Env M.Den j.1) → Env (fun s => V (s.denote M.tyAlg ρ)) j.2.1 → V (j.2.2.denote M.tyAlg ρ)

/-- The syntax algebra induced by an ordinary interpretation over evaluated heads. -/
@[expose] def alg (V : M.Den k₀ → Type e') (I : M.Interp V) :
    FoldAlgebra S.toFamily.polynomial (M.Sem V) :=
  fun _ o next ρ η =>
    cast (congrArg V ((M.result_coh o.1.1 o.1.2 ρ o.2.2).symm.trans
        (congrArg (·.denote M.tyAlg ρ) o.2.1)))
      (I o.1.1 (Heads.evalAnn M.tyAlg o.1.2 ρ) (M.wf_coh o.1.1 o.1.2 ρ o.2.2) fun p ξ ηb =>
        cast (congrArg V (M.sort_coh o.1.1 o.1.2 ρ p ξ o.2.2))
          (next p (Env.append ξ ρ)
            (Env.append (M.binderEnv V o.1.2 o.2.2 ρ p ξ ηb)
              (M.ambientEnv V (H.tbind o.1.1 p) ξ ρ η))))

/-- The ordinary meaning: the generic fold. -/
@[expose] def denote (V : M.Den k₀ → Type e') (I : M.Interp V) {Θ : List K}
    {Γ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀} (t : S.toFamily.Term Θ Γ s) :
    M.Sem V ⟨Θ, Γ, s⟩ :=
  t.fold (fun _ x _ η => η _ x) (M.alg V I)

@[simp] theorem denote_var (V : M.Den k₀ → Type e') (I : M.Interp V) {Θ : List K}
    {Γ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀} (x : ScopedVar Γ s) (ρ : Env M.Den Θ)
    (η : Env (fun s => V (s.denote M.tyAlg ρ)) Γ) :
    M.denote V I (ScopedFamily.Term.var (σ := S.toFamily) x) ρ η = η s x := rfl

theorem denote_node (V : M.Den k₀ → Type e') (I : M.Interp V) {Θ : List K}
    {Γ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀} (o : S.toFamily.Op Θ s)
    (args : (p : S.toFamily.Arg o) → S.toFamily.Term (S.toFamily.world o p)
      (S.toFamily.binders o p ++ (S.toFamily.ambient o p).context Γ) (S.toFamily.sort o p))
    (ρ : Env M.Den Θ) :
    M.denote V I (ScopedFamily.Term.node o args) ρ =
      M.alg V I ⟨Θ, Γ, s⟩ o (fun p => M.denote V I (args p)) ρ := rfl

/-- A checked node means its interpretation at the evaluated head, with each child read in its
fresh binders and the ambient environment moved below the child's type binders. -/
theorem denote_stackedNode (V : M.Den k₀ → Type e') (I : M.Interp V) {Θ : List K}
    {Γ : List (τ.Term Θ k₀)} (h : H.Shape) (a : H.Ann τ h Θ) (wf : S.WF h a)
    (args : (p : H.Arg h) → S.toFamily.Term (H.tbind h p ++ Θ)
      (S.binders h a p ++ (enter (k₀ := k₀) (H.tbind h p)).context Γ) (S.sort h a p))
    (ρ : Env M.Den Θ) (η : Env (fun s => V (s.denote M.tyAlg ρ)) Γ) :
    M.denote V I (S.node h a wf args) ρ η =
      cast (congrArg V (M.result_coh h a ρ wf).symm)
        (I h (Heads.evalAnn M.tyAlg a ρ) (M.wf_coh h a ρ wf) fun p ξ ηb =>
          cast (congrArg V (M.sort_coh h a ρ p ξ wf))
            (M.denote V I (args p) (Env.append ξ ρ)
              (Env.append (M.binderEnv V a wf ρ p ξ ηb) (M.ambientEnv V (H.tbind h p) ξ ρ η)))) :=
  rfl

/-! ## Continuous interpretations -/

/-- A continuous interpretation of the value level. It sees each head only through its
evaluated annotations and value-level side condition, and receives each child as a continuous
function of the child's type arguments and fresh value binders. -/
abbrev DomainInterp (D : M.Den k₀ → Type e) [∀ d, OmegaCompletePartialOrder (D d)] :=
  ∀ (h : H.Shape) (v : H.AnnV M.Den h), M.WFV h v →
    ((p : H.Arg h) → (ξ : Env M.Den (H.tbind h p)) →
      Env D (M.bindersV h v p ξ) →𝒄 D (M.sortV h v p ξ)) →𝒄 D (M.resultV h v)

variable (D : M.Den k₀ → Type e) [∀ d, OmegaCompletePartialOrder (D d)]

/-- Continuous meanings of terms: for each type assignment, a continuous function of the value
environment. -/
abbrev DomainSem (j : ScopedFamily.Judgment (fun Θ => τ.Term Θ k₀)) :=
  (ρ : Env M.Den j.1) → Env (fun s => D (s.denote M.tyAlg ρ)) j.2.1 →𝒄 D (j.2.2.denote M.tyAlg ρ)

/-- The children of a head as a continuous function of the ambient environment. -/
@[expose] noncomputable def children {Θ : List K} {Γ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀}
    (o : S.Op Θ s)
    (next : (p : H.Arg o.1.1) → M.DomainSem D (S.toFamily.polynomial.src ⟨Θ, Γ, s⟩ o p))
    (ρ : Env M.Den Θ) :
    Env (fun s => D (s.denote M.tyAlg ρ)) Γ →𝒄
      ((p : H.Arg o.1.1) → (ξ : Env M.Den (H.tbind o.1.1 p)) →
        Env D (M.bindersV o.1.1 (Heads.evalAnn M.tyAlg o.1.2 ρ) p ξ) →𝒄
          D (M.sortV o.1.1 (Heads.evalAnn M.tyAlg o.1.2 ρ) p ξ)) :=
  .ofFun (fun η p ξ => .ofFun (fun ηb => ContinuousHom.ofEq D (M.sort_coh o.1.1 o.1.2 ρ p ξ o.2.2)
      (next p (Env.append ξ ρ)
        (Env.append (M.binderEnvContinuous D o.1.2 o.2.2 ρ p ξ ηb)
          (M.ambientEnvContinuous D (H.tbind o.1.1 p) ξ ρ η)))) (by fun_prop)) (by
    apply ωScottContinuous.of_apply₂
    intro p
    apply ωScottContinuous.of_apply₂
    intro ξ
    apply ContinuousHom.ωScottContinuous_of_apply
    intro ηb
    fun_prop)

theorem children_apply {Θ : List K} {Γ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀}
    (o : S.Op Θ s)
    (next : (p : H.Arg o.1.1) → M.DomainSem D (S.toFamily.polynomial.src ⟨Θ, Γ, s⟩ o p))
    (ρ : Env M.Den Θ) (η : Env (fun s => D (s.denote M.tyAlg ρ)) Γ) (p : H.Arg o.1.1)
    (ξ : Env M.Den (H.tbind o.1.1 p))
    (ηb : Env D (M.bindersV o.1.1 (Heads.evalAnn M.tyAlg o.1.2 ρ) p ξ)) :
    M.children D o next ρ η p ξ ηb = ContinuousHom.ofEq D (M.sort_coh o.1.1 o.1.2 ρ p ξ o.2.2)
      (next p (Env.append ξ ρ)
        (Env.append (M.binderEnv D o.1.2 o.2.2 ρ p ξ ηb)
          (M.ambientEnv D (H.tbind o.1.1 p) ξ ρ η))) := by
  rw [← ambientEnvContinuous_apply]
  rfl

/-- The syntax algebra induced by a continuous interpretation over evaluated heads. -/
@[expose] noncomputable def domainAlg (I : M.DomainInterp D) :
    FoldAlgebra S.toFamily.polynomial (M.DomainSem D) :=
  fun _ o next ρ =>
    (ContinuousHom.ofEq D ((M.result_coh o.1.1 o.1.2 ρ o.2.2).symm.trans
        (congrArg (·.denote M.tyAlg ρ) o.2.1))).comp
      ((I o.1.1 (Heads.evalAnn M.tyAlg o.1.2 ρ) (M.wf_coh o.1.1 o.1.2 ρ o.2.2)).comp
        (M.children D o next ρ))

/-- The continuous meaning: the generic fold. -/
@[expose] noncomputable def denoteDomain (I : M.DomainInterp D) {Θ : List K}
    {Γ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀} (t : S.toFamily.Term Θ Γ s) :
    M.DomainSem D ⟨Θ, Γ, s⟩ :=
  t.fold (fun _ x _ => .ofFun fun η => η _ x) (M.domainAlg D I)

@[simp] theorem denoteDomain_var (I : M.DomainInterp D) {Θ : List K} {Γ : List (τ.Term Θ k₀)}
    {s : τ.Term Θ k₀} (x : ScopedVar Γ s) (ρ : Env M.Den Θ)
    (η : Env (fun s => D (s.denote M.tyAlg ρ)) Γ) :
    M.denoteDomain D I (ScopedFamily.Term.var (σ := S.toFamily) x) ρ η = η s x := rfl

theorem denoteDomain_node (I : M.DomainInterp D) {Θ : List K} {Γ : List (τ.Term Θ k₀)}
    {s : τ.Term Θ k₀} (o : S.toFamily.Op Θ s)
    (args : (p : S.toFamily.Arg o) → S.toFamily.Term (S.toFamily.world o p)
      (S.toFamily.binders o p ++ (S.toFamily.ambient o p).context Γ) (S.toFamily.sort o p))
    (ρ : Env M.Den Θ) :
    M.denoteDomain D I (ScopedFamily.Term.node o args) ρ =
      M.domainAlg D I ⟨Θ, Γ, s⟩ o (fun p => M.denoteDomain D I (args p)) ρ := rfl

/-- A checked node means its interpretation at the evaluated head, with each child read in its
fresh binders and the ambient environment moved below the child's type binders. -/
theorem denoteDomain_stackedNode (I : M.DomainInterp D) {Θ : List K} {Γ : List (τ.Term Θ k₀)}
    (h : H.Shape) (a : H.Ann τ h Θ) (wf : S.WF h a)
    (args : (p : H.Arg h) → S.toFamily.Term (H.tbind h p ++ Θ)
      (S.binders h a p ++ (enter (k₀ := k₀) (H.tbind h p)).context Γ) (S.sort h a p))
    (ρ : Env M.Den Θ) (η : Env (fun s => D (s.denote M.tyAlg ρ)) Γ) :
    M.denoteDomain D I (S.node h a wf args) ρ η =
      ContinuousHom.ofEq D (M.result_coh h a ρ wf).symm
        (I h (Heads.evalAnn M.tyAlg a ρ) (M.wf_coh h a ρ wf) fun p ξ =>
          .ofFun (fun ηb => ContinuousHom.ofEq D (M.sort_coh h a ρ p ξ wf)
            (M.denoteDomain D I (args p) (Env.append ξ ρ)
              (Env.append (M.binderEnvContinuous D a wf ρ p ξ ηb)
                (M.ambientEnvContinuous D (H.tbind h p) ξ ρ η)))) (by fun_prop)) := rfl

theorem denoteDomain_cast (I : M.DomainInterp D) {Θ : List K} {Γ Δ : List (τ.Term Θ k₀)}
    {s s' : τ.Term Θ k₀} (hΓ : Γ = Δ) (hs : s = s') (t : S.toFamily.Term Θ Γ s)
    (ρ : Env M.Den Θ) (E : Env (fun s => D (s.denote M.tyAlg ρ)) Δ) :
    HEq (M.denoteDomain D I (ScopedFamily.Term.cast (σ := S.toFamily) hΓ hs t) ρ E)
      (M.denoteDomain D I t ρ (Env.castCtx hΓ.symm E)) := by
  subst hΓ hs
  rfl

theorem denoteDomain_congr (I : M.DomainInterp D) {Θ : List K} {Γ : List (τ.Term Θ k₀)}
    {s : τ.Term Θ k₀} (t : S.toFamily.Term Θ Γ s) {ρ₁ ρ₂ : Env M.Den Θ} (hρ : ρ₁ = ρ₂)
    {E₁ : Env (fun s => D (s.denote M.tyAlg ρ₁)) Γ} {E₂ : Env (fun s => D (s.denote M.tyAlg ρ₂)) Γ}
    (hE : HEq E₁ E₂) : HEq (M.denoteDomain D I t ρ₁ E₁) (M.denoteDomain D I t ρ₂ E₂) := by
  subst hρ
  cases eq_of_heq hE
  rfl

theorem domainInterp_heq (I : M.DomainInterp D) (h : H.Shape) {v₁ v₂ : H.AnnV M.Den h}
    (hv : v₁ = v₂) (w₁ : M.WFV h v₁) (w₂ : M.WFV h v₂)
    {c₁ : (p : H.Arg h) → (ξ : Env M.Den (H.tbind h p)) →
      Env D (M.bindersV h v₁ p ξ) →𝒄 D (M.sortV h v₁ p ξ)}
    {c₂ : (p : H.Arg h) → (ξ : Env M.Den (H.tbind h p)) →
      Env D (M.bindersV h v₂ p ξ) →𝒄 D (M.sortV h v₂ p ξ)}
    (hc : ∀ p ξ ηb₁ ηb₂, HEq ηb₁ ηb₂ → HEq (c₁ p ξ ηb₁) (c₂ p ξ ηb₂)) :
    HEq (I h v₁ w₁ c₁) (I h v₂ w₂ c₂) := by
  subst hv
  obtain rfl : c₁ = c₂ := funext fun p => funext fun ξ =>
    ContinuousHom.ext _ _ fun ηb => eq_of_heq (hc p ξ ηb ηb HEq.rfl)
  rfl

/-! ## Type-parameter substitution commutes with the continuous meaning -/

/-- Transport a value environment along equal type assignments. -/
private def castEnv {Θ : List K} {ρ₁ ρ₂ : Env M.Den Θ} (h : ρ₁ = ρ₂) {L : List (τ.Term Θ k₀)}
    (E : Env (fun s => D (s.denote M.tyAlg ρ₁)) L) : Env (fun s => D (s.denote M.tyAlg ρ₂)) L :=
  h ▸ E

omit [∀ d, OmegaCompletePartialOrder (D d)] in
private theorem castEnv_heq {Θ : List K} {ρ₁ ρ₂ : Env M.Den Θ} (h : ρ₁ = ρ₂)
    {L : List (τ.Term Θ k₀)} (E : Env (fun s => D (s.denote M.tyAlg ρ₁)) L) :
    HEq (M.castEnv D h E) E := by
  subst h
  rfl

omit [∀ d, OmegaCompletePartialOrder (D d)] in
private theorem pointwise_castEnv_left {Θ : List K} {ρ₁ ρ₂ : Env M.Den Θ} (h : ρ₁ = ρ₂)
    {L : List (τ.Term Θ k₀)} (E : Env (fun s => D (s.denote M.tyAlg ρ₁)) L) {U : Type*}
    {F : U → Type e} {L' : List U} (G : Env F L') (hp : Env.Pointwise E G) :
    Env.Pointwise (M.castEnv D h E) G := by
  subst h
  exact hp

omit [∀ d, OmegaCompletePartialOrder (D d)] in
theorem pointwise_binderEnv {Θ Θ' : List K} {h : H.Shape} (θ : τ.Substitution Θ Θ')
    (a : H.Ann τ h Θ) (wf : S.WF h a) (ρ' : Env M.Den Θ') (p : H.Arg h)
    (ξ : Env M.Den (H.tbind h p))
    (ηb₁ : Env D (M.bindersV h (Heads.evalAnn M.tyAlg (Heads.Ann.subst θ a) ρ') p ξ))
    (ηb₂ : Env D (M.bindersV h (Heads.evalAnn M.tyAlg a (Term.substitutionEnv M.tyAlg θ ρ')) p ξ))
    (hb : HEq ηb₁ ηb₂) :
    Env.Pointwise (M.binderEnv D a wf (Term.substitutionEnv M.tyAlg θ ρ') p ξ ηb₂)
      (M.binderEnv D (Heads.Ann.subst θ a) (S.wf_subst θ h a wf) ρ' p ξ ηb₁) := by
  intro s s' x y hxy
  apply Env.apply_heq_of_heq _
    (((Env.castCtx_heq _ _).trans hb.symm).trans (Env.castCtx_heq _ _).symm)
  · simp only [ScopedVar.index_map, hxy]
  · rw [M.binders_coh _ _ _ _ _ wf, M.binders_coh _ _ _ _ _ (S.wf_subst θ h a wf),
      Heads.evalAnn_subst M.tyAlg θ a ρ']

omit [∀ d, OmegaCompletePartialOrder (D d)] in
theorem pointwise_ambientEnv {Θ Θ' : List K} (Ξ : List K) (θ : τ.Substitution Θ Θ')
    (ξ : Env M.Den Ξ) (ρ' : Env M.Den Θ') {Γ : List (τ.Term Θ k₀)}
    (η' : Env (fun s => D (s.denote M.tyAlg ρ')) (Γ.map (·.subst θ)))
    (η : Env (fun s => D (s.denote M.tyAlg (Term.substitutionEnv M.tyAlg θ ρ'))) Γ)
    (hη : Env.Pointwise η η') :
    Env.Pointwise (M.ambientEnv D Ξ ξ (Term.substitutionEnv M.tyAlg θ ρ') η)
      (M.ambientEnv D Ξ ξ ρ' η') := by
  cases Ξ with
  | nil => exact hη
  | cons k Ξ =>
    intro s s' x y hxy
    revert hxy
    induction x using ScopedFamily.Ambient.var_inductionOn (enter (k :: Ξ)) with
    | h s₀ x₀ =>
      induction y using ScopedFamily.Ambient.var_inductionOn (enter (k :: Ξ)) with
      | h s₁ y₁ =>
        induction y₁ using ScopedVar.map_inductionOn with
        | h s₂ y₂ =>
          intro hxy
          rw [ScopedFamily.Ambient.index_var, ScopedFamily.Ambient.index_var,
            ScopedVar.index_map] at hxy
          simp only [ambientEnv, ScopedFamily.Ambient.env_var]
          exact (cast_heq _ _).trans
            ((hη x₀ (y₂.map _) (by rw [ScopedVar.index_map, hxy])).trans (cast_heq _ _).symm)

/-- Substituting type parameters commutes with the continuous meaning, for every
interpretation over evaluated heads. The value environments agree at every position. -/
theorem denoteDomain_map (I : M.DomainInterp D) {Θ : List K} {Γ : List (τ.Term Θ k₀)}
    {s : τ.Term Θ k₀} (t : S.toFamily.Term Θ Γ s) {Θ' : List K} (θ : τ.Substitution Θ Θ')
    (ρ' : Env M.Den Θ') (η' : Env (fun s => D (s.denote M.tyAlg ρ')) (Γ.map (·.subst θ)))
    (η : Env (fun s => D (s.denote M.tyAlg (Term.substitutionEnv M.tyAlg θ ρ'))) Γ)
    (hη : Env.Pointwise η η') :
    HEq (M.denoteDomain D I (t.map S.paramHom θ) ρ' η')
      (M.denoteDomain D I t (Term.substitutionEnv M.tyAlg θ ρ') η) := by
  revert Θ' θ ρ' η' η hη
  refine ScopedFamily.Term.inductionOn (σ := S.toFamily)
    (C := fun Θ Γ s t => ∀ {Θ' : List K} (θ : τ.Substitution Θ Θ') (ρ' : Env M.Den Θ')
      (η' : Env (fun s => D (s.denote M.tyAlg ρ')) (Γ.map (·.subst θ)))
      (η : Env (fun s => D (s.denote M.tyAlg (Term.substitutionEnv M.tyAlg θ ρ'))) Γ),
      Env.Pointwise η η' → HEq (M.denoteDomain D I (t.map S.paramHom θ) ρ' η')
        (M.denoteDomain D I t (Term.substitutionEnv M.tyAlg θ ρ') η)) ?_ ?_ t
  · intro Θ Γ s x Θ' θ ρ' η' η hη
    exact ((Env.forall₂_iff_map.mp hη) s x).symm
  · intro Θ Γ s o args ih Θ' θ ρ' η' η hη
    rw [ScopedFamily.Term.map_node, denoteDomain_node, denoteDomain_node]
    simp only [domainAlg, ContinuousHom.comp_apply]
    refine (ContinuousHom.ofEq_heq _ _ _).trans
      (HEq.trans ?_ (ContinuousHom.ofEq_heq _ _ _).symm)
    refine M.domainInterp_heq D I o.1.1 (Heads.evalAnn_subst M.tyAlg θ o.1.2 ρ') _ _ ?_
    intro p ξ ηb₁ ηb₂ hb
    refine (heq_of_eq (M.children_apply D _ _ _ _ _ _ _)).trans
      (HEq.trans ?_ (heq_of_eq (M.children_apply D _ _ _ _ _ _ _)).symm)
    refine (ContinuousHom.ofEq_heq _ _ _).trans
      (HEq.trans ?_ (ContinuousHom.ofEq_heq _ _ _).symm)
    have hρ : Term.substitutionEnv M.tyAlg (Substitution.liftMany θ (H.tbind o.1.1 p))
        (Env.append ξ ρ') = Env.append ξ (Term.substitutionEnv M.tyAlg θ ρ') :=
      Term.substitutionEnv_liftMany _ _ _ _ _
    refine (M.denoteDomain_cast D I _ _ _ _ _).trans ?_
    refine (ih p _ _ _ (M.castEnv D hρ.symm _) ?_).trans
      (M.denoteDomain_congr D I _ hρ (M.castEnv_heq D _ _))
    apply M.pointwise_castEnv_left
    apply Env.Forall₂.cast_right
    apply Env.Forall₂.append
    · exact (S.binders_subst θ o.1.1 o.1.2 p ▸ List.length_map _).symm
    · exact M.pointwise_binderEnv D θ o.1.2 o.2.2 ρ' p ξ ηb₁ ηb₂ hb
    · exact M.pointwise_ambientEnv D _ θ ξ ρ' η' η hη

/-- The closed case: instantiate the parameters of a term with no free values. -/
theorem denoteDomain_map_closed (I : M.DomainInterp D) {Θ : List K} {s : τ.Term Θ k₀}
    (t : S.toFamily.Term Θ [] s) {Θ' : List K} (θ : τ.Substitution Θ Θ') (ρ' : Env M.Den Θ') :
    HEq (M.denoteDomain D I (t.map S.paramHom θ) ρ' Env.empty)
      (M.denoteDomain D I t (Term.substitutionEnv M.tyAlg θ ρ') Env.empty) :=
  M.denoteDomain_map D I t θ ρ' _ _ fun _ _ x => nomatch x

/-! ## The fundamental lemma -/

variable {M D} {V : M.Den k₀ → Type e'}

/-- A continuous interpretation simulated by an ordinary one: at every evaluated head,
children related on related fresh binders give related results. -/
@[expose] def DomainInterp.Related (R : ∀ d, D d → V d → Prop) (I : M.DomainInterp D)
    (I' : M.Interp V) : Prop :=
  ∀ (h : H.Shape) (v : H.AnnV M.Den h) (w : M.WFV h v)
    (c : (p : H.Arg h) → (ξ : Env M.Den (H.tbind h p)) →
      Env D (M.bindersV h v p ξ) →𝒄 D (M.sortV h v p ξ))
    (c' : (p : H.Arg h) → (ξ : Env M.Den (H.tbind h p)) →
      Env V (M.bindersV h v p ξ) → V (M.sortV h v p ξ)),
    (∀ p ξ ηb ζb, Env.LiftRel R ηb ζb → R _ (c p ξ ηb) (c' p ξ ζb)) →
      R _ (I h v w c) (I' h v w c')

omit [∀ d, OmegaCompletePartialOrder (D d)] in
/-- A relation indexed by type-level meanings survives transport along their equations. -/
theorem rel_cast {R : ∀ d, D d → V d → Prop} {d d' : M.Den k₀} (h : d = d') {x : D d}
    {y : V d} (hxy : R d x y) : R d' (cast (congrArg D h) x) (cast (congrArg V h) y) := by
  subst h
  exact hxy

omit [∀ d, OmegaCompletePartialOrder (D d)] in
/-- Related fresh binders give related binder environments. -/
theorem liftRel_binderEnv {R : ∀ d, D d → V d → Prop} {Θ : List K} {h : H.Shape}
    (a : H.Ann τ h Θ) (wf : S.WF h a) (ρ : Env M.Den Θ) (p : H.Arg h)
    (ξ : Env M.Den (H.tbind h p)) {ηb : Env D (M.bindersV h (Heads.evalAnn M.tyAlg a ρ) p ξ)}
    {ζb : Env V (M.bindersV h (Heads.evalAnn M.tyAlg a ρ) p ξ)} (hb : Env.LiftRel R ηb ζb) :
    Env.LiftRel (fun s : τ.Term (H.tbind h p ++ Θ) k₀ => R (s.denote M.tyAlg (Env.append ξ ρ)))
      (M.binderEnv D a wf ρ p ξ ηb) (M.binderEnv V a wf ρ p ξ ζb) :=
  fun _ x => hb.castCtx (M.binders_coh h a ρ p ξ wf).symm _
    (x.map fun s => s.denote M.tyAlg (Env.append ξ ρ))

omit [∀ d, OmegaCompletePartialOrder (D d)] in
/-- Related environments stay related below a block of type binders. -/
theorem liftRel_ambientEnv {R : ∀ d, D d → V d → Prop} {Θ : List K}
    {Γ : List (τ.Term Θ k₀)} (Ξ : List K) (ξ : Env M.Den Ξ) (ρ : Env M.Den Θ)
    {η : Env (fun s => D (s.denote M.tyAlg ρ)) Γ} {ζ : Env (fun s => V (s.denote M.tyAlg ρ)) Γ}
    (hη : Env.LiftRel (fun s : τ.Term Θ k₀ => R (s.denote M.tyAlg ρ)) η ζ) :
    Env.LiftRel (fun s : τ.Term (Ξ ++ Θ) k₀ => R (s.denote M.tyAlg (Env.append ξ ρ)))
      (M.ambientEnv D Ξ ξ ρ η) (M.ambientEnv V Ξ ξ ρ ζ) := by
  cases Ξ with
  | nil => exact hη
  | cons k Ξ =>
    intro s x
    induction x using ScopedFamily.Ambient.var_inductionOn (enter (k :: Ξ)) with
    | h s₀ x₀ =>
      simp only [ambientEnv, ScopedFamily.Ambient.env_var]
      exact rel_cast (Term.denote_weakenMany M.tyAlg s₀ ξ ρ).symm (hη s₀ x₀)

/-- The fundamental lemma: constructor-local relatedness at evaluated heads gives related
meanings for every term, at every type assignment, in related environments. -/
theorem denoteDomain_related {R : ∀ d, D d → V d → Prop} {I : M.DomainInterp D}
    {I' : M.Interp V} (hI : DomainInterp.Related R I I') {Θ : List K}
    {Γ : List (τ.Term Θ k₀)} {s : τ.Term Θ k₀} (t : S.toFamily.Term Θ Γ s) (ρ : Env M.Den Θ)
    {η : Env (fun s => D (s.denote M.tyAlg ρ)) Γ} {ζ : Env (fun s => V (s.denote M.tyAlg ρ)) Γ}
    (hη : Env.LiftRel (fun s : τ.Term Θ k₀ => R (s.denote M.tyAlg ρ)) η ζ) :
    R _ (M.denoteDomain D I t ρ η) (M.denote V I' t ρ ζ) := by
  revert ρ η ζ
  refine IFreeM.fold_rel (fun j F G => ∀ (ρ : Env M.Den j.1)
      (η : Env (fun s => D (s.denote M.tyAlg ρ)) j.2.1)
      (ζ : Env (fun s => V (s.denote M.tyAlg ρ)) j.2.1),
      Env.LiftRel (fun s : τ.Term j.1 k₀ => R (s.denote M.tyAlg ρ)) η ζ →
        R _ (F ρ η) (G ρ ζ))
    (fun _ x _ => .ofFun fun η => η _ x) (fun _ x _ η => η _ x) (M.domainAlg D I)
    (M.alg V I') ?_ ?_ t
  · intro j x ρ η ζ hη
    exact hη _ x
  · intro j o ds es hds ρ η ζ hη
    simp only [domainAlg, alg, ContinuousHom.comp_apply, ContinuousHom.ofEq_apply]
    refine rel_cast ((M.result_coh o.1.1 o.1.2 ρ o.2.2).symm.trans
      (congrArg (·.denote M.tyAlg ρ) o.2.1)) (hI _ _ _ _ _ fun p ξ ηb ζb hb => ?_)
    rw [M.children_apply D o ds ρ η p ξ ηb]
    exact rel_cast (M.sort_coh o.1.1 o.1.2 ρ p ξ o.2.2) (hds p _ _ _
      ((liftRel_binderEnv o.1.2 o.2.2 ρ p ξ hb).append (liftRel_ambientEnv _ ξ ρ hη)))

end Model

end Stacked

end IPFunctor.ScopedSignature
