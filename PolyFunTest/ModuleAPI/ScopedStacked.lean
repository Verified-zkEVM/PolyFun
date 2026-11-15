/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedVectors
import PolyFun.IPFunctor.Scoped.Stacked

/-! # Ordinary-import checks for two-level binding families -/

open IPFunctor IPFunctor.ScopedSignature

/-- Weakening past a block keeps the older positions and moves the index. -/
example {S : Type} {Γ : List S} {a : S} (Ξ : List S) (x : ScopedVar Γ a) :
    (x.weakenMany Ξ).index = x.index + Ξ.length := by simp

/-- Weakening below one variable by substitution is the renaming `Term.weaken`. -/
example {S : Type} {σ : ScopedSignature S} {Γ : List S} {a : S} (b : S) (t : σ.Term Γ a) :
    t.subst (Substitution.weakenMany [b]) = t.weaken b :=
  Term.subst_weakenMany_singleton b t

/-- Substituting by a composite substitutes twice. -/
example {S : Type} {σ : ScopedSignature S} {Γ Δ Θ : List S} {a : S} (t : σ.Term Γ a)
    (θ : σ.Substitution Γ Δ) (θ' : σ.Substitution Δ Θ) :
    t.subst (θ'.comp θ) = (t.subst θ).subst θ' :=
  Term.subst_comp t θ θ'

namespace PolyFunTest.ModuleAPI.ScopedStacked

open Examples.ScopedVectors Examples.ScopedVectors.TyTerm

/-- An empty block of type binders keeps the value context. -/
example {Θ : List Kind} :
    (Stacked.enter [] : ScopedFamily.Ambient (fun Θ => TySig.Term Θ .scheme) Θ ([] ++ Θ)) =
      .keep := rfl

/-- An application's children take terms in the ambient context, with no coercion. -/
example {Θ : List Kind} {Γ : List (TySig.Term Θ .scheme)} {A B : TyTerm Θ .type}
    (f : Tm Θ Γ (mono (arrow A B))) (x : Tm Θ Γ (mono A)) : Tm Θ Γ (mono B) :=
  lang.node .app (Env.cons A (Env.cons B Env.empty)) trivial
    (fun p => match p with | false => f | true => x)

/-- The derived action is the identity at an application, which keeps its context. -/
example {Θ : List Kind} {Γ : List (TySig.Term Θ .scheme)} {A B : TyTerm Θ .type}
    {s : TySig.Term Θ .scheme} (t : Tm Θ Γ s) (p : Bool) :
    lang.reindexAction (⟨⟨.app, Env.cons A (Env.cons B Env.empty)⟩, rfl, trivial⟩ :
      lang.Op Θ (mono B)) p t = t := rfl

/-- The derived action is lawful, so value substitutions compose. -/
example {Γ Δ Λ : List (TySig.Term [] .scheme)} {s : TySig.Term [] .scheme} (t : Tm [] Γ s)
    (θ : lang.toFamily.Substitution Γ Δ) (θ' : lang.toFamily.Substitution Δ Λ) :
    (t.subst lang.reindexAction θ).subst lang.reindexAction θ' =
      t.subst lang.reindexAction (fun a x => (θ a x).subst lang.reindexAction θ') :=
  lang.subst_subst t θ θ'

/-- Type-parameter substitution commutes with value substitution. -/
example {Γ Δ : List (TySig.Term [.size] .scheme)} {s : TySig.Term [.size] .scheme}
    (μ : TySig.Substitution [.size] []) (θ : lang.toFamily.Substitution Γ Δ)
    (t : Tm [.size] Γ s) :
    (t.subst lang.reindexAction θ).map lang.paramHom μ =
      (t.map lang.paramHom μ).subst lang.reindexAction (θ.map lang.paramHom μ) :=
  lang.map_subst μ θ t

end PolyFunTest.ModuleAPI.ScopedStacked
