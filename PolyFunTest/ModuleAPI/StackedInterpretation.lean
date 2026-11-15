/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedVectors
import PolyFun.IPFunctor.Scoped.StackedInterpretation

/-! # Ordinary-import checks for interpretations of two-level binding families -/

open OmegaCompletePartialOrder IPFunctor IPFunctor.ScopedSignature

/-- Transport along an equation of indices composes. -/
example {ι : Type} (D : ι → Type) [∀ i, OmegaCompletePartialOrder (D i)] {i j k : ι}
    (h : i = j) (h' : j = k) (x : D i) :
    ContinuousHom.ofEq D h' (ContinuousHom.ofEq D h x) = ContinuousHom.ofEq D (h.trans h') x :=
  ContinuousHom.ofEq_ofEq D h h' x

/-- A weakened type-level term ignores the fresh block. -/
example {S : Type} {σ : ScopedSignature S} {V : S → Type} (alg : Interpretation σ V)
    {Γ Ξ : List S} {a : S} (t : σ.Term Γ a) (ξ : Env V Ξ) (η : Env V Γ) :
    (t.subst (Substitution.weakenMany Ξ)).denote alg (Env.append ξ η) = t.denote alg η :=
  Term.denote_weakenMany alg t ξ η

/-- One step of the continuous meaning of a checked node, for every stacked family. -/
example {K : Type} {τ : ScopedSignature K} {k₀ : K} {H : Heads K} {S : Stacked τ k₀ H}
    (M : S.Model) (D : M.Den k₀ → Type) [∀ d, OmegaCompletePartialOrder (D d)]
    (I : M.DomainInterp D) {Θ : List K} {Γ : List (τ.Term Θ k₀)} (h : H.Shape)
    (a : H.Ann τ h Θ) (wf : S.WF h a)
    (args : (p : H.Arg h) → S.toFamily.Term (H.tbind h p ++ Θ)
      (S.binders h a p ++ (Stacked.enter (k₀ := k₀) (H.tbind h p)).context Γ) (S.sort h a p))
    (ρ : Env M.Den Θ) (η : Env (fun s => D (s.denote M.tyAlg ρ)) Γ) :
    M.denoteDomain D I (S.node h a wf args) ρ η =
      ContinuousHom.ofEq D (M.result_coh h a ρ wf).symm
        (I h (Heads.evalAnn M.tyAlg a ρ) (M.wf_coh h a ρ wf) fun p ξ =>
          .ofFun (fun ηb => ContinuousHom.ofEq D (M.sort_coh h a ρ p ξ wf)
            (M.denoteDomain D I (args p) (Env.append ξ ρ)
              (Env.append (M.binderEnvContinuous D a wf ρ p ξ ηb)
                (M.ambientEnvContinuous D (H.tbind h p) ξ ρ η)))) (by fun_prop)) :=
  M.denoteDomain_stackedNode D I h a wf args ρ η

namespace PolyFunTest.ModuleAPI.StackedInterpretation

open Examples.ScopedVectors Examples.ScopedVectors.TyTerm

/-- Instantiating a size commutes with the lazy meaning, for every substitution. -/
example (θ : TySig.Substitution [.size] []) :
    HEq (model.denoteDomain SDom lazy (repSeven.map lang.paramHom θ) Env.empty Env.empty)
      (model.denoteDomain SDom lazy repSeven (Term.substitutionEnv model.tyAlg θ Env.empty)
        Env.empty) :=
  model.denoteDomain_map_closed SDom lazy repSeven θ Env.empty

/-- The lazy meaning represents the total evaluation of every closed term. -/
example {s : TySig.Term [] .scheme} (t : Tm [] [] s) : Rep _ (meaning t) (evaluate t) :=
  meaning_represents t

/-- A coercion between `[m + n]nat` and `[n + m]nat` evaluates to the identity. -/
example (m n : ℕ) (xs : ℕ → ℕ) :
    (show (m n : ℕ) → (ℕ → ℕ) → ℕ → ℕ from evaluate swap) m n xs = xs :=
  evaluate_swap m n xs

end PolyFunTest.ModuleAPI.StackedInterpretation
