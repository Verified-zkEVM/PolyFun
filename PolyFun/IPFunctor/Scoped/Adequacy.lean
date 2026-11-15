/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.DomainInterpretation

/-!
# A syntactic logical relation for continuous meanings

Adequacy relates a continuous meaning to an operational semantics on closed terms. The generic
part is a logical relation between semantic values and closed terms. Suppose that a continuous
algebra relates each constructor's result to the closed node whenever each argument's meaning is
related to the argument closed by related terms (`DomainInterpretation.RelatedSyntax`). Then
every term's meaning in a semantic environment is related to the term closed by a related
substitution (`Term.denoteDomain_relatedSyntax`). In particular, each closed term is related to
its own meaning.

The relation is any family `R : ∀ a, V a → σ.Term [] a → Prop`, so the operational semantics
stays inside `R`, and a closing substitution is an environment of closed terms related by
`Env.LiftRel R`. A constructor that takes a least fixed point discharges its case by fixed-point
induction when `R` is admissible in its semantic argument. Computational adequacy itself, such as
"the meaning is a value exactly when evaluation terminates", is a corollary for each language.

`Term.instantiate` closes a term below a block of binders by closed terms. It is the operation
that the relation's constructor case applies to each argument.
-/

public section

open OmegaCompletePartialOrder

universe u v w z

namespace IPFunctor.ScopedSignature

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S}

namespace Term

/-- The empty substitution leaves a closed term unchanged. -/
@[simp] theorem subst_empty {a : S} (t : σ.Term [] a) : t.subst Env.empty = t := by
  have h : (Env.empty : σ.Substitution [] []) = fun _ x => var x := Env.eq_empty _ |>.symm
  rw [h, subst_id]

/-- Close a term below a block of binders by closed terms. -/
@[expose] def instantiate {Ξ : List S} {b : S} (c : σ.Term (Ξ ++ []) b)
    (ζ : Env (σ.Term []) Ξ) : σ.Term [] b :=
  c.subst (Env.append ζ Env.empty)

/-- Below no binders, closing changes nothing. -/
@[simp] theorem instantiate_nil {b : S} (c : σ.Term [] b) (ζ : Env (σ.Term []) []) :
    c.instantiate ζ = c :=
  subst_empty c

/-- Below one binder, closing is single-variable substitution. -/
theorem instantiate_single {a b : S} (c : σ.Term [a] b) (v : σ.Term [] a) :
    c.instantiate (Env.single v) = c.substOne v := by
  rw [instantiate, substOne]
  congr 1
  funext c x
  cases x with
  | zero => rfl
  | succ x => exact nomatch x

/-- A substitution lifted past a block of binders, then closed by closed terms, is the
substitution that closes the block and the rest at once. -/
theorem subst_liftMany_append {Γ : List S} (θ : σ.Substitution Γ []) :
    (Ξ : List S) → (ζ : Env (σ.Term []) Ξ) → ∀ {a : S} (x : ScopedVar (Ξ ++ Γ) a),
      (Substitution.liftMany θ Ξ a x).subst (Env.append ζ Env.empty) = Env.append ζ θ a x
  | [], _, _, x => subst_empty (θ _ x)
  | _ :: Ξ, ζ, _, .zero => rfl
  | b :: Ξ, ζ, a, .succ x => by
    change ((Substitution.liftMany θ Ξ a x).rename fun _ => ScopedVar.succ).subst _ = _
    rw [subst_rename]
    exact subst_liftMany_append θ Ξ (fun c y => ζ c y.succ) x

/-- Substituting below a block, then closing the block, substitutes once. -/
theorem instantiate_subst_liftMany {Ξ Γ : List S} {b : S} (c : σ.Term (Ξ ++ Γ) b)
    (θ : σ.Substitution Γ []) (ζ : Env (σ.Term []) Ξ) :
    (c.subst (Substitution.liftMany θ Ξ)).instantiate ζ = c.subst (Env.append ζ θ) := by
  rw [instantiate, subst_subst]
  congr 1
  funext a x
  exact subst_liftMany_append θ Ξ ζ x

end Term

variable {V : S → Type z} [∀ a, OmegaCompletePartialOrder (V a)]

/-- A continuous algebra related to closed syntax by `R`: whenever each argument's meaning is
related to the argument closed by related terms, the constructor's result is related to the
closed node. -/
@[expose] def DomainInterpretation.RelatedSyntax (R : ∀ a, V a → σ.Term [] a → Prop)
    (alg : DomainInterpretation σ V) : Prop :=
  ∀ {a} (op : σ.Op a) (k : (p : σ.Arg op) → Env V (σ.binders op p) →𝒄 V (σ.sort op p))
    (c : (p : σ.Arg op) → σ.Term (σ.binders op p ++ []) (σ.sort op p)),
    (∀ p ξ ζ, Env.LiftRel R ξ ζ → R _ (k p ξ) ((c p).instantiate ζ)) →
      R a (alg op k) (Term.node op c)

/-- The fundamental lemma of a syntactic logical relation: the meaning in a semantic
environment is related to the term closed by a related substitution. -/
theorem Term.denoteDomain_relatedSyntax {R : ∀ a, V a → σ.Term [] a → Prop}
    {alg : DomainInterpretation σ V} (h : alg.RelatedSyntax R) {Γ : List S} {a : S}
    (t : σ.Term Γ a) {η : Env V Γ} {θ : σ.Substitution Γ []} (hη : Env.LiftRel R η θ) :
    R a (t.denoteDomain alg η) (t.subst θ) := by
  induction t using Term.inductionOn with
  | hvar Γ a x => exact hη a x
  | hnode Γ a op args ih =>
    rw [denoteDomain_node, subst_node]
    refine h op _ _ fun p ξ ζ hξ => ?_
    rw [instantiate_subst_liftMany]
    exact ih p (hξ.append hη)

/-- Each closed term is related to its own meaning. -/
theorem Term.denoteDomain_relatedSyntax_closed {R : ∀ a, V a → σ.Term [] a → Prop}
    {alg : DomainInterpretation σ V} (h : alg.RelatedSyntax R) {a : S} (t : σ.Term [] a) :
    R a (t.denoteDomain alg Env.empty) t := by
  have ht := t.denoteDomain_relatedSyntax h (Env.liftRel_empty R)
  rwa [subst_empty] at ht

end IPFunctor.ScopedSignature
