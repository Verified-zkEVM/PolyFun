/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.EnvRelation
public import PolyFun.IPFunctor.Scoped.Uses

/-!
# Call-by-value interpretations of binding signatures

`Term.denote` reads a term in an algebra whose arguments are functions of their bound variables.
A call-by-value interpretation in a monad `m` is the same fold with two changes. A constructor
receives each argument as a computation in `m`, from the values of the variables the argument
binds, of the argument's value (`CBVInterpretation`). A variable returns its value by `pure`
(`Term.denoteCBV`). Variables are bound to values, never to computations, so the algebra decides
when each argument runs and in which order the effects of the arguments happen. A language whose
arrows are read as Kleisli arrows `a → m b` is interpreted this way: an abstraction returns a
closure, and an application runs the function, then the argument, then the closure. A
`DomainInterpretation` reads the same syntax lazily instead: it passes each argument as a
continuous function, which the algebra may apply, discard or take a least fixed point of.

Renaming reads the environment through the renaming (`Term.denoteCBV_rename`). No substitution
law holds for arbitrary terms: a substituted term would run where the variable is read, rather
than once where it is bound.

`Term.denoteCBV_related` is the fundamental lemma of a logical relation between a call-by-value
interpretation and an ordinary `Interpretation`. It takes a relation `RV` between computed values
and plain values, and a relation `RC` between computations and plain values. Suppose that `pure`
sends related values to related computations, and that each head in a set `H` sends related
arguments to related results (`CBVInterpretation.RelatedOn`). Then every term whose heads lie in
`H` has related meanings in environments related by `Env.LiftRel RV`. Adequacy of an effectful
reading against an ordinary one is the instance in which a computation is related to a value when
running the computation gives a related value. Restricting `H` states the lemma for the fragment of
terms that avoid some constructors, such as the effect-free fragment.
-/

public section

universe u v w z z' z''

namespace IPFunctor.ScopedSignature

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S} {m : Type z → Type z'} {V : S → Type z}
  {Γ Δ : List S}

/-- A call-by-value algebra in the monad `m`: each constructor receives each argument as a
computation, from the values of the argument's bound variables, of the argument's value. -/
abbrev CBVInterpretation (σ : ScopedSignature.{u, v, w} S) (m : Type z → Type z')
    (V : S → Type z) :=
  ∀ {a} (op : σ.Op a), ((p : σ.Arg op) → Env V (σ.binders op p) → m (V (σ.sort op p))) → m (V a)

namespace Term

variable [Pure m]

/-- The call-by-value meaning of a term: the fold of `Term.denote` in a call-by-value algebra,
with each variable returning its value by `pure`. -/
@[expose] def denoteCBV (alg : CBVInterpretation σ m V) {a : S} (t : σ.Term Γ a)
    (η : Env V Γ) : m (V a) :=
  t.fold (D := fun j : Judgment S => Env V j.1 → m (V j.2))
    (fun _ x η => pure (η _ x))
    (fun _ op next η => alg op (fun p ξ => next p (Env.append ξ η))) η

@[simp] theorem denoteCBV_var (alg : CBVInterpretation σ m V) {a : S} (x : ScopedVar Γ a)
    (η : Env V Γ) : (var (σ := σ) x).denoteCBV alg η = pure (η a x) := rfl

@[simp] theorem denoteCBV_node (alg : CBVInterpretation σ m V) {a : S} (op : σ.Op a)
    (args : (p : σ.Arg op) → σ.Term (σ.binders op p ++ Γ) (σ.sort op p)) (η : Env V Γ) :
    (node op args).denoteCBV alg η =
      alg op (fun p ξ => (args p).denoteCBV alg (Env.append ξ η)) := rfl

/-- Renaming syntax reads its environment through the renaming. -/
theorem denoteCBV_rename (alg : CBVInterpretation σ m V) {a : S} (t : σ.Term Γ a)
    (ρ : Renaming Γ Δ) (η : Env V Δ) :
    (t.rename ρ).denoteCBV alg η = t.denoteCBV alg (Env.rename ρ η) := by
  induction t using Term.inductionOn generalizing Δ with
  | hvar Γ a x => rfl
  | hnode Γ a op args ih =>
    simp only [rename_node, denoteCBV_node]
    congr 1
    funext p ξ
    rw [ih p, Env.rename_append]

end Term

/-! ## Related interpretations -/

section Related

variable {W : S → Type z''}

/-- A call-by-value algebra simulated by an ordinary one at the heads in `H`: at each of them,
arguments related at related bound values give related results. -/
@[expose] def CBVInterpretation.RelatedOn (H : Set σ.Head) (RV : ∀ a, V a → W a → Prop)
    (RC : ∀ a, m (V a) → W a → Prop) (alg : CBVInterpretation σ m V)
    (alg' : Interpretation σ W) : Prop :=
  ∀ h ∈ H, ∀ (k : (p : σ.Arg h.op) → Env V (σ.binders h.op p) → m (V (σ.sort h.op p)))
    (k' : (p : σ.Arg h.op) → Env W (σ.binders h.op p) → W (σ.sort h.op p)),
    (∀ p ξ ξ', Env.LiftRel RV ξ ξ' → RC _ (k p ξ) (k' p ξ')) →
      RC h.sort (alg h.op k) (alg' h.op k')

/-- **The fundamental lemma** of a logical relation between a call-by-value meaning and an
ordinary one. If `pure` sends related values to related computations, and each head in `H` sends
related arguments to related results, then each term whose heads lie in `H` has related meanings
in related environments. -/
theorem Term.denoteCBV_related [Pure m] {H : Set σ.Head} {RV : ∀ a, V a → W a → Prop}
    {RC : ∀ a, m (V a) → W a → Prop} {alg : CBVInterpretation σ m V}
    {alg' : Interpretation σ W} (hpure : ∀ a v w, RV a v w → RC a (pure v) w)
    (h : CBVInterpretation.RelatedOn H RV RC alg alg') {a : S} (t : σ.Term Γ a)
    (ht : t.heads ⊆ H) {η : Env V Γ} {ζ : Env W Γ} (hη : Env.LiftRel RV η ζ) :
    RC a (t.denoteCBV alg η) (t.denote alg' ζ) := by
  induction t using Term.inductionOn with
  | hvar Γ a x => exact hpure a _ _ (hη a x)
  | hnode Γ a op args ih =>
    exact h ⟨a, op⟩ (ht (mem_heads_node_self op args)) _ _ fun p ξ ξ' hξ =>
      ih p ((heads_subset_heads_node op args p).trans ht) (hξ.append hη)

end Related

end IPFunctor.ScopedSignature
