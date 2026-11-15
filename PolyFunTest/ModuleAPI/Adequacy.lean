/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.ScopedDomains
import PolyFun.Control.Domain.ResultRel
import PolyFun.IPFunctor.Scoped.Adequacy

/-! # Ordinary-import checks for relations between results and syntactic logical relations -/

open OmegaCompletePartialOrder IPFunctor IPFunctor.ScopedSignature

/-- Lifted relations compute on constructors, through an ordinary import. -/
example (E : Unit → Bool → Prop) (R : ℕ → ℤ → Prop) (x : ℕ) (y : ℤ) (e : Unit) (e' : Bool) :
    (DomainResult.LiftRel E R (DomainResult.value x) (DomainResult.value y) ↔ R x y) ∧
      (DomainResult.LiftRel E R (DomainResult.error e) (DomainResult.error e') ↔ E e e') ∧
      DomainResult.LiftRel E R ⊥ ⊥ :=
  ⟨Iff.rfl, Iff.rfl, trivial⟩

/-- A returned value is related only to a returned value. -/
example {E : Unit → Unit → Prop} {R : ℕ → ℕ → Prop} {x : ℕ} {r : DomainResult Unit ℕ} :
    DomainResult.LiftRel E R (DomainResult.value x) r ↔ ∃ y, r = DomainResult.value y ∧ R x y :=
  DomainResult.liftRel_value_left

/-- Equality lifts to equality, and swapping the results swaps the relations. -/
example {d r : DomainResult Unit ℕ} (h : DomainResult.LiftRel (· = ·) (· = ·) d r) :
    d = r ∧ DomainResult.LiftRel (fun e' e => e = e') (fun y x => x = y) r d :=
  ⟨DomainResult.liftRel_eq_iff.mp h, h.flip⟩

/-- Lifted relations are core's `Option.Rel` of `Sum.LiftRel`, through an ordinary import. -/
example {E : Unit → Unit → Prop} {R : ℕ → ℕ → Prop} {x y : ℕ} (h : R x y) :
    DomainResult.LiftRel E R (DomainResult.value x) (DomainResult.value y) :=
  DomainResult.liftRel_iff_optionRel.mpr (.some (.inr h))

/-- Bottom, or a relation to a unique result, is admissible. -/
example {α β : Type} [OmegaCompletePartialOrder α] {R : α → β → Prop}
    (hR : ∀ y, Admissible fun x : α => R x y) (r₀ : DomainResult Unit β) :
    Admissible fun d : DomainResult Unit α =>
      d = ⊥ ∨ ∃ r, r = r₀ ∧ DomainResult.LiftRel (· = ·) R d r :=
  DomainResult.admissible_bot_or_liftRel (fun _ _ h h' => h.trans h'.symm) hR

/-- Closing a term below a block of binders is substitution by the block and nothing else. -/
example {S : Type} {σ : ScopedSignature S} {Ξ : List S} {b : S} (c : σ.Term (Ξ ++ []) b)
    (ζ : Env (σ.Term []) Ξ) : c.instantiate ζ = c.subst (Env.append ζ Env.empty) := rfl

/-- Below one binder, closing is single-variable substitution. -/
example {S : Type} {σ : ScopedSignature S} {a b : S} (c : σ.Term [a] b) (v : σ.Term [] a) :
    c.instantiate (Env.single v) = c.substOne v :=
  Term.instantiate_single c v

/-- The fundamental lemma of a syntactic logical relation, for every continuous algebra. -/
example {S : Type} {σ : ScopedSignature S} {V : S → Type} [∀ a, OmegaCompletePartialOrder (V a)]
    {R : ∀ a, V a → σ.Term [] a → Prop} {alg : DomainInterpretation σ V}
    (h : alg.RelatedSyntax R) {Γ : List S} {a : S} (t : σ.Term Γ a) {η : Env V Γ}
    {θ : σ.Substitution Γ []} (hη : Env.LiftRel R η θ) :
    R a (t.denoteDomain alg η) (t.subst θ) :=
  Term.denoteDomain_relatedSyntax h t hη

namespace PolyFunTest.ModuleAPI.Adequacy

open Examples.ScopedDomains

/-- Adequacy at numbers. -/
example (t : Expr [] .nat) (n : ℕ) : meaning t = number n ↔ Eval t (numeral n) :=
  meaning_eq_number_iff t n

/-- A closed term means bottom exactly when it does not evaluate. -/
example {a : Ty} (t : Expr [] a) : meaning t = ⊥ ↔ ∀ w, ¬Eval t w :=
  meaning_eq_bot_iff t

/-- The call-by-name evaluator ignores an unused divergent argument, as the lazy meaning does. -/
example : meaning (.app (.lam .zero) diverge) = number 0 :=
  (meaning_eq_number_iff _ 0).mpr eval_const

/-- A divergent term does not evaluate. -/
example (w : Expr [] .nat) : ¬Eval diverge w :=
  (meaning_eq_bot_iff diverge).mp meaning_diverge w

end PolyFunTest.ModuleAPI.Adequacy
