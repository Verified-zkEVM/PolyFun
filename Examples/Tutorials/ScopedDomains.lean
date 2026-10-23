/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.DomainInterpretation
public import Mathlib.Order.Category.OmegaCompletePartialOrder

/-!
# A lazy language with general recursion

A call-by-name language with natural numbers, functions and a fixed-point
constructor. Its meaning is a `DomainInterpretation`: each constructor combines
the continuous meanings of its arguments, so `fix` is a least fixed point, an
unused argument is never demanded, and the substitution laws come from the
generic API.

A call-by-value evaluator for the recursion-free fragment is an ordinary
`Interpretation` into `Option`. One constructor-local lemma relates the two
interpretations, and `Term.denoteDomain_related` lifts it to every term: whenever
the evaluator returns a value, the lazy meaning represents it. The converse
fails, because the lazy meaning ignores an unused divergent argument.
-/

public section

open OmegaCompletePartialOrder

namespace Examples.ScopedDomains

open IPFunctor IPFunctor.ScopedSignature

/-- Natural numbers and functions. -/
inductive Ty where
  | nat
  | arrow (argument result : Ty)

/-- Constructors, indexed by their result type. -/
inductive Op : Ty → Type where
  | zero : Op .nat
  | succ : Op .nat
  | ifz (a : Ty) : Op a
  | lam (a b : Ty) : Op (.arrow a b)
  | app (a b : Ty) : Op b
  | fix (a : Ty) : Op a

/-- The number of arguments of each constructor. -/
@[expose, reducible] def Op.arity : {a : Ty} → Op a → Nat
  | _, .zero => 0
  | _, .succ | _, .lam _ _ | _, .fix _ => 1
  | _, .app _ _ => 2
  | _, .ifz _ => 3

/-- `ifz n z s` binds the predecessor in `s`; `lam` and `fix` bind their own argument. -/
@[expose, reducible] def signature : ScopedSignature Ty where
  Op := Op
  Arg op := Fin op.arity
  binders op := match op with
    | .zero => Fin.elim0
    | .succ | .app _ _ => fun _ => []
    | .ifz _ => Fin.cases [] (Fin.cases [] (fun _ => [.nat]))
    | .lam a _ | .fix a => fun _ => [a]
  sort op := match op with
    | .zero => Fin.elim0
    | .succ => fun _ => .nat
    | .ifz a => Fin.cases .nat (fun _ => a)
    | .lam _ b => fun _ => b
    | .app a b => Fin.cases (.arrow a b) (fun _ => a)
    | .fix a => fun _ => a

/-- Typed terms over the signature. -/
abbrev Expr := signature.Term

namespace Expr

variable {Γ : List Ty} {a b : Ty}

/-- The number zero. -/
@[expose] def zero : Expr Γ .nat := .node .zero (fun p => nomatch p)

/-- The successor of a number. -/
@[expose] def succ (n : Expr Γ .nat) : Expr Γ .nat := .node .succ (fun _ => n)

/-- Test a number for zero, binding its predecessor otherwise. -/
@[expose] def ifz (n : Expr Γ .nat) (z : Expr Γ a) (s : Expr (.nat :: Γ) a) : Expr Γ a :=
  .node (.ifz a) (Fin.cases n (Fin.cases z (fun _ => s)))

/-- Function abstraction. -/
@[expose] def lam (body : Expr (a :: Γ) b) : Expr Γ (.arrow a b) := .node (.lam a b) (fun _ => body)

/-- Application, passing the argument unevaluated. -/
@[expose] def app (f : Expr Γ (.arrow a b)) (x : Expr Γ a) : Expr Γ b :=
  .node (.app a b) (Fin.cases f (fun _ => x))

/-- General recursion: the body sees its own meaning. -/
@[expose] def fix (body : Expr (a :: Γ) a) : Expr Γ a := .node (.fix a) (fun _ => body)

end Expr

/-! ## Lazy meaning -/

/-- Values: numbers, and continuous maps of suspended arguments. -/
@[expose, implicit_reducible] noncomputable def Ty.value : Ty → ωCPO.{0}
  | .nat => ωCPO.of (DiscreteOrder ℕ)
  | .arrow a b => ωCPO.of (DomainResult Empty a.value →𝒄 DomainResult Empty b.value)

/-- Computations: bottom, or the availability of a value's outer constructor. -/
@[expose, reducible] noncomputable def Ty.domain (a : Ty) : PointedDomain.{0} :=
  .ofType (DomainResult Empty a.value)

/-- A number as a lazy computation. -/
@[expose] noncomputable def number (n : ℕ) : Ty.nat.domain := DomainResult.value ⟨n⟩

/-- A one-variable environment. -/
@[expose] noncomputable def single {a : Ty} : a.domain →𝒄 ScopedDomain.Env Ty.domain [a] :=
  .ofFun (fun x => ScopedDomain.Env.cons Ty.domain x (ScopedDomain.Env.empty Ty.domain)) (by
    apply ωScottContinuous.of_apply₂
    intro b
    apply ωScottContinuous.of_apply₂
    intro v
    cases v with
    | zero => exact ωScottContinuous.id
    | succ v => exact nomatch v)

/-- The continuous body of a one-variable binder. -/
@[expose] noncomputable def body {a b : Ty} :
    (ScopedDomain.Env Ty.domain [a] →𝒄 b.domain) →𝒄 (a.domain →𝒄 b.domain) :=
  .ofFun (fun k => k.comp single) (by
    apply ContinuousHom.ωScottContinuous_of_apply
    intro x
    change ωScottContinuous (fun k : ScopedDomain.Env Ty.domain [a] →𝒄 b.domain => k (single x))
    fun_prop)

/-- Continue with the zero branch, or with the successor branch at the predecessor. -/
@[expose] noncomputable def branch {a : Ty} :
    (a.domain × (Ty.nat.domain →𝒄 a.domain)) →𝒄 (DiscreteOrder ℕ →𝒄 a.domain) :=
  .ofFun (fun p => DiscreteOrder.continuousMap fun n : ℕ => match n with
      | 0 => p.1
      | m + 1 => p.2 (number m)) (by
    apply ContinuousHom.ωScottContinuous_of_apply
    intro n
    rcases n with ⟨_ | m⟩
    · exact Prod.ωScottContinuous_fst
    · change ωScottContinuous fun p : a.domain × (Ty.nat.domain →𝒄 a.domain) => p.2 (number m)
      fun_prop)

/-- The constructor algebra; `fix` takes the least fixed point of its body. -/
@[expose] noncomputable def algebra : DomainInterpretation signature Ty.domain
  | _, .zero => .const (number 0)
  | _, .succ => .ofFun (fun k => DomainResult.bind
      (DiscreteOrder.continuousMap fun n : ℕ => number (n + 1))
      (k 0 (ScopedDomain.Env.empty Ty.domain)))
  | _, .ifz _ => .ofFun (fun k => DomainResult.elimContinuous Empty.elim
      (branch (k 1 (ScopedDomain.Env.empty Ty.domain), body (k 2)))
      (k 0 (ScopedDomain.Env.empty Ty.domain)))
  | _, .lam _ _ => DomainResult.valueContinuous.comp (body.comp (.ofFun (fun k => k 0)))
  | _, .app _ _ => .ofFun (fun k =>
      DomainResult.applyContinuous (k 0 (ScopedDomain.Env.empty Ty.domain))
        (k 1 (ScopedDomain.Env.empty Ty.domain)))
  | _, .fix _ => ContinuousHom.fixContinuous.comp (body.comp (.ofFun (fun k => k 0)))

/-- The lazy meaning of a closed term. -/
@[expose] noncomputable def meaning {a : Ty} (t : Expr [] a) : a.domain :=
  t.denoteDomain algebra (ScopedDomain.Env.empty Ty.domain)

/-! ## A total evaluator and the fundamental lemma -/

/-- Native results: numbers, and partial functions on native arguments. -/
@[expose, reducible] def Ty.native : Ty → Type
  | .nat => ℕ
  | .arrow a b => a.native → Option b.native

/-- An evaluation outcome: a native result, or no answer. -/
@[expose, reducible] def Ty.result (a : Ty) : Type := Option a.native

/-- Call-by-value evaluation of the recursion-free fragment; `fix` is unsupported. -/
@[expose] def evaluator : Interpretation signature Ty.result
  | _, .zero, _ => some (0 : ℕ)
  | _, .succ, k => (k 0 Env.empty).map fun n : ℕ => n + 1
  | _, .ifz _, k => (k 0 Env.empty).bind fun n : ℕ => match n with
      | 0 => k 1 Env.empty
      | m + 1 => k 2 (Env.cons (V := Ty.result) (some m) Env.empty)
  | _, .lam a _, k => some fun x : a.native => k 0 (Env.cons (V := Ty.result) (some x) Env.empty)
  | _, .app a b, k => (k 0 Env.empty).bind fun f : a.native → Option b.native =>
      (k 1 Env.empty).bind f
  | _, .fix _, _ => none

/-- A lazy computation represents a native result. -/
@[expose] def Represents : (a : Ty) → a.domain → a.native → Prop
  | .nat, d, n => d = number n
  | .arrow a b, d, f => ∃ g : a.domain →𝒄 b.domain, d = DomainResult.value g ∧
      ∀ e x, Represents a e x → ∀ y, f x = some y → Represents b (g e) y

/-- Every result the evaluator returns is represented by the lazy meaning. -/
@[expose] def Agrees (a : Ty) (d : a.domain) (v : a.result) : Prop :=
  ∀ x, v = some x → Represents a d x

theorem agrees_none (a : Ty) (d : a.domain) : Agrees a d none := fun _ h => nomatch h

theorem envRelated_empty :
    EnvRelated Agrees (ScopedDomain.Env.empty Ty.domain) (Env.empty (V := Ty.result)) :=
  fun _ x => nomatch x

theorem envRelated_single {a : Ty} {e : a.domain} {x : a.native} (h : Represents a e x) :
    EnvRelated Agrees (single e) (Env.cons (V := Ty.result) (some x) Env.empty) := by
  intro b v
  cases v with
  | zero => rintro _ ⟨⟩; exact h
  | succ v => exact nomatch v

/-- The only constructor-local proof: each constructor preserves agreement. -/
theorem algebra_related : DomainInterpretation.Related Agrees algebra evaluator := by
  intro a op k k' hk
  cases op with
  | zero => rintro _ ⟨⟩; rfl
  | succ =>
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp hx
      have h := hk 0 _ _ envRelated_empty n hn
      change DomainResult.bind _ (k 0 _) = _
      rw [show k 0 (ScopedDomain.Env.empty Ty.domain) = number n from h]
      rfl
  | ifz =>
      intro x hx
      obtain ⟨n, hn, hx⟩ := Option.bind_eq_some_iff.mp hx
      change ℕ at n
      have h : k 0 (ScopedDomain.Env.empty Ty.domain) = number n :=
        hk 0 _ _ envRelated_empty n hn
      have step : algebra (Op.ifz a) k =
          branch (k 1 (ScopedDomain.Env.empty Ty.domain), body (k 2)) ⟨n⟩ := by
        rw [show algebra (Op.ifz a) k = DomainResult.elim (β := a.domain) Empty.elim
          (branch (k 1 (ScopedDomain.Env.empty Ty.domain), body (k 2)))
          (k 0 (ScopedDomain.Env.empty Ty.domain)) from rfl, h]
        rfl
      rw [step]
      rcases n with _ | m
      · exact hk 1 _ _ envRelated_empty x hx
      · exact hk 2 _ _ (envRelated_single rfl) x hx
  | lam a b =>
      rintro _ ⟨⟩
      exact ⟨body (k 0), rfl, fun e x hex y hy =>
        hk 0 (single e) _ (envRelated_single hex) y hy⟩
  | app a b =>
      intro y hy
      obtain ⟨f, hf, hy⟩ := Option.bind_eq_some_iff.mp hy
      obtain ⟨x, hx, hy⟩ := Option.bind_eq_some_iff.mp hy
      obtain ⟨g, hg, hfg⟩ := hk 0 _ _ envRelated_empty f hf
      have hxe := hk 1 _ _ envRelated_empty x hx
      have step : DomainResult.applyContinuous (k 0 (ScopedDomain.Env.empty Ty.domain))
          (k 1 (ScopedDomain.Env.empty Ty.domain)) =
            g (k 1 (ScopedDomain.Env.empty Ty.domain)) := by
        rw [hg]
        rfl
      change Represents _ (DomainResult.applyContinuous (k 0 _) (k 1 _)) y
      rw [step]
      exact hfg _ x hxe y hy
  | fix a => exact agrees_none _ _

/-- Whenever the evaluator returns a value, the lazy meaning represents it. -/
theorem meaning_represents {a : Ty} (t : Expr [] a) (x : a.native)
    (h : t.denote evaluator Env.empty = some x) : Represents a (meaning t) x :=
  Term.denoteDomain_related algebra_related t envRelated_empty x h

/-- In particular, an evaluated number is the lazy meaning. -/
theorem meaning_eq_number (t : Expr [] .nat) (n : ℕ)
    (h : t.denote evaluator Env.empty = some n) : meaning t = number n :=
  meaning_represents t n h

/-! ## What only the lazy meaning sees -/

/-- A divergent number. -/
@[expose] def diverge : Expr [] .nat := .fix (.var .zero)

theorem meaning_diverge : meaning diverge = ⊥ :=
  le_bot_iff.mp (ContinuousHom.fix_le _ (le_refl _))

/-- An unused divergent argument is never demanded. -/
theorem meaning_const : meaning (.app (.lam .zero) diverge) = number 0 := rfl

/-- The call-by-value evaluator gives up on the same term. -/
theorem evaluator_const : (Expr.app (.lam .zero) diverge).denote evaluator Env.empty = none := rfl

/-- Beta reduction holds in the lazy meaning, through the generic substitution law. -/
theorem meaning_beta {a b : Ty} (t : Expr [a] b) (x : Expr [] a) :
    meaning (.app (.lam t) x) = meaning (t.substOne x) := by
  rw [meaning, meaning, Term.denoteDomain_substOne]
  rfl

end Examples.ScopedDomains
