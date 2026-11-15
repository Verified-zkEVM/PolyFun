/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Domain.ResultRel
public import PolyFun.IPFunctor.Scoped.Adequacy
public import PolyFun.IPFunctor.Scoped.Certificate
public import Mathlib.Order.Category.OmegaCompletePartialOrder

/-!
# A lazy language with general recursion

A call-by-name language with natural numbers, functions and a fixed-point constructor. Its
meaning is a `DomainInterpretation`: each constructor combines the continuous meanings of its
arguments. So `fix` is a least fixed point and an unused argument is never demanded. The
substitution laws come from the generic API.

A call-by-value evaluator for the recursion-free fragment is an ordinary `Interpretation` into
`Option`. One constructor-local lemma relates the two, and `Term.denoteDomain_related` lifts it
to every term: whenever the evaluator returns a value, the lazy meaning represents it. The
converse fails, because the lazy meaning ignores an unused divergent argument.

With a representation of numbers, the same lemma certifies programs. A program with one
numeric input whose evaluation returns `implementation n` at every input `n` has a
`CertifiedMeaning` (`addTwoCertified`). A program that the evaluator handles only on some
inputs corresponds to its implementation there (`pred_correspondsOn`). A decoder into results
over native numbers composes with a certificate (`addTwoDecoded`).

The lazy meaning is also adequate for a call-by-name evaluator. A closed numeric term means `n`
exactly when it evaluates to the numeral `n`, and a closed term means bottom exactly when it
does not evaluate (`meaning_eq_number_iff`, `meaning_eq_bot_iff`). Soundness follows from the
substitution law. The converse follows from a syntactic logical relation, which
`Term.denoteDomain_relatedSyntax` proves for every term from one case per constructor.
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
@[expose] def lam (body : Expr (a :: Γ) b) : Expr Γ (.arrow a b) :=
  .node (.lam a b) (fun _ => body)

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
abbrev Ty.Comp (a : Ty) : Type := DomainResult Empty a.value

/-- A number as a lazy computation. -/
@[expose] noncomputable def number (n : ℕ) : Ty.nat.Comp := DomainResult.value ⟨n⟩

/-- Continue with the zero branch, or with the successor branch at the predecessor. -/
@[expose] noncomputable def branch {a : Ty} :
    (a.Comp × (Ty.nat.Comp →𝒄 a.Comp)) →𝒄 (DiscreteOrder ℕ →𝒄 a.Comp) :=
  .ofFun (fun p => DiscreteOrder.continuousMap fun n : ℕ => match n with
      | 0 => p.1
      | m + 1 => p.2 (number m)) (by
    apply ContinuousHom.ωScottContinuous_of_apply
    intro n
    rcases n with ⟨_ | m⟩
    · exact Prod.ωScottContinuous_fst
    · change ωScottContinuous fun p : a.Comp × (Ty.nat.Comp →𝒄 a.Comp) => p.2 (number m)
      fun_prop)

/-- The constructor algebra; `fix` takes the least fixed point of its body. An abstraction's value
is `Env.abstraction` of its body's meaning, written as an `ofFun` clause rather than a composite,
so that the kernel checks equations between nested abstractions in time linear in their depth. -/
@[expose] noncomputable def algebra : DomainInterpretation signature Ty.Comp
  | _, .zero => .const (number 0)
  | _, .succ => .ofFun (fun k => DomainResult.bind
      (DiscreteOrder.continuousMap fun n : ℕ => number (n + 1)) (k 0 Env.empty))
  | _, .ifz _ => .ofFun (fun k => DomainResult.elimContinuous Empty.elim
      (branch (k 1 Env.empty, Env.bindOne (k 2))) (k 0 Env.empty))
  | _, .lam _ _ => .ofFun (fun k => DomainResult.value (Env.abstraction (k 0)))
      (DomainResult.valueContinuous.ωScottContinuous.comp
        (Env.abstractionContinuous.ωScottContinuous.comp (ωScottContinuous.apply 0)))
  | _, .app _ _ => .ofFun (fun k =>
      DomainResult.applyContinuous (k 0 Env.empty) (k 1 Env.empty))
  | _, .fix a => ContinuousHom.fixContinuous.comp (Env.bindOne.comp
      (.ofFun (fun k : (_ : Fin 1) → Env Ty.Comp [a] →𝒄 a.Comp => k 0)))

/-- The lazy meaning of a closed term. -/
@[expose] noncomputable def meaning {a : Ty} (t : Expr [] a) : a.Comp :=
  t.denoteDomain algebra Env.empty

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
      | m + 1 => k 2 (Env.single (V := Ty.result) (some m))
  | _, .lam a _, k => some fun x : a.native => k 0 (Env.single (V := Ty.result) (some x))
  | _, .app a b, k => (k 0 Env.empty).bind fun f : a.native → Option b.native =>
      (k 1 Env.empty).bind f
  | _, .fix _, _ => none

/-- A lazy computation represents a native result. -/
@[expose] def Represents : (a : Ty) → a.Comp → a.native → Prop
  | .nat, d, n => d = number n
  | .arrow a b, d, f => ∃ g : a.Comp →𝒄 b.Comp, d = DomainResult.value g ∧
      ∀ e x, Represents a e x → ∀ y, f x = some y → Represents b (g e) y

/-- Every result the evaluator returns is represented by the lazy meaning. -/
@[expose] def Agrees (a : Ty) (d : a.Comp) (v : a.result) : Prop :=
  ∀ x, v = some x → Represents a d x

theorem agrees_none (a : Ty) (d : a.Comp) : Agrees a d none := fun _ h => nomatch h

theorem liftRel_single {a : Ty} {e : a.Comp} {x : a.native} (h : Represents a e x) :
    Env.LiftRel Agrees (Env.single e) (Env.single (V := Ty.result) (some x)) :=
  (Env.liftRel_empty _).cons fun _ hx => Option.some.inj hx ▸ h

/-- The only constructor-local proof: each constructor preserves agreement. -/
theorem algebra_related : DomainInterpretation.Related Agrees algebra evaluator := by
  intro a op k k' hk
  cases op with
  | zero => rintro _ ⟨⟩; rfl
  | succ =>
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp hx
      have h : k 0 Env.empty = number n := hk 0 _ _ (Env.liftRel_empty _) n hn
      change DomainResult.bind _ (k 0 _) = _
      rw [h]
      rfl
  | ifz =>
      intro x hx
      obtain ⟨n, hn, hx⟩ := Option.bind_eq_some_iff.mp hx
      change ℕ at n
      have h : k 0 Env.empty = number n := hk 0 _ _ (Env.liftRel_empty _) n hn
      have step : algebra (Op.ifz a) k =
          branch (k 1 Env.empty, Env.bindOne (k 2)) ⟨n⟩ := by
        rw [show algebra (Op.ifz a) k = DomainResult.elim (β := a.Comp) Empty.elim
          (branch (k 1 Env.empty, Env.bindOne (k 2))) (k 0 Env.empty) from rfl, h]
        rfl
      rw [step]
      rcases n with _ | m
      · exact hk 1 _ _ (Env.liftRel_empty _) x hx
      · exact hk 2 _ _ (liftRel_single (show Represents .nat (number m) m from rfl)) x hx
  | lam a b =>
      rintro _ ⟨⟩
      exact ⟨Env.abstraction (k 0), rfl, fun e x hex y hy =>
        hk 0 (Env.single e) _ (liftRel_single hex) y hy⟩
  | app a b =>
      intro y hy
      obtain ⟨f, hf, hy⟩ := Option.bind_eq_some_iff.mp hy
      obtain ⟨x, hx, hy⟩ := Option.bind_eq_some_iff.mp hy
      obtain ⟨g, hg, hfg⟩ := hk 0 _ _ (Env.liftRel_empty _) f hf
      have hxe := hk 1 _ _ (Env.liftRel_empty _) x hx
      have step : DomainResult.applyContinuous (k 0 Env.empty) (k 1 Env.empty) =
          g (k 1 Env.empty) := by
        rw [hg]
        rfl
      change Represents _ (DomainResult.applyContinuous (k 0 _) (k 1 _)) y
      rw [step]
      exact hfg _ x hxe y hy
  | fix a => exact agrees_none _ _

/-- Whenever the evaluator returns a value, the lazy meaning represents it. -/
theorem meaning_represents {a : Ty} (t : Expr [] a) (x : a.native)
    (h : t.denote evaluator Env.empty = some x) : Represents a (meaning t) x :=
  Term.denoteDomain_related algebra_related t (Env.liftRel_empty _) x h

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
theorem evaluator_const :
    (Expr.app (.lam .zero) diverge).denote evaluator Env.empty = none := rfl

/-- Beta reduction holds in the lazy meaning, through the generic substitution law. -/
theorem meaning_beta {a b : Ty} (t : Expr [a] b) (x : Expr [] a) :
    meaning (.app (.lam t) x) = meaning (t.substOne x) := by
  rw [meaning, meaning, Term.denoteDomain_substOne]
  rfl

/-! ## Certified evaluation

A program with one numeric input is a term in the context `[.nat]`. Numbers are represented
faithfully: a computation agrees with an evaluated number exactly when it is that number. So the
fundamental lemma and the evaluator's result at each input certify the lazy meaning. -/

section Certified

open Control.Semantics

/-- Numbers embed faithfully into numeric computations. -/
@[expose] noncomputable def natEmbedding : ℕ ↪ Ty.nat.Comp :=
  ⟨number, fun _ _ h => congrArg DiscreteOrder.value (DomainResult.value_inj.mp h)⟩

/-- A numeric computation agrees with an evaluated number exactly when it is that number. -/
theorem agrees_some_iff (d : Ty.nat.Comp) (n : ℕ) : Agrees .nat d (some n) ↔ d = number n :=
  ⟨fun h => h n rfl, fun h _ hx => Option.some.inj hx ▸ h⟩

/-- Add two to the input. -/
@[expose] def addTwo : Expr [.nat] .nat := .succ (.succ (.var .zero))

/-- The lazy meaning of `addTwo` returns the encoding of `n + 2` at the encoding of every `n`.
The evaluator computes `n + 2` definitionally. -/
@[expose] noncomputable def addTwoCertified : CertifiedMeaning natEmbedding natEmbedding :=
  addTwo.certifiedMeaning algebra_related (nativeIn := some) (nativeOut := some)
    (fun n => (agrees_some_iff _ n).2 rfl) (fun n d h => (agrees_some_iff d n).1 h) (· + 2)
    (fun _ => rfl)

/-- A native contract transfers to the lazy meaning on encoded inputs. -/
theorem addTwo_contract :
    DataContract natEmbedding natEmbedding addTwoCertified.meaning (fun _ => True)
      (fun n m => n < m) :=
  (addTwoCertified.contract_iff _ _).2 fun n _ => Nat.lt_add_of_pos_right (by decide)

/-- The predecessor. At zero the program takes a divergent branch. -/
@[expose] def pred : Expr [.nat] .nat := .ifz (.var .zero) (.fix (.var .zero)) (.var .zero)

/-- The evaluator handles `pred` only on positive inputs, so its lazy meaning corresponds to
`(· - 1)` there. The correspondence promises nothing at zero. -/
theorem pred_correspondsOn :
    CorrespondsOn natEmbedding natEmbedding (0 < ·)
      (fun d => pred.denoteDomain algebra (Env.single d)) (· - 1) :=
  pred.correspondsOn_denoteDomain algebra_related (nativeIn := some) (nativeOut := some)
    (fun n _ => (agrees_some_iff _ n).2 rfl) (fun n d h => (agrees_some_iff d n).1 h)
    (fun n hn => match n, hn with | _ + 1, _ => rfl)

/-- At zero, the lazy meaning of `pred` diverges. -/
theorem pred_zero : pred.denoteDomain algebra (Env.single (number 0)) = ⊥ :=
  le_bot_iff.mp (ContinuousHom.fix_le _ (le_refl _))

/-- Read a numeric computation as a result over native numbers. -/
@[expose] noncomputable def decodeNat : Ty.nat.Comp → DomainResult Empty ℕ :=
  DomainResult.map DiscreteOrder.value

/-- An encoded number decodes to that number. -/
@[expose] noncomputable def decodeNatCertified :
    CertifiedMeaning natEmbedding (DomainResult.valueEmbedding : ℕ ↪ DomainResult Empty ℕ) where
  meaning := decodeNat
  implementation := id
  correct _ := rfl

/-- The decoded lazy meaning of `addTwo`, certified against `(· + 2)`. -/
@[expose] noncomputable def addTwoDecoded :
    CertifiedMeaning natEmbedding (DomainResult.valueEmbedding : ℕ ↪ DomainResult Empty ℕ) :=
  decodeNatCertified.comp addTwoCertified

/-- At every native input, the decoded lazy meaning returns `n + 2` as a value: it neither
diverges nor fails. -/
theorem decodeNat_addTwo (n : ℕ) :
    decodeNat (addTwo.denoteDomain algebra (Env.single (number n))) =
      DomainResult.value (n + 2) :=
  addTwoDecoded.correct n

end Certified

/-! ## Call-by-name evaluation and adequacy

A big-step call-by-name evaluator runs closed terms to numerals and abstractions. It passes each
argument unevaluated, closing a body with `Term.instantiate`. A semantic value is related to a
closed term when the term evaluates to a related value term, and bottom is related to every term.
The relation is admissible, because evaluation is deterministic, so the fixed-point case is
fixed-point induction. -/

section Adequacy

/-- The numeral of a number. -/
@[expose] def numeral : ℕ → Expr [] .nat
  | 0 => .zero
  | n + 1 => .succ (numeral n)

/-- The children of a closed node. -/
abbrev Args {a : Ty} (op : Op a) :=
  (p : signature.Arg op) → Expr (signature.binders op p ++ []) (signature.sort op p)

/-- Big-step call-by-name evaluation of closed terms to numerals and abstractions. Each rule
matches a node through its whole argument function, so that two evaluations of one term can be
compared by `cases`. -/
inductive Eval : {a : Ty} → Expr [] a → Expr [] a → Prop where
  | zero {args : Args .zero} : Eval (.node .zero args) (numeral 0)
  | succ {args : Args .succ} {n : ℕ} :
      Eval (args 0) (numeral n) → Eval (.node .succ args) (numeral (n + 1))
  | ifzZero {a : Ty} {args : Args (.ifz a)} {v : Expr [] a} :
      Eval (args 0) (numeral 0) → Eval (args 1) v → Eval (.node (.ifz a) args) v
  | ifzSucc {a : Ty} {args : Args (.ifz a)} {n : ℕ} {v : Expr [] a} :
      Eval (args 0) (numeral (n + 1)) →
        Eval ((args 2).instantiate (Env.single (numeral n))) v → Eval (.node (.ifz a) args) v
  | lam {a b : Ty} {args : Args (.lam a b)} :
      Eval (.node (.lam a b) args) (.node (.lam a b) args)
  | app {a b : Ty} {args : Args (.app a b)} {body : Args (.lam a b)} {v : Expr [] b} :
      Eval (args 0) (.node (.lam a b) body) →
        Eval ((body 0).instantiate (Env.single (args 1))) v → Eval (.node (.app a b) args) v
  | fix {a : Ty} {args : Args (.fix a)} {v : Expr [] a} :
      Eval ((args 0).instantiate (Env.single (.node (.fix a) args))) v →
        Eval (.node (.fix a) args) v

theorem numeral_injective : Function.Injective numeral := by
  intro m n h
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => cases h
  | succ m ih =>
    cases n with
    | zero => cases h
    | succ n => exact congrArg (· + 1) (ih (congrFun (eq_of_heq (IFreeM.liftBind.inj h).2) 0))

/-- Evaluation is deterministic. -/
theorem Eval.unique {a : Ty} {e v w : Expr [] a} (h : Eval e v) (h' : Eval e w) : v = w := by
  induction h with
  | zero => cases h'; rfl
  | succ _ ih =>
    cases h' with
    | succ h' => rw [numeral_injective (ih h')]
  | ifzZero _ _ ih₀ ih₁ =>
    cases h' with
    | ifzZero _ h₁ => exact ih₁ h₁
    | ifzSucc h₀ _ => exact absurd (numeral_injective (ih₀ h₀)) (Nat.succ_ne_zero _).symm
  | ifzSucc _ _ ih₀ ih₁ =>
    cases h' with
    | ifzZero h₀ _ => exact absurd (numeral_injective (ih₀ h₀)) (Nat.succ_ne_zero _)
    | ifzSucc h₀ h₁ =>
      obtain rfl := Nat.succ.inj (numeral_injective (ih₀ h₀))
      exact ih₁ h₁
  | lam => cases h'; rfl
  | app _ _ ih₀ ih₁ =>
    cases h' with
    | app h₀ h₁ =>
      cases ih₀ h₀
      exact ih₁ h₁
  | fix _ ih =>
    cases h' with
    | fix h₁ => exact ih h₁

/-- Computations related to closed terms by a relation `VR` on values: bottom is related to every
term, and a returned value to a term that evaluates to a related value term. -/
@[expose] def RelatedBy {a : Ty} (VR : a.value → Expr [] a → Prop) (d : a.Comp)
    (e : Expr [] a) : Prop :=
  d = ⊥ ∨ ∃ r : DomainResult Empty (Expr [] a), (∃ w, Eval e w ∧ r = DomainResult.value w) ∧
    DomainResult.LiftRel (fun e _ => e.elim) VR d r

/-- Related values: a number to its numeral, and a function to an abstraction whose body, closed
by any term related to an argument, is related to the function's result there. -/
@[expose] def ValueRel : (a : Ty) → a.value → Expr [] a → Prop
  | .nat, n, w => w = numeral (DiscreteOrder.value n)
  | .arrow a b, g, w => (∃ body : Args (.lam a b), w = .node (.lam a b) body) ∧
      ∀ body : Args (.lam a b), w = .node (.lam a b) body → ∀ x arg, RelatedBy (ValueRel a) x arg →
        RelatedBy (ValueRel b) ((show a.Comp →𝒄 b.Comp from g) x)
          ((body 0).instantiate (Env.single arg))

/-- The logical relation between computations and closed terms. -/
abbrev Related {a : Ty} : a.Comp → Expr [] a → Prop := RelatedBy (ValueRel a)

theorem related_bot {a : Ty} (e : Expr [] a) : Related ⊥ e := Or.inl rfl

theorem related_value_iff {a : Ty} {v : a.value} {e : Expr [] a} :
    Related (DomainResult.value v) e ↔ ∃ w, Eval e w ∧ ValueRel a v w := by
  constructor
  · rintro (h | ⟨r, ⟨w, hw, rfl⟩, hr⟩)
    · exact absurd h (DomainResult.value_ne_bot v)
    · exact ⟨w, hw, (DomainResult.liftRel_value_value _ _).mp hr⟩
  · rintro ⟨w, hw, hv⟩
    exact Or.inr ⟨_, ⟨w, hw, rfl⟩, (DomainResult.liftRel_value_value _ _).mpr hv⟩

/-- A term related to a computation stays related to it when it evaluates to everything that the
first term evaluates to. -/
theorem Related.expand {a : Ty} {d : a.Comp} {e e' : Expr [] a} (h : Related d e')
    (he : ∀ w, Eval e' w → Eval e w) : Related d e := by
  rcases h with h | ⟨r, ⟨w, hw, rfl⟩, hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, ⟨w, he w hw, rfl⟩, hr⟩

/-- An argument with no binders, closed by the empty environment, is the argument itself. -/
theorem Related.of_instantiate_nil {a : Ty} {d : a.Comp} {c : Expr [] a}
    (h : Related d (c.instantiate (Ξ := []) Env.empty)) : Related d c := by
  rwa [Term.instantiate_nil] at h

theorem eval_numeral (n : ℕ) : Eval (numeral n) (numeral n) := by
  induction n with
  | zero => exact Eval.zero
  | succ n ih => exact Eval.succ ih

theorem related_number (n : ℕ) : Related (number n) (numeral n) :=
  related_value_iff.mpr ⟨_, eval_numeral n, rfl⟩

/-- Relations of this shape are closed under suprema of chains, because evaluation is
deterministic. -/
theorem admissible_relatedBy {a : Ty} {VR : a.value → Expr [] a → Prop}
    (hVR : ∀ w, Admissible fun v : a.value => VR v w) (e : Expr [] a) :
    Admissible fun d : a.Comp => RelatedBy VR d e :=
  DomainResult.admissible_bot_or_liftRel (fun _ _ ⟨_, hw, hr⟩ ⟨_, hw', hr'⟩ => by
    rw [hr, hr', hw.unique hw']) hVR

theorem admissible_valueRel : (a : Ty) → (w : Expr [] a) →
    Admissible fun v : a.value => ValueRel a v w
  | .nat, _ => admissible_discrete _
  | .arrow a b, _ => fun c hc => ⟨(hc 0).1, fun body hbody x arg harg =>
      ((admissible_relatedBy (admissible_valueRel b) _).comp
        (.ofFun fun g : a.Comp →𝒄 b.Comp => g x)) c fun n => (hc n).2 body hbody x arg harg⟩

theorem admissible_related {a : Ty} (e : Expr [] a) : Admissible fun d : a.Comp => Related d e :=
  admissible_relatedBy (admissible_valueRel a) e

/-- Each constructor preserves the relation. With it, `Term.denoteDomain_relatedSyntax` relates
every term. -/
theorem algebra_relatedSyntax :
    DomainInterpretation.RelatedSyntax (fun a => Related (a := a)) algebra := by
  intro a op k c hk
  cases op with
  | zero => exact related_value_iff.mpr ⟨_, Eval.zero, rfl⟩
  | succ =>
    have h0 := Related.of_instantiate_nil (hk 0 Env.empty Env.empty (Env.liftRel_empty _))
    change Related (DomainResult.bind (DiscreteOrder.continuousMap fun n : ℕ => number (n + 1))
      (k 0 Env.empty)) _
    generalize k 0 Env.empty = d at h0 ⊢
    induction d using DomainResult.inductionOn with
    | bot => exact related_bot _
    | error e => exact e.elim
    | value v =>
      obtain ⟨w, hw, rfl⟩ := related_value_iff.mp h0
      exact related_value_iff.mpr ⟨_, Eval.succ hw, rfl⟩
  | ifz a =>
    have h0 := Related.of_instantiate_nil (hk 0 Env.empty Env.empty (Env.liftRel_empty _))
    have h1 := Related.of_instantiate_nil (hk 1 Env.empty Env.empty (Env.liftRel_empty _))
    change Related (DomainResult.elim (β := a.Comp) Empty.elim
      (branch (k 1 Env.empty, Env.bindOne (k 2))) (k 0 Env.empty)) _
    generalize k 0 Env.empty = d at h0 ⊢
    induction d using DomainResult.inductionOn with
    | bot => exact related_bot _
    | error e => exact e.elim
    | value v =>
      obtain ⟨w, hw, rfl⟩ := related_value_iff.mp h0
      rcases v with ⟨_ | n⟩
      · exact h1.expand fun _ hv => Eval.ifzZero hw hv
      · exact (hk 2 (Env.single (number n)) (Env.single (numeral n))
          ((Env.liftRel_empty _).cons (related_number n))).expand fun _ hv => Eval.ifzSucc hw hv
  | lam a b =>
    refine related_value_iff.mpr ⟨_, Eval.lam, ⟨c, rfl⟩, fun body hbody x arg harg => ?_⟩
    cases hbody
    exact hk 0 (Env.single x) (Env.single arg) ((Env.liftRel_empty _).cons harg)
  | app a b =>
    have h0 := Related.of_instantiate_nil (hk 0 Env.empty Env.empty (Env.liftRel_empty _))
    have h1 := Related.of_instantiate_nil (hk 1 Env.empty Env.empty (Env.liftRel_empty _))
    change Related (DomainResult.applyContinuous (k 0 Env.empty) (k 1 Env.empty)) _
    generalize k 0 Env.empty = d at h0 ⊢
    induction d using DomainResult.inductionOn with
    | bot => exact related_bot _
    | error e => exact e.elim
    | value g =>
      obtain ⟨w, hw, ⟨body, rfl⟩, hg⟩ := related_value_iff.mp h0
      exact Related.expand (hg body rfl _ _ h1) fun _ hv => Eval.app hw hv
  | fix a =>
    change Related (ContinuousHom.fix (Env.bindOne (k 0))) (Term.node (.fix a) c)
    refine (admissible_related _).fix_induction _ (related_bot _) fun d hd => ?_
    exact (hk 0 (Env.single d) (Env.single (.node (.fix a) c))
      ((Env.liftRel_empty _).cons hd)).expand fun _ hv => Eval.fix hv

/-- Every closed term is related to its lazy meaning. -/
theorem meaning_related {a : Ty} (t : Expr [] a) : Related (meaning t) t :=
  Term.denoteDomain_relatedSyntax_closed algebra_relatedSyntax t

/-- A successor demands its argument. -/
theorem meaning_succ (args : Args .succ) :
    meaning (.node .succ args) =
      DomainResult.bind (DiscreteOrder.continuousMap fun n : ℕ => number (n + 1))
        (meaning (args 0)) := rfl

theorem meaning_numeral (n : ℕ) : meaning (numeral n) = number n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [numeral, Expr.succ, meaning_succ, ih]
    rfl

theorem meaning_instantiate_single {a b : Ty} (c : Expr [a] b) (x : Expr [] a) :
    meaning (c.instantiate (Env.single x)) = c.denoteDomain algebra (Env.single (meaning x)) := by
  rw [Term.instantiate_single, meaning, Term.denoteDomain_substOne]
  rfl

/-- A test for zero demands the tested number. -/
theorem meaning_ifz {a : Ty} (args : Args (.ifz a)) :
    meaning (.node (.ifz a) args) =
      DomainResult.elim (β := a.Comp) Empty.elim
        (branch (meaning (args 1),
          Env.bindOne (DomainInterpretation.under ((args 2).denoteDomain algebra) Env.empty)))
        (meaning (args 0)) := rfl

/-- An application demands the function and suspends the argument. -/
theorem meaning_app {a b : Ty} (args : Args (.app a b)) :
    meaning (.node (.app a b) args) =
      DomainResult.applyContinuous (meaning (args 0)) (meaning (args 1)) := rfl

/-- Evaluation preserves the lazy meaning. -/
theorem Eval.sound {a : Ty} {e w : Expr [] a} (h : Eval e w) : meaning e = meaning w := by
  induction h with
  | zero => rfl
  | @succ args n _ ih =>
    rw [meaning_succ, ih, meaning_numeral, meaning_numeral]
    rfl
  | @ifzZero a args v _ _ ih₀ ih₁ =>
    exact ((meaning_ifz args).trans (congrArg _ (ih₀.trans (meaning_numeral 0)))).trans ih₁
  | @ifzSucc a args n v _ _ ih₀ ih₁ =>
    refine ((meaning_ifz args).trans
      (congrArg _ (ih₀.trans (meaning_numeral (n + 1))))).trans ?_
    refine Eq.trans ?_ ((meaning_instantiate_single (args 2) (numeral n)).symm.trans ih₁)
    exact (congrArg (fun x => (args 2).denoteDomain algebra (Env.single x))
      (meaning_numeral n)).symm
  | lam => rfl
  | @app a b args body v _ _ ih₀ ih₁ =>
    refine ((meaning_app args).trans
      (congrArg (DomainResult.applyContinuous · (meaning (args 1))) ih₀)).trans ?_
    exact (meaning_instantiate_single (body 0) (args 1)).symm.trans ih₁
  | @fix a args v _ ih =>
    have hfix := ContinuousHom.map_fix
      (Env.bindOne (DomainInterpretation.under ((args 0).denoteDomain algebra) Env.empty))
    exact (hfix.symm.trans
      (meaning_instantiate_single (args 0) (.node (.fix a) args)).symm).trans ih

/-- The result of an evaluation means a returned value. -/
theorem Eval.meaning_ne_bot {a : Ty} {e w : Expr [] a} (h : Eval e w) : meaning w ≠ ⊥ := by
  induction h with
  | zero => exact DomainResult.value_ne_bot _
  | succ _ _ =>
    rw [meaning_numeral]
    exact DomainResult.value_ne_bot _
  | ifzZero _ _ _ ih₁ => exact ih₁
  | ifzSucc _ _ _ ih₁ => exact ih₁
  | lam => exact DomainResult.value_ne_bot _
  | app _ _ _ ih₁ => exact ih₁
  | fix _ ih => exact ih

/-- Adequacy at numbers: a closed numeric term means `n` exactly when it evaluates to the
numeral `n`. -/
theorem meaning_eq_number_iff (t : Expr [] .nat) (n : ℕ) :
    meaning t = number n ↔ Eval t (numeral n) := by
  refine ⟨fun h => ?_, fun h => h.sound.trans (meaning_numeral n)⟩
  have ht := meaning_related t
  rw [h] at ht
  obtain ⟨w, hw, rfl⟩ := related_value_iff.mp ht
  exact hw

/-- A closed term means bottom exactly when it does not evaluate. -/
theorem meaning_eq_bot_iff {a : Ty} (t : Expr [] a) : meaning t = ⊥ ↔ ∀ w, ¬Eval t w := by
  refine ⟨fun h w hw => hw.meaning_ne_bot (hw.sound.symm.trans h), fun h => ?_⟩
  rcases meaning_related t with ht | ⟨_, ⟨w, hw, -⟩, -⟩
  · exact ht
  · exact absurd hw (h w)

/-- The call-by-name evaluator passes the divergent argument unevaluated, so it returns zero
where the call-by-value evaluator gives up (`evaluator_const`). -/
theorem eval_const : Eval (.app (.lam .zero) diverge) (numeral 0) :=
  Eval.app Eval.lam Eval.zero

end Adequacy

end Examples.ScopedDomains
