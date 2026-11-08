/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

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

end Examples.ScopedDomains
