/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.StackedInterpretation

/-!
# Size-indexed vectors as a two-level family

A small polymorphic language whose types mention sizes, built as a `Stacked` family. The type
level is a `ScopedSignature` with kinds `size`, `type` and `scheme`, and terms quantify over
sizes. A head is a shape with type annotations, and its result sort is computed from them.

* Applications keep their context exactly, so variables below them need no coercion
  (`twice`).
* A coercion between types of one shape is a head whose evidence is checked by evaluating the
  types; between `[m + n]nat` and `[n + m]nat` it is `rfl` (`swap`).
* Substitution does not return a written type definitionally after an instantiation, so a
  coercion follows it (`repSeven`).
* The value-substitution laws and the commutation of size substitution with value substitution
  are the generic `Stacked` lemmas.

The meanings are length-erased: a vector denotes a stream that ignores its length. A lazy
call-by-name meaning and a total evaluator interpret the heads through their evaluated
annotations. The lazy meaning represents the evaluator (`denoteDomain_related`), and size
instantiation commutes with the lazy meaning (`denoteDomain_map_closed`), with no proof for any
individual head.
-/

public section

namespace Examples.ScopedVectors

open OmegaCompletePartialOrder IPFunctor IPFunctor.ScopedSignature

/-! ## The type level

The type level is an ordinary binding signature. Sizes denote natural numbers, and the
evaluated types and schemes are small inductive types. -/

/-- Kinds of the type level. -/
inductive Kind where
  | size
  | type
  | scheme

/-- Type-level constructors: sizes, types and size-polymorphic schemes. -/
inductive TyOp : Kind → Type where
  | lit (n : ℕ) : TyOp .size
  | add : TyOp .size
  | nat : TyOp .type
  | vec : TyOp .type
  | arrow : TyOp .type
  | mono : TyOp .scheme
  | all : TyOp .scheme

/-- Children of a type-level constructor. -/
@[expose, reducible] def TyOp.Arg : {k : Kind} → TyOp k → Type
  | _, .lit _ | _, .nat => Empty
  | _, .mono | _, .all => Unit
  | _, .add | _, .vec | _, .arrow => Bool

/-- Only a quantifier binds a size parameter. -/
@[expose, reducible] def TyOp.binders : {k : Kind} → (o : TyOp k) → o.Arg → List Kind
  | _, .all => fun _ => [.size]
  | _, _ => fun _ => []

/-- Kinds of the children. -/
@[expose, reducible] def TyOp.sort : {k : Kind} → (o : TyOp k) → o.Arg → Kind
  | _, .lit _ => Empty.elim
  | _, .nat => Empty.elim
  | _, .add => fun _ => .size
  | _, .vec => fun b => cond b .type .size
  | _, .arrow => fun _ => .type
  | _, .mono => fun _ => .type
  | _, .all => fun _ => .scheme

/-- The type-level signature. -/
@[expose, reducible] def TySig : ScopedSignature Kind where
  Op := TyOp
  Arg := TyOp.Arg
  binders := TyOp.binders
  sort := TyOp.sort

/-- Type-level terms over ordered size parameters `Θ`. -/
abbrev TyTerm (Θ : List Kind) (k : Kind) := TySig.Term Θ k

namespace TyTerm

variable {Θ : List Kind}

/-- A size literal. -/
@[expose] def lit (n : ℕ) : TyTerm Θ .size := Term.node (TyOp.lit n) (fun p => nomatch p)
/-- The sum of two sizes. -/
@[expose] def add (m n : TyTerm Θ .size) : TyTerm Θ .size :=
  Term.node TyOp.add (fun p => match p with | false => m | true => n)
/-- Natural numbers. -/
@[expose] def nat : TyTerm Θ .type := Term.node TyOp.nat (fun p => nomatch p)
/-- Vectors of a given size. -/
@[expose] def vec (n : TyTerm Θ .size) (a : TyTerm Θ .type) : TyTerm Θ .type :=
  Term.node TyOp.vec (fun p => match p with | false => n | true => a)
/-- Functions. -/
@[expose] def arrow (a b : TyTerm Θ .type) : TyTerm Θ .type :=
  Term.node TyOp.arrow (fun p => match p with | false => a | true => b)
/-- A monomorphic scheme. -/
@[expose] def mono (t : TyTerm Θ .type) : TyTerm Θ .scheme := Term.node TyOp.mono (fun _ => t)
/-- Quantification over one size. -/
@[expose] def all (b : TyTerm (.size :: Θ) .scheme) : TyTerm Θ .scheme :=
  Term.node TyOp.all (fun _ => b)

variable {Θ' : List Kind} (θ : TySig.Substitution Θ Θ')

/-! Substitution through each two-child former needs a case split on the child; the unary
formers commute with substitution definitionally. -/

@[simp] theorem subst_lit (n : ℕ) : (lit n : TyTerm Θ _).subst θ = lit n := by
  simp only [lit, Term.subst_node]; congr 1; funext p; nomatch p
@[simp] theorem subst_nat : (nat : TyTerm Θ _).subst θ = nat := by
  simp only [nat, Term.subst_node]; congr 1; funext p; nomatch p
@[simp] theorem subst_mono (t : TyTerm Θ .type) : (mono t).subst θ = mono (t.subst θ) := rfl
@[simp] theorem subst_all (b : TyTerm (.size :: Θ) .scheme) :
    (all b).subst θ = all (b.subst (Substitution.lift θ .size)) := rfl
@[simp] theorem subst_add (m n : TyTerm Θ .size) :
    (add m n).subst θ = add (m.subst θ) (n.subst θ) := by
  simp only [add, Term.subst_node]; congr 1; funext p; cases p <;> rfl
@[simp] theorem subst_vec (n : TyTerm Θ .size) (a : TyTerm Θ .type) :
    (vec n a).subst θ = vec (n.subst θ) (a.subst θ) := by
  simp only [vec, Term.subst_node]; congr 1; funext p; cases p <;> rfl
@[simp] theorem subst_arrow (a b : TyTerm Θ .type) :
    (arrow a b).subst θ = arrow (a.subst θ) (b.subst θ) := by
  simp only [arrow, Term.subst_node]; congr 1; funext p; cases p <;> rfl

end TyTerm

open TyTerm

/-- Instantiation commutes with substitution. -/
theorem substOne_subst {Θ Θ' : List Kind} {k k' : Kind} (body : TyTerm (k :: Θ) k')
    (arg : TyTerm Θ k) (θ : TySig.Substitution Θ Θ') :
    (body.substOne arg).subst θ =
      (body.subst (Substitution.lift θ k)).substOne (arg.subst θ) := by
  rw [Term.substOne_subst_lift, Term.substOne, Term.subst_subst]
  congr 1
  funext c x
  cases x <;> rfl

/-- Evaluated types. -/
inductive TValue where
  | nat
  | vec (n : ℕ) (a : TValue)
  | arrow (a b : TValue)

/-- Evaluated schemes. -/
inductive SScheme where
  | mono (t : TValue)
  | all (f : ℕ → SScheme)

/-- Meanings of kinds. -/
@[expose, reducible] def Den : Kind → Type
  | .size => ℕ
  | .type => TValue
  | .scheme => SScheme

/-- The type-level fold. -/
@[expose] def tyAlgFn : {k : Kind} → (o : TyOp k) →
    ((p : o.Arg) → Env Den (o.binders p) → Den (o.sort p)) → Den k
  | _, .lit n, _ => n
  | _, .add, c => (c false Env.empty : ℕ) + c true Env.empty
  | _, .nat, _ => TValue.nat
  | _, .vec, c => TValue.vec (c false Env.empty) (c true Env.empty)
  | _, .arrow, c => TValue.arrow (c false Env.empty) (c true Env.empty)
  | _, .mono, c => SScheme.mono (c () Env.empty)
  | _, .all, c => SScheme.all fun n => c () (Env.single n)

/-- The type-level interpretation. -/
@[expose] def tyAlg : TySig.Interpretation Den := fun o c => tyAlgFn o c

/-! ## Shapes of evaluated types -/

/-- The shape of an evaluated type: its lengths erased. -/
inductive TShape where
  | nat
  | vec (a : TShape)
  | arrow (a b : TShape)

/-- Forget the lengths of an evaluated type. -/
@[expose] def TValue.shape : TValue → TShape
  | .nat => .nat
  | .vec _ a => .vec a.shape
  | .arrow a b => .arrow a.shape b.shape

/-! ## The value level as a stacked family -/

/-- Head shapes: finite data with no types. -/
inductive Shape where
  | lit (k : ℕ)
  | rep
  | lam
  | app
  | sabs
  | sapp
  | conv

/-- Children of each shape. -/
@[expose, reducible] def Shape.Arg : Shape → Type
  | .lit _ | .rep => Empty
  | .app => Bool
  | .lam | .sabs | .sapp | .conv => Unit

/-- Only a size abstraction binds a type parameter in its child. -/
@[expose, reducible] def Shape.tbind : (h : Shape) → h.Arg → List Kind
  | .sabs => fun _ => [.size]
  | _ => fun _ => []

/-- Annotation slots: `lam a b`, `app a b`, `sabs body`, `sapp body n`, `conv s t`. -/
@[expose, reducible] def Shape.slots : Shape → List (List Kind × Kind)
  | .lit _ | .rep => []
  | .lam | .app | .conv => [([], .type), ([], .type)]
  | .sabs => [([.size], .scheme)]
  | .sapp => [([.size], .scheme), ([], .size)]

/-- The heads. -/
@[expose, reducible] def heads : Heads Kind := ⟨Shape, Shape.Arg, Shape.tbind, Shape.slots⟩

/-- `rep : ∀ n, nat → [n]nat` builds a constant vector. -/
@[expose] def repScheme : TyTerm [] .scheme := all (mono (arrow nat (vec (Term.var .zero) nat)))

/-- The empty substitution, weakening closed schemes. -/
@[expose] def closed {Θ : List Kind} : TySig.Substitution [] Θ := fun _ x => nomatch x

/-- Value binders of each child. -/
@[expose] def bindersFn : {Θ : List Kind} → (h : Shape) → heads.Ann TySig h Θ → (p : h.Arg) →
    List (TyTerm (h.tbind p ++ Θ) .scheme)
  | _, .lam, a, _ => [mono (a _ .zero)]
  | _, _, _, _ => []

/-- Sorts of the children. -/
@[expose] def sortFn : {Θ : List Kind} → (h : Shape) → heads.Ann TySig h Θ → (p : h.Arg) →
    TyTerm (h.tbind p ++ Θ) .scheme
  | _, .lit _, _, p => nomatch p
  | _, .rep, _, p => nomatch p
  | _, .lam, a, _ => mono (a _ (.succ .zero))
  | _, .app, a, false => mono (arrow (a _ .zero) (a _ (.succ .zero)))
  | _, .app, a, true => mono (a _ .zero)
  | _, .sabs, a, _ => a _ .zero
  | _, .sapp, a, _ => all (a _ .zero)
  | _, .conv, a, _ => mono (a _ .zero)

/-- Result sorts. -/
@[expose] def resultFn : {Θ : List Kind} → (h : Shape) → heads.Ann TySig h Θ →
    TyTerm Θ .scheme
  | _, .lit _, _ => mono nat
  | _, .rep, _ => repScheme.subst closed
  | _, .lam, a => mono (arrow (a _ .zero) (a _ (.succ .zero)))
  | _, .app, a => mono (a _ (.succ .zero))
  | _, .sabs, a => all (a _ .zero)
  | _, .sapp, a => (a _ .zero).substOne (a _ (.succ .zero))
  | _, .conv, a => mono (a _ (.succ .zero))

/-- `conv s t` needs `s` and `t` to have the same shape at every assignment; for types that
differ only in their sizes this is `fun _ => rfl`. No other head has a side condition. -/
@[expose] def wfFn : {Θ : List Kind} → (h : Shape) → heads.Ann TySig h Θ → Prop
  | _, .conv, a => ∀ ρ, ((a _ .zero).denote tyAlg ρ).shape =
      ((a _ (.succ .zero)).denote tyAlg ρ).shape
  | _, _, _ => True

/-- The language: one substitution equation per typing rule. -/
@[expose] def lang : Stacked TySig .scheme heads where
  binders := bindersFn
  sort := sortFn
  result := resultFn
  WF := wfFn
  binders_subst θ h a p := by cases h <;> rfl
  sort_subst θ h a p := by
    cases h with
    | app => cases p <;> simp [sortFn, Heads.Ann.subst, Substitution.liftMany]
    | lit => nomatch p
    | rep => nomatch p
    | _ => rfl
  result_subst θ h a := by
    cases h with
    | sapp => exact substOne_subst _ _ θ
    | rep =>
      simp only [resultFn, Term.subst_subst]
      congr 1
      funext c x
      nomatch x
    | lam => simp [resultFn, Heads.Ann.subst, Substitution.liftMany]
    | lit => simp [resultFn]
    | _ => rfl
  WF_subst θ h a wf := by
    cases h with
    | conv =>
      intro ρ
      change (((a _ .zero).subst θ).denote tyAlg ρ).shape =
        (((a _ (.succ .zero)).subst θ).denote tyAlg ρ).shape
      rw [Term.denote_subst, Term.denote_subst]
      exact wf _
    | _ => trivial

/-- Typed terms: size parameters `Θ`, value context `Γ`, scheme `s`. The value context is
spelled `TySig.Term`, as in the generic lemmas, rather than through `TyTerm`; see the guide's
section on two-level families. -/
abbrev Tm (Θ : List Kind) (Γ : List (TySig.Term Θ .scheme)) (s : TySig.Term Θ .scheme) :=
  lang.toFamily.Term Θ Γ s

variable {Θ : List Kind} {Γ : List (TySig.Term Θ .scheme)}

/-- A variable. -/
@[expose] def varT {s : TyTerm Θ .scheme} (x : ScopedVar Γ s) : Tm Θ Γ s :=
  ScopedFamily.Term.var x
/-- A number. -/
@[expose] def litT (k : ℕ) : Tm Θ Γ (mono nat) :=
  lang.node (.lit k) Env.empty trivial (fun p => nomatch p)
/-- The constant-vector primitive. -/
@[expose] def repT : Tm Θ Γ (repScheme.subst closed) :=
  lang.node .rep Env.empty trivial (fun p => nomatch p)
/-- Abstraction over a value; the body's context extends `Γ` itself. -/
@[expose] def lamT (A B : TyTerm Θ .type) (body : Tm Θ (mono A :: Γ) (mono B)) :
    Tm Θ Γ (mono (arrow A B)) :=
  lang.node .lam (Env.cons A (Env.cons B Env.empty)) trivial (fun _ => body)
/-- Application. Both children keep the context `Γ` exactly. -/
@[expose] def appT (A B : TyTerm Θ .type) (f : Tm Θ Γ (mono (arrow A B))) (x : Tm Θ Γ (mono A)) :
    Tm Θ Γ (mono B) :=
  lang.node .app (Env.cons A (Env.cons B Env.empty)) trivial
    (fun p => match p with | false => f | true => x)
/-- Abstraction over a size; the ambient sorts are weakened. -/
@[expose] def sabsT (body : TyTerm (.size :: Θ) .scheme)
    (e : Tm (.size :: Θ) (Γ.map (·.subst (Substitution.weakenMany (σ := TySig) [Kind.size])))
      body) :
    Tm Θ Γ (all body) :=
  lang.node .sabs (Env.cons body Env.empty) trivial (fun _ => e)
/-- Instantiation of a size. -/
@[expose] def sappT (body : TyTerm (.size :: Θ) .scheme) (n : TyTerm Θ .size)
    (e : Tm Θ Γ (all body)) : Tm Θ Γ (body.substOne n) :=
  lang.node .sapp (Env.cons body (Env.cons n Env.empty)) trivial (fun _ => e)
/-- A coercion between types of the same shape, checked by evaluation. -/
@[expose] def convT (s t : TyTerm Θ .type) (e : Tm Θ Γ (mono s))
    (hst : ∀ ρ, (s.denote tyAlg ρ).shape = (t.denote tyAlg ρ).shape := by intro _; rfl) :
    Tm Θ Γ (mono t) :=
  lang.node .conv (Env.cons s (Env.cons t Env.empty)) hst (fun _ => e)

/-- Variables below applications need no coercion: `λ f x. f (f x)`. -/
@[expose] def twice : Tm [] [] (mono (arrow (arrow nat nat) (arrow nat nat))) :=
  lamT _ _ (lamT _ _ (appT nat nat (varT (.succ .zero))
    (appT nat nat (varT (.succ .zero)) (varT .zero))))

/-- The size variable `m`, bound first. -/
abbrev vm : TyTerm [.size, .size] .size := Term.var (.succ .zero)
/-- The size variable `n`, bound nearest. -/
abbrev vn : TyTerm [.size, .size] .size := Term.var .zero

/-- Vectors of sizes `m + n` and `n + m` have the same shape at every assignment. -/
example (ρ : Env Den [.size, .size]) :
    ((vec (add vm vn) nat).denote tyAlg ρ).shape =
      ((vec (add vn vm) nat).denote tyAlg ρ).shape := rfl

/-- `Λ m n. λ (x : [m + n]nat). x : [n + m]nat`. The coercion's evidence is `rfl`, because
domains ignore lengths; no arithmetic fact is consulted. -/
@[expose] def swap : Tm [] [] (all (all (mono (arrow (vec (add vm vn) nat)
    (vec (add vn vm) nat))))) :=
  sabsT _ (sabsT _ (lamT _ _ (convT (vec (add vm vn) nat) _ (varT .zero))))

/-- Substitution laws hold by the generic lemmas. -/
example {Γ Δ Λ : List (TyTerm [] .scheme)} {s : TyTerm [] .scheme} (t : Tm [] Γ s)
    (θ : lang.toFamily.Substitution Γ Δ) (θ' : lang.toFamily.Substitution Δ Λ) :
    (t.subst lang.reindexAction θ).subst lang.reindexAction θ' =
      t.subst lang.reindexAction (fun a x => (θ a x).subst lang.reindexAction θ') :=
  lang.subst_subst t θ θ'

/-- The body of `rep`'s scheme, weakened below the size binder. -/
abbrev repBody : TyTerm [.size, .size] .scheme :=
  (mono (arrow nat (vec (Term.var .zero) nat))).subst (Substitution.lift closed .size)

/-- The type of `rep{n}` as substitution computes it. -/
abbrev repInst : TyTerm [.size] .type :=
  ((arrow nat (vec (Term.var .zero) nat)).subst (Substitution.lift closed .size)).substOne
    (Term.var .zero)

/-- `rep{n} 7 : [n]nat`, with a coercion after the instantiation: substitution does not
return the written type definitionally, but the shapes agree by `rfl`. -/
@[expose] def repSeven : Tm [.size] [] (mono (vec (Term.var .zero) nat)) :=
  appT nat (vec (Term.var .zero) nat)
    (convT repInst (arrow nat (vec (Term.var .zero) nat))
      (sappT repBody (Term.var .zero) repT))
    (litT 7)

/-- `n := 3`. -/
@[expose] def three : TySig.Substitution [.size] [] := Env.cons (lit 3) closed

/-- Instantiating the size of `repSeven` at `3` is a generic family map. -/
example : Tm [] [] ((mono (vec (Term.var .zero) nat)).subst three) :=
  repSeven.map lang.paramHom three

/-! ## Length-erased domains -/

/-- Call-by-name domains. A vector is a stream that ignores its length, and a function is a
continuous map. -/
@[expose] noncomputable def TShape.dom : TShape → PointedDomain.{0}
  | .nat => .ofType (DomainResult Empty (DiscreteOrder ℕ))
  | .vec a => .pi ℕ fun _ => a.dom
  | .arrow a b => .ofType (a.dom →𝒄 b.dom)

/-- Native values, with lengths erased in the same way. -/
@[expose, reducible] def TShape.native : TShape → Type
  | .nat => ℕ
  | .vec a => ℕ → a.native
  | .arrow a b => a.native → b.native

/-- Domains of schemes: a quantifier denotes a family indexed by sizes. -/
@[expose] noncomputable def SScheme.dom : SScheme → PointedDomain.{0}
  | .mono t => t.shape.dom
  | .all f => .pi ℕ fun n => (f n).dom

/-- Native values of schemes. -/
@[expose, reducible] def SScheme.native : SScheme → Type
  | .mono t => t.shape.native
  | .all f => (n : ℕ) → (f n).native

/-- Value carriers of the lazy meaning. -/
abbrev SDom (s : SScheme) : Type := s.dom

/-- Value carriers of the total evaluator. -/
abbrev SNative (s : SScheme) : Type := s.native

/-! ## A model over evaluated heads

The value-level typing rules repeat the syntactic ones on evaluated annotations. Each
coherence equation is `rfl`, except instantiation (`denote_substOne`) and the weakening of
the closed primitive scheme. -/

/-- Value binders of each child. -/
@[expose] def bindersV : (h : Shape) → heads.AnnV Den h → (p : h.Arg) → Env Den (h.tbind p) →
    List SScheme
  | .lam, v, _, _ => [.mono (v _ .zero Env.empty)]
  | _, _, _, _ => []

/-- Sorts of the children. -/
@[expose] def sortV : (h : Shape) → heads.AnnV Den h → (p : h.Arg) → Env Den (h.tbind p) →
    SScheme
  | .lit _, _, p, _ => nomatch p
  | .rep, _, p, _ => nomatch p
  | .lam, v, _, _ => .mono (v _ (.succ .zero) Env.empty)
  | .app, v, false, _ => .mono (.arrow (v _ .zero Env.empty) (v _ (.succ .zero) Env.empty))
  | .app, v, true, _ => .mono (v _ .zero Env.empty)
  | .sabs, v, _, ξ => v _ .zero ξ
  | .sapp, v, _, _ => .all fun n => v _ .zero (Env.single n)
  | .conv, v, _, _ => .mono (v _ .zero Env.empty)

/-- Result sorts. -/
@[expose] def resultV : (h : Shape) → heads.AnnV Den h → SScheme
  | .lit _, _ => .mono .nat
  | .rep, _ => repScheme.denote tyAlg Env.empty
  | .lam, v => .mono (.arrow (v _ .zero Env.empty) (v _ (.succ .zero) Env.empty))
  | .app, v => .mono (v _ (.succ .zero) Env.empty)
  | .sabs, v => .all fun n => v _ .zero (Env.single n)
  | .sapp, v => v _ .zero (Env.single (v _ (.succ .zero) Env.empty))
  | .conv, v => .mono (v _ (.succ .zero) Env.empty)

/-- A coercion relates evaluated types of one shape. -/
@[expose] def wfV : (h : Shape) → heads.AnnV Den h → Prop
  | .conv, v => (v _ .zero Env.empty).shape = (v _ (.succ .zero) Env.empty).shape
  | _, _ => True

/-- The model. -/
@[expose] def model : Stacked.Model lang where
  Den := Den
  tyAlg := tyAlg
  WFV := wfV
  bindersV := bindersV
  sortV := sortV
  resultV := resultV
  WF_coh h a ρ wf := by
    cases h with
    | conv => exact wf ρ
    | _ => trivial
  binders_coh h a ρ p ξ _ := by cases h <;> rfl
  sort_coh h a ρ p ξ _ := by
    cases h with
    | app => cases p <;> rfl
    | lit => nomatch p
    | rep => nomatch p
    | _ => rfl
  result_coh h a ρ _ := by
    cases h with
    | sapp => exact Term.denote_substOne _ _ _ _
    | rep =>
      change (repScheme.subst closed).denote tyAlg ρ = repScheme.denote tyAlg Env.empty
      rw [Term.denote_subst]
      congr 1
      funext c x
      nomatch x
    | _ => rfl

/-! ## The lazy meaning and a total evaluator -/

/-- The carriers of the lazy meaning, at the model's evaluated schemes. -/
noncomputable scoped instance instSDom :
    ∀ d : model.Den .scheme, OmegaCompletePartialOrder (SDom d) :=
  fun d => (SScheme.dom d).cpo

/-- Application of a lazy function, as a continuous map. -/
@[expose] noncomputable def applyLazy (A B : TValue) :
    SDom (.mono (.arrow A B)) × SDom (.mono A) →𝒄 SDom (.mono B) :=
  ContinuousHom.Prod.apply (α := A.shape.dom) (β := B.shape.dom)

/-- A lazy function as a continuous map. -/
@[expose] noncomputable def asHom {a b : TShape} (d : (TShape.arrow a b).dom) :
    a.dom →𝒄 b.dom := d

/-- Instantiate a lazy size-polymorphic value, as a continuous map. -/
@[expose] noncomputable def atSize (f : ℕ → SScheme) (n : ℕ) : SDom (.all f) →𝒄 SDom (f n) :=
  .ofFun (fun g => (show (m : ℕ) → (f m).dom from g) n)
    (ωScottContinuous.apply₂ ωScottContinuous.id n)

/-- A coercion between types of one shape, as a continuous map. -/
@[expose] noncomputable def convLazy (A B : TValue) (h : A.shape = B.shape) :
    SDom (.mono A) →𝒄 SDom (.mono B) :=
  ContinuousHom.ofEq (fun sh : TShape => (sh.dom : Type)) h

/-- The constant-vector primitive at any size: the constant stream. -/
@[expose] noncomputable def repLazy : TShape.nat.dom →𝒄 (TShape.vec .nat).dom :=
  .ofFun fun x _ => x

/-- The lazy interpretation: call by name, with coercions cast along shapes. An abstraction's value
is `Env.abstraction` of its body's meaning, as an `ofFun` clause, so that the kernel checks
equations between nested abstractions in time linear in their depth. -/
@[expose] noncomputable def lazy : model.DomainInterp SDom
  | .lit k, _, _ =>
    .const (show SDom (.mono .nat) from (DomainResult.value ⟨k⟩ : DomainResult Empty _))
  | .rep, _, _ => .const (show SDom (repScheme.denote tyAlg Env.empty) from fun _ => repLazy)
  | .lam, v, _ => .ofFun (fun c => Env.abstraction (V := SDom) (a := .mono (v _ .zero Env.empty))
        (E := SDom (.mono (v _ (.succ .zero) Env.empty))) (c () Env.empty))
      (Env.abstractionContinuous.ωScottContinuous.comp
        (ωScottContinuous.apply₂ ωScottContinuous.id () |>.apply₂ Env.empty))
  | .app, v, _ => (applyLazy (v _ .zero Env.empty) (v _ (.succ .zero) Env.empty)).comp
      (.ofFun fun c => (c false Env.empty Env.empty, c true Env.empty Env.empty))
  | .sabs, _, _ => .ofFun fun c n => c () (Env.single n) Env.empty
  | .sapp, v, _ => (atSize (fun n => v _ .zero (Env.single n)) (v _ (.succ .zero) Env.empty)).comp
      (.ofFun (fun c => c () Env.empty Env.empty)
        (ContinuousHom.ωScottContinuous_apply (ωScottContinuous.apply₂
          (ωScottContinuous.apply₂ ωScottContinuous.id ()) Env.empty) ωScottContinuous.const))
  | .conv, v, w => (convLazy (v _ .zero Env.empty) (v _ (.succ .zero) Env.empty) w).comp
      (.ofFun (fun c => c () Env.empty Env.empty)
        (ContinuousHom.ωScottContinuous_apply (ωScottContinuous.apply₂
          (ωScottContinuous.apply₂ ωScottContinuous.id ()) Env.empty) ωScottContinuous.const))

/-- The constant-vector primitive on native values. -/
@[expose] def repNative : SNative (repScheme.denote tyAlg Env.empty) := fun _ x _ => x

/-- A total evaluator into native values. -/
@[expose] def native : model.Interp SNative
  | .lit k, _, _, _ => (k : ℕ)
  | .rep, _, _, _ => repNative
  | .lam, _, _, c => fun x => c () Env.empty (Env.single x)
  | .app, _, _, c => c false Env.empty Env.empty (c true Env.empty Env.empty)
  | .sabs, _, _, c => fun n => c () (Env.single n) Env.empty
  | .sapp, v, _, c => c () Env.empty Env.empty (v _ (.succ .zero) Env.empty)
  | .conv, _, w, c => cast (congrArg TShape.native w) (c () Env.empty Env.empty)

/-- A lazy value represents a native value of the same shape. -/
@[expose] def RepT : (a : TShape) → a.dom → a.native → Prop
  | .nat, d, n => d = DomainResult.value ⟨n⟩
  | .vec a, d, xs => ∀ i, RepT a (d i) (xs i)
  | .arrow a b, d, f => ∀ e x, RepT a e x → RepT b (asHom d e) (f x)

/-- Representation at schemes: a quantifier represents pointwise in its size. -/
@[expose] def Rep : (s : SScheme) → SDom s → SNative s → Prop
  | .mono t, d, v => RepT t.shape d v
  | .all f, d, v => ∀ n, Rep (f n) (d n) (v n)

theorem repT_cast {a b : TShape} (h : a = b) {d : a.dom} {x : a.native} (hr : RepT a d x) :
    RepT b (cast (congrArg (fun sh : TShape => (sh.dom : Type)) h) d)
      (cast (congrArg TShape.native h) x) := by
  subst h
  exact hr

theorem liftRel_single {s : SScheme} {d : SDom s} {v : SNative s} (h : Rep s d v) :
    Env.LiftRel Rep (Env.single d) (Env.single (V := SNative) v) :=
  (Env.liftRel_empty _).cons h

/-- The only constructor-local proof: every head preserves representation. -/
theorem lazy_related : Stacked.Model.DomainInterp.Related Rep lazy native := by
  intro h v w c c' hc
  cases h with
  | lit k =>
    exact (rfl : (DomainResult.value (⟨k⟩ : DiscreteOrder ℕ) : DomainResult Empty _) = _)
  | rep => exact fun _ _ _ hex _ => hex
  | lam => exact fun e x hex => hc () Env.empty _ _ (liftRel_single hex)
  | app =>
    exact hc false Env.empty _ _ (Env.liftRel_empty _) _ _
      (hc true Env.empty _ _ (Env.liftRel_empty _))
  | sabs => exact fun n => hc () (Env.single n) _ _ (Env.liftRel_empty _)
  | sapp => exact hc () Env.empty _ _ (Env.liftRel_empty _) _
  | conv => exact repT_cast w (hc () Env.empty _ _ (Env.liftRel_empty _))

/-- The lazy meaning of a closed term. -/
@[expose] noncomputable def meaning {s : TyTerm [] .scheme} (t : Tm [] [] s) :
    SDom (s.denote tyAlg Env.empty) :=
  model.denoteDomain SDom lazy t Env.empty Env.empty

/-- The total evaluation of a closed term. -/
@[expose] def evaluate {s : TyTerm [] .scheme} (t : Tm [] [] s) :
    SNative (s.denote tyAlg Env.empty) :=
  model.denote SNative native t Env.empty Env.empty

/-- The lazy meaning represents the total evaluation of every closed term. -/
theorem meaning_represents {s : TyTerm [] .scheme} (t : Tm [] [] s) :
    Rep _ (meaning t) (evaluate t) :=
  model.denoteDomain_related lazy_related t Env.empty (Env.liftRel_empty _)

/-- `swap` evaluates to the identity: the coercion only casts along an equation of shapes. -/
theorem evaluate_swap (m n : ℕ) (xs : ℕ → ℕ) :
    (show (m n : ℕ) → (ℕ → ℕ) → ℕ → ℕ from evaluate swap) m n xs = xs := rfl

/-- `twice f x = f (f x)`. -/
theorem meaning_twice (f : TShape.nat.dom →𝒄 TShape.nat.dom) (x : TShape.nat.dom) :
    (show (TShape.nat.dom →𝒄 TShape.nat.dom) →𝒄 TShape.nat.dom →𝒄 TShape.nat.dom from
      meaning twice) f x = f (f x) := rfl

/-! ## Instantiating a size commutes with meaning -/

theorem substitutionEnv_three :
    Term.substitutionEnv tyAlg three Env.empty = (Env.single (3 : ℕ) : Env Den [.size]) := by
  funext k x
  cases x with
  | zero => rfl
  | succ x => nomatch x

/-- Instantiating `n := 3` in the syntax, then taking the meaning, agrees with the meaning at
the evaluated assignment, which `substitutionEnv_three` computes to `n = 3`. No obligation
was proved for any head of the language. -/
theorem repSeven_three :
    HEq (model.denoteDomain SDom lazy (repSeven.map lang.paramHom three) Env.empty Env.empty)
      (model.denoteDomain SDom lazy repSeven (Term.substitutionEnv model.tyAlg three Env.empty)
        Env.empty) :=
  model.denoteDomain_map_closed SDom lazy repSeven three Env.empty

end Examples.ScopedVectors
