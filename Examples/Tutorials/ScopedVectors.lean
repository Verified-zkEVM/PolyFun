/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Stacked
public import PolyFun.IPFunctor.Scoped.Interpretation

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
-/

public section

namespace Examples.ScopedVectors

open IPFunctor IPFunctor.ScopedSignature

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
  wf_subst θ h a wf := by
    cases h with
    | conv =>
      intro ρ
      change (((a _ .zero).subst θ).denote tyAlg ρ).shape =
        (((a _ (.succ .zero)).subst θ).denote tyAlg ρ).shape
      rw [Term.denote_subst, Term.denote_subst]
      exact wf _
    | _ => trivial

/-- Typed terms: size parameters `Θ`, value context `Γ`, scheme `s`. -/
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

end Examples.ScopedVectors
