/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Interpretation
public import PolyFun.Realizability.StepClass

/-!
# Admissible interpretations of scoped terms

Fix a representation for each semantic sort. An interpretation preserves admissibility when
each constructor acts admissibly on argument meanings, including meanings under fresh binders.
Then every fixed term denotes an admissible function of the input whenever all variables of its
context do.
-/

public section

universe u v w z r

namespace IPFunctor.ScopedSignature

open PFunctor (StepClass)

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S} {V : S → Type z}
  {C : StepClass.{z, r}} {repr : (s : S) → C.Str (V s)} {ι : Type z} {input : C.Str ι}
  {Γ Δ : List S}

/-- Every variable lookup is an admissible function of the input. -/
@[expose] def Env.Admissible (C : StepClass.{z, r}) (repr : (s : S) → C.Str (V s))
    (input : C.Str ι) (ρ : ι → Env V Γ) : Prop :=
  ∀ ⦃s⦄ (x : ScopedVar Γ s), C.Hom input (repr s) (fun i => ρ i s x)

theorem Env.Admissible.empty : Env.Admissible C repr input (fun _ => Env.empty) :=
  fun _ x => nomatch x

/-- Binding a value computed admissibly from the input keeps an environment admissible. -/
theorem Env.Admissible.cons {s : S} {ρ : ι → Env V Γ} {value : ι → V s}
    (hρ : Env.Admissible C repr input ρ) (hv : C.Hom input (repr s) value) :
    Env.Admissible C repr input (fun i => Env.cons (value i) (ρ i)) := by
  intro a x
  cases x with
  | zero => exact hv
  | succ x => exact hρ x

/-- Appending an admissible block of bindings keeps an environment admissible. -/
theorem Env.Admissible.append {ξ : ι → Env V Δ} {ρ : ι → Env V Γ}
    (hξ : Env.Admissible C repr input ξ) (hρ : Env.Admissible C repr input ρ) :
    Env.Admissible C repr input (fun i => Env.append (ξ i) (ρ i)) := by
  induction Δ with
  | nil => exact hρ
  | cons s Δ ih =>
    exact Env.Admissible.cons
      (ih (ξ := fun i a x => ξ i a (.succ x)) (fun _ x => hξ (.succ x))) (hξ .zero)

/-- Each constructor acts admissibly on arguments that are admissible at every assignment to
their bound variables computed admissibly from the same input. The premise does not make an
argument admissible jointly in the input and its bound variables. -/
@[expose] def Interpretation.PreservesAdmissible (alg : Interpretation σ V)
    (C : StepClass.{z, r}) (repr : (s : S) → C.Str (V s)) : Prop :=
  ∀ {ι : Type z} (input : C.Str ι) {s} (op : σ.Op s)
    (args : (p : σ.Arg op) → ι → Env V (σ.binders op p) → V (σ.sort op p)),
    (∀ p (ξ : ι → Env V (σ.binders op p)), Env.Admissible C repr input ξ →
      C.Hom input (repr (σ.sort op p)) (fun i => args p i (ξ i))) →
    C.Hom input (repr s) (fun i => alg op (fun p η => args p i η))

/-- The meaning of a fixed term is admissible in every admissible environment. -/
theorem Term.denote_admissible {alg : Interpretation σ V} {s : S} (t : σ.Term Γ s)
    (h : alg.PreservesAdmissible C repr) {ρ : ι → Env V Γ} (hρ : Env.Admissible C repr input ρ) :
    C.Hom input (repr s) (fun i => t.denote alg (ρ i)) := by
  induction t using Term.inductionOn with
  | hvar Γ s x => exact hρ x
  | hnode Γ s op args ih =>
    apply h input op (fun p i η => (args p).denote alg (Env.append η (ρ i)))
    exact fun p ξ hξ => ih p (hξ.append hρ)

namespace Binary

/-- A one-sorted signature whose operations have two arguments in the ambient scope. -/
@[expose, reducible] def signature (Op : Type v) : ScopedSignature Unit where
  Op _ := Op
  Arg _ := Bool
  binders _ _ := []
  sort _ _ := ()

/-- Interpret a tag as a binary operation, with its left argument at position `false`. -/
@[expose] def algebra {Op : Type v} {A : Type z} (applyOp : Op → A → A → A) :
    Interpretation (signature Op) (fun _ => A) :=
  fun op args => applyOp op (args false Env.empty) (args true Env.empty)

/-- Apply a binary operation to two terms in the same context. -/
@[expose] def app {Op : Type v} {Γ : List Unit} (op : Op) (left right : (signature Op).Term Γ ()) :
    (signature Op).Term Γ () :=
  Term.node op fun b => if b then right else left

@[simp] theorem denote_app {Op : Type v} {A : Type z} {Γ : List Unit}
    (applyOp : Op → A → A → A) (op : Op) (left right : (signature Op).Term Γ ())
    (ρ : Env (fun _ : Unit => A) Γ) :
    (app op left right).denote (algebra applyOp) ρ =
      applyOp op (left.denote (algebra applyOp) ρ) (right.denote (algebra applyOp) ρ) := rfl

/-- Read the first variable in a two-variable context. -/
@[expose] def fst {Op : Type v} : (signature Op).Term [(), ()] () := .var .zero

/-- Read the second variable in a two-variable context. -/
@[expose] def snd {Op : Type v} : (signature Op).Term [(), ()] () := .var (.succ .zero)

/-- Apply an operation to the first two variables in their context order. -/
@[expose] def term {Op : Type v} (op : Op) : (signature Op).Term [(), ()] () := app op fst snd

/-- The two variables receive the two fields of the input pair. -/
@[expose] def pairEnv {A : Type z} (p : A × A) : Env (fun _ : Unit => A) [(), ()] :=
  Env.cons p.1 (Env.single p.2)

@[simp] theorem denote_fst {Op : Type v} {A : Type z} (applyOp : Op → A → A → A) (p : A × A) :
    fst.denote (algebra applyOp) (pairEnv p) = p.1 := rfl

@[simp] theorem denote_snd {Op : Type v} {A : Type z} (applyOp : Op → A → A → A) (p : A × A) :
    snd.denote (algebra applyOp) (pairEnv p) = p.2 := rfl

@[simp] theorem denote_term {Op : Type v} {A : Type z} (applyOp : Op → A → A → A)
    (op : Op) (p : A × A) : (term op).denote (algebra applyOp) (pairEnv p) = applyOp op p.1 p.2 :=
  rfl

/-- The binary interpretation preserves admissibility when every operation is admissible on the
represented pair. -/
theorem preservesAdmissible {Op : Type v} {A : Type z} {applyOp : Op → A → A → A}
    {repr : C.Str A} [P : C.HasProd]
    (h : ∀ op, C.Hom (P.prod repr repr) repr (fun p => applyOp op p.1 p.2)) :
    Interpretation.PreservesAdmissible (σ := signature Op) (algebra applyOp) C
      (fun _ => repr) := by
  intro ι input s op args hargs
  exact C.comp_mem (P.pair_mem (hargs false (fun _ => Env.empty) Env.Admissible.empty)
    (hargs true (fun _ => Env.empty) Env.Admissible.empty)) (h op)

/-- Reading either variable of a pair is an admissible projection. -/
theorem pairEnv_admissible {A : Type z} {repr : C.Str A} [P : C.HasProd] :
    Env.Admissible C (fun _ => repr) (P.prod repr repr) pairEnv :=
  (Env.Admissible.empty.cons (P.snd_mem repr repr)).cons (P.fst_mem repr repr)

/-- Every fixed two-variable term denotes an admissible function of a represented pair. -/
theorem denote_admissible {Op : Type v} {A : Type z} {applyOp : Op → A → A → A}
    {repr : C.Str A} [P : C.HasProd]
    (h : ∀ op, C.Hom (P.prod repr repr) repr (fun p => applyOp op p.1 p.2))
    (t : (signature Op).Term [(), ()] ()) :
    C.Hom (P.prod repr repr) repr (fun p => t.denote (algebra applyOp) (pairEnv p)) :=
  t.denote_admissible (preservesAdmissible h) pairEnv_admissible

end Binary

end IPFunctor.ScopedSignature
