/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Uses
public import ToCslib.Data.Fin.Cases

/-!
# A typed language using scoped polynomial syntax

Arithmetic, functions, lexical lets, and bounded loops share the generic
binding and interpretation APIs. A loop stores its body once, independently
of the iteration count. Let elimination uses capture-avoiding substitution. It leaves no let
under any binder, so the program it returns means the same under every interpretation of
`let`.
-/

public section

namespace Examples.ScopedPrograms

open IPFunctor IPFunctor.ScopedSignature

/-- The sorts of the example language. -/
inductive Ty where
  | nat
  | arrow (argument result : Ty)

/-- Native values interpreting each sort. -/
@[expose, reducible] def Ty.Value : Ty → Type
  | .nat => Nat
  | .arrow a b => a.Value → b.Value

/-- Operations describe binding, without carrying syntax children. -/
inductive Op : Ty → Type where
  | literal (n : Nat) : Op .nat
  | add : Op .nat
  | lam (a b : Ty) : Op (.arrow a b)
  | app (a b : Ty) : Op b
  | letE (a b : Ty) : Op b
  | loop (a : Ty) (n : Nat) : Op a

/-- All argument positions are finite, with two positions for a loop's seed and body. -/
@[expose, reducible] def Op.arity : {a : Ty} → Op a → Nat
  | _, .literal _ => 0
  | _, .lam _ _ => 1
  | _, _ => 2

/-- A loop body binds its index followed by the accumulated state. -/
@[expose, reducible] def signature : ScopedSignature Ty where
  Op := Op
  Arg op := Fin op.arity
  binders op := match op with
    | .literal _ => Fin.elim0
    | .add | .app _ _ => fun _ => []
    | .lam a _ => fun _ => [a]
    | .letE a _ => Fin.cases [] (fun _ => [a])
    | .loop a _ => Fin.cases [] (fun _ => [.nat, a])
  sort op := match op with
    | .literal _ => Fin.elim0
    | .add => fun _ => .nat
    | .lam _ b => fun _ => b
    | .app a b => Fin.cases (.arrow a b) (fun _ => a)
    | .letE a b => Fin.cases a (fun _ => b)
    | .loop a _ => fun _ => a

/-- Expressions reuse the polynomial free carrier. -/
abbrev Expr := signature.Term

namespace Expr

variable {Γ : List Ty} {a b : Ty}

/-- Natural-number literal. -/
@[expose] def literal (n : Nat) : Expr Γ .nat := .node (.literal n) (fun p => nomatch p)

/-- Addition in any scope. -/
@[expose] def add (x y : Expr Γ .nat) : Expr Γ .nat :=
  .node .add (Fin.cases x (fun _ => y))

/-- Function abstraction extends the body scope. -/
@[expose] def lam (body : Expr (a :: Γ) b) : Expr Γ (.arrow a b) :=
  .node (.lam a b) (fun _ => body)

/-- Lazy syntax for a lexical binding; its native interpretation is total. -/
@[expose] def letE (value : Expr Γ a) (body : Expr (a :: Γ) b) : Expr Γ b :=
  .node (.letE a b) (Fin.cases value (fun _ => body))

/-- A bounded loop stores one seed and one body. -/
@[expose] def loop (n : Nat) (seed : Expr Γ a) (body : Expr (.nat :: a :: Γ) a) : Expr Γ a :=
  .node (.loop a n) (Fin.cases seed (fun _ => body))

end Expr

/-- The constructor algebra, with all binding handled by the shared interpreter. -/
@[expose] def algebra : Interpretation signature Ty.Value
  | _, .literal n, _ => n
  | _, .add, next => next 0 Env.empty + next 1 Env.empty
  | _, .lam _ _, next => fun x => next 0 (Env.cons x Env.empty)
  | _, .app _ _, next => next 0 Env.empty (next 1 Env.empty)
  | _, .letE _ _, next => next 1 (Env.cons (next 0 Env.empty) Env.empty)
  | _, .loop _ n, next => Nat.rec (next 0 Env.empty)
      (fun i state => next 1 (Env.cons i (Env.cons state Env.empty))) n

/-- Evaluate a closed arithmetic example. -/
@[expose] def sumTo (n : Nat) : Expr [] .nat :=
  .loop n (.literal 0) (.add (.var .zero) (.var (.succ .zero)))

/-- Evaluate a lexical binding under another binder. -/
@[expose] def captureExample : Expr [] (.arrow .nat .nat) :=
  .letE (.literal 7) (.lam (.add (.var (.succ .zero)) (.var .zero)))

/-- One constructor-level transformation used as an indexed fold algebra. -/
@[expose] def eliminateLetNode : FoldAlgebra signature.polynomial
    (fun j => Expr j.1 j.2) := fun _ op =>
  match op with
  | .letE _ _ => fun args => (args 1).substOne (args 0)
  | op => fun args => .node op args

/-- Eliminate lexical let nodes, using the common fold and substitution machinery. -/
@[expose] def eliminateLets {Γ : List Ty} {a : Ty} (e : Expr Γ a) : Expr Γ a :=
  e.fold (fun _ x => .var x) eliminateLetNode

/-- Let elimination preserves meaning in every environment, including under lambdas. -/
theorem eliminateLets_correct {Γ : List Ty} {a : Ty} (e : Expr Γ a) (ρ : Env Ty.Value Γ) :
    (eliminateLets e).denote algebra ρ = e.denote algebra ρ := by
  have h := IFreeM.fold_fusion
    (P := signature.polynomial)
    (D := fun j => Expr j.1 j.2)
    (E := fun j : Judgment Ty => Env Ty.Value j.1 → Ty.Value j.2)
    (fun _ t η => t.denote algebra η)
    (fun _ x => Term.var x) (fun _ x η => η _ x)
    eliminateLetNode
    (fun _ op next η => algebra op (fun p ξ => next p (Env.append ξ η)))
    (fun _ _ => rfl)
    (by
      intro ⟨Γ, a⟩ op args
      funext η
      cases op with
      | letE a b => exact Term.denote_substOne algebra (args 1) (args 0) η
      | literal n => rfl
      | add => rfl
      | lam a b => rfl
      | app a b => rfl
      | loop a n => rfl)
    e
  exact congrFun h ρ

/-! ## Let elimination removes every let -/

/-- Whether an operation is a lexical binding. -/
@[expose] def Op.isLet : {a : Ty} → Op a → Bool
  | _, .letE _ _ => true
  | _, _ => false

/-- Let elimination keeps only heads of the original program, and none of them is a let. -/
theorem heads_eliminateLets {Γ : List Ty} {a : Ty} (e : Expr Γ a) :
    (eliminateLets e).heads ⊆ {h ∈ e.heads | h.op.isLet = false} := by
  refine IFreeM.fold_rel (D := fun j => Expr j.1 j.2) (E := fun _ => Set signature.Head)
    (fun _ e' s => e'.heads ⊆ {h ∈ s | h.op.isLet = false}) _ _ _ _ ?_ ?_ e
  · exact fun _ _ => Set.empty_subset _
  intro ⟨Γ, a⟩ op es ss h
  have hes (p) : (es p).heads ⊆ {x ∈ insert ⟨a, op⟩ (⋃ p, ss p) | x.op.isLet = false} :=
    (h p).trans fun x hx => ⟨Set.mem_insert_of_mem _ (Set.mem_iUnion_of_mem _ hx.1), hx.2⟩
  cases op with
  | letE a b =>
    exact (Term.heads_substOne_subset (es 1) (es 0)).trans (Set.union_subset (hes 1) (hes 0))
  | literal n | add | lam a b | app a b | loop a n =>
    exact Set.insert_subset_iff.2 ⟨⟨Set.mem_insert _ _, rfl⟩, Set.iUnion_subset hes⟩

/-- After let elimination, a program means the same under every interpretation that agrees
with `algebra` on the other operations, however it interprets `let`. -/
theorem eliminateLets_denote_of_agree {alg : Interpretation signature Ty.Value}
    (hagree : ∀ h : signature.Head, h.op.isLet = false → alg h.op = algebra h.op)
    {Γ : List Ty} {a : Ty} (e : Expr Γ a) (ρ : Env Ty.Value Γ) :
    (eliminateLets e).denote alg ρ = e.denote algebra ρ := by
  rw [Term.denote_congr_of_heads_subset (H := {h : signature.Head | h.op.isLet = false}) _
    ((heads_eliminateLets e).trans fun _ hh => hh.2) fun h hh => hagree h hh,
    eliminateLets_correct]

end Examples.ScopedPrograms
