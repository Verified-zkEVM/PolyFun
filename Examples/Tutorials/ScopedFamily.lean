/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.FamilyMap
public import PolyFun.IPFunctor.Scoped.ConstantFamily

/-!
# A finite polymorphic IR built from a binding family

This small language has Boolean values, ordinary functions and one explicit
type quantifier. It illustrates changing parameter contexts independently of
any effect or source language. Its runtime erasure is a generic polynomial fold.
Parameter renaming is a generic family homomorphism, including under binders.
-/

public section

namespace Examples.ScopedFamily

open IPFunctor

/-- Simple types with a finite scope of free type parameters. -/
inductive Ty (n : Nat) where
  | bit
  | param (i : Fin n)
  | arrow (a b : Ty n)
  deriving DecidableEq

/-- Protect the nearest type parameter when lifting a parameter renaming. -/
@[expose] def lift {n m : Nat} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

theorem lift_comp {n m k : Nat} (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    lift (τ ∘ ρ) = lift τ ∘ lift ρ := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Rename the free parameters of a monotype. -/
@[expose] def Ty.rename {n m : Nat} (ρ : Fin n → Fin m) : Ty n → Ty m
  | .bit => .bit
  | .param i => .param (ρ i)
  | .arrow a b => .arrow (a.rename ρ) (b.rename ρ)

theorem Ty.rename_rename {n m k : Nat} (a : Ty n) (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    (a.rename ρ).rename τ = a.rename (τ ∘ ρ) := by
  induction a <;> simp_all [rename]

/-- Local values may have an ordinary type or one explicitly quantified type. -/
inductive ValueSort (n : Nat) where
  | mono (a : Ty n)
  | poly (body : Ty (n + 1))

/-- Reindex local schemes, retaining a quantified scheme's own binder. -/
@[expose] def ValueSort.rename {n m : Nat} (ρ : Fin n → Fin m) : ValueSort n → ValueSort m
  | .mono a => .mono (a.rename ρ)
  | .poly a => .poly (a.rename (lift ρ))

theorem ValueSort.rename_rename {n m k : Nat} (a : ValueSort n)
    (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    (a.rename ρ).rename τ = a.rename (τ ∘ ρ) := by
  cases a <;> simp only [rename, Ty.rename_rename, lift_comp]

/-- Constructor heads contain only finite data. -/
inductive Op (n : Nat) : ValueSort n → Type where
  | bit (b : Bool) : Op n (.mono .bit)
  | lam (a b : Ty n) : Op n (.mono (.arrow a b))
  | app (a b : Ty n) : Op n (.mono b)
  | typeAbs (body : Ty (n + 1)) : Op n (.poly body)

namespace Op

/-- Number of recursive children stored by a head. -/
@[expose, reducible] def arity {n : Nat} : {s : ValueSort n} → Op n s → Nat
  | _, .bit _ => 0
  | _, .lam _ _ | _, .typeAbs _ => 1
  | _, .app _ _ => 2

/-- A type abstraction extends its child's parameter scope. -/
@[expose, reducible] def world {n : Nat} : {s : ValueSort n} → (o : Op n s) → Fin o.arity → Nat
  | _, .typeAbs _, _ => n + 1
  | _, _, _ => n

/-- Weaken ambient value sorts when entering a type abstraction. -/
@[expose, reducible] def reindex {n : Nat} : {s : ValueSort n} → (o : Op n s) →
    (p : Fin o.arity) → ValueSort n → ValueSort (o.world p)
  | _, .typeAbs _, _ => ValueSort.rename Fin.succ
  | _, .bit _, _ | _, .lam _ _, _ | _, .app _ _, _ => id

/-- Only a value lambda introduces a new local value. -/
@[expose, reducible] def binders {n : Nat} : {s : ValueSort n} → (o : Op n s) →
    (p : Fin o.arity) → List (ValueSort (o.world p))
  | _, .lam a _, _ => [.mono a]
  | _, _, _ => []

/-- Required result sort at each recursive position. -/
@[expose, reducible] def sort {n : Nat} : {s : ValueSort n} → (o : Op n s) →
    (p : Fin o.arity) → ValueSort (o.world p)
  | _, .bit _, p => nomatch p
  | _, .lam _ b, _ => .mono b
  | _, .app a b, p => Fin.cases (.mono (.arrow a b)) (fun _ => .mono a) p
  | _, .typeAbs body, _ => .mono body

/-- Change a head's free parameters. -/
@[expose] def rename {n m : Nat} (ρ : Fin n → Fin m) :
    {s : ValueSort n} → Op n s → Op m (s.rename ρ)
  | _, .bit b => .bit b
  | _, .lam a b => .lam (a.rename ρ) (b.rename ρ)
  | _, .app a b => .app (a.rename ρ) (b.rename ρ)
  | _, .typeAbs body => .typeAbs (body.rename (lift ρ))

@[simp] theorem arity_rename {n m : Nat} (ρ : Fin n → Fin m) {s : ValueSort n} (o : Op n s) :
    (o.rename ρ).arity = o.arity := by cases o <;> rfl

/-- Lift a parameter renaming at the selected child's type binder. -/
@[expose] def next {n m : Nat} (ρ : Fin n → Fin m) {s : ValueSort n} (o : Op n s)
    (p : Fin (o.rename ρ).arity) : Fin (o.world (p.cast (o.arity_rename ρ))) →
      Fin ((o.rename ρ).world p) := by
  cases o <;> first | exact lift ρ | exact ρ

end Op

/-- A polynomial IR with separate type-parameter and local-value scopes. -/
@[expose, reducible] def signature : IPFunctor.ScopedFamily Nat ValueSort where
  Op := Op
  Arg o := Fin o.arity
  world := Op.world
  reindex := Op.reindex
  binders := Op.binders
  sort := Op.sort

/-- Finite syntax is the shared indexed free tree. -/
abbrev Term := signature.Term

/-- Parameter renaming is supplied by constructor-local laws, not a second tree recursion. -/
@[expose] def parameterHom : signature.Hom signature
    (fun n m => Fin n → Fin m) (fun ρ => ValueSort.rename ρ) where
  op := fun {_ _} ρ {_} o => o.rename ρ
  arg := fun {_ _} ρ {_} o p => p.cast (o.arity_rename ρ)
  next := fun {_ _} ρ {_} o p => o.next ρ p
  binders := by
    intro n m ρ s o p
    cases o <;> rfl
  reindex := by
    intro n m ρ s o p a
    cases o <;> try rfl
    exact (ValueSort.rename_rename a Fin.succ (lift ρ)).trans
      (ValueSort.rename_rename a ρ Fin.succ).symm
  sort := by
    intro n m ρ s o p
    cases o <;> first | rfl | exact Fin.elim0 p | skip
    cases p using Fin.cases <;> rfl

/-- Untyped runtime descriptions, with type abstractions erased. -/
inductive Runtime where
  | var (index : Nat)
  | bit (b : Bool)
  | lam (body : Runtime)
  | app (function argument : Runtime)
  deriving DecidableEq

/-- Erase one constructor's static type information. -/
@[expose] def eraseOp {n : Nat} {s : ValueSort n} (o : Op n s)
    (next : Fin o.arity → Runtime) : Runtime := match o with
  | .bit b => .bit b
  | .lam _ _ => .lam (next 0)
  | .app _ _ => .app (next 0) (next 1)
  | .typeAbs _ => next 0

/-- Constructor-local erasure compatibility supplies the traversal proof. -/
theorem eraseOp_rename {n m : Nat} (ρ : Fin n → Fin m) {s : ValueSort n} (o : Op n s)
    (ds : Fin o.arity → Runtime) (vs : Fin (o.rename ρ).arity → Runtime)
    (h : ∀ p, ds (p.cast (o.arity_rename ρ)) = vs p) :
    eraseOp o ds = eraseOp (o.rename ρ) vs := by
  cases o with
  | bit b => rfl
  | lam a b => exact congrArg Runtime.lam (h ⟨0, by change 0 < 1; decide⟩)
  | app a b =>
      exact congrArg₂ Runtime.app
        (h ⟨0, by change 0 < 2; decide⟩) (h ⟨1, by change 1 < 2; decide⟩)
  | typeAbs body => exact h ⟨0, by change 0 < 1; decide⟩

/-- The generic fold interprets this IR into runtime syntax. -/
@[expose] def erase {n : Nat} {Γ : List (ValueSort n)} {s : ValueSort n}
    (t : Term n Γ s) : Runtime :=
  t.fold (D := fun _ => Runtime) (fun _ x => .var x.index) (fun _ o next => eraseOp o next)

/-- The generic relational traversal theorem proves erasure preservation for
every parameter renaming, including maps that identify parameters. -/
theorem erase_parameters {n m : Nat} (ρ : Fin n → Fin m)
    {Γ : List (ValueSort n)} {s : ValueSort n} (t : Term n Γ s) :
    erase (t.map parameterHom ρ) = erase t := by
  symm
  apply IFreeM.fold_traverse_rel parameterHom.toTraversal IPFunctor.ScopedFamily.Hom.leaf
    (fun _ x => Runtime.var x.index) (fun _ o next => eraseOp o next)
    (fun _ x => Runtime.var x.index) (fun _ o next => eraseOp o next)
    (fun _ x y => x = y) ?_ ?_ (.mk ρ Γ s) t
  · intro i j state x
    cases state
    change Runtime.var x.index = Runtime.var (x.map _).index
    rw [ScopedVar.index_map]
  · intro i j state o ds vs hs
    cases state
    exact eraseOp_rename _ o ds vs hs

/-- One finite description of the polymorphic identity function. -/
@[expose] def identity : Term 0 [] (.poly (.arrow (.param 0) (.param 0))) :=
  .liftBind (.typeAbs (.arrow (.param 0) (.param 0))) (fun _ =>
    .liftBind (.lam (.param 0) (.param 0)) (fun _ => .pure .zero))

/-- Type abstraction erases, and the value binder retains its nearest variable. -/
theorem erase_identity : erase identity = .lam (.var 0) := rfl

/-- The generic value-renaming law applies below the type binder. -/
theorem rename_identity {n : Nat} {Γ : List (ValueSort n)} {s : ValueSort n} (t : Term n Γ s) :
    t.rename (fun x => x) = t := IPFunctor.ScopedFamily.Term.rename_id t

/-- Parameter maps preserve variable positions even when they identify type parameters. -/
theorem map_variable {n m : Nat} (ρ : Fin n → Fin m) {Γ : List (ValueSort n)}
    {s : ValueSort n} (x : ScopedVar Γ s) :
    erase ((IPFunctor.ScopedFamily.Term.var x).map parameterHom ρ) = .var x.index := by
  change Runtime.var (x.map (ValueSort.rename ρ)).index = _
  rw [ScopedVar.index_map]

end Examples.ScopedFamily
