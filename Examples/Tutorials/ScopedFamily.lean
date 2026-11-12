/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.FamilyMapSubstitution
public import PolyFun.IPFunctor.Scoped.ConstantFamily
import PolyFun.IPFunctor.Scoped.FamilyMapCongr

/-!
# A finite polymorphic IR built from a binding family

This small language has Boolean values, ordinary functions and one explicit
type quantifier. It illustrates changing parameter contexts independently of
any effect or source language. Its runtime erasure is a generic polynomial fold.
Parameter renaming is a generic family homomorphism, including under binders.
Only a type abstraction changes the parameter context, so every other child keeps its
ambient context exactly. That homomorphism also supplies the lawful reindexing action for
value substitution.
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

/-- Weaken ambient value sorts when entering a type abstraction. Every other child keeps
the ambient context exactly. -/
@[expose, reducible] def ambient {n : Nat} : {s : ValueSort n} → (o : Op n s) →
    (p : Fin o.arity) → ScopedFamily.Ambient ValueSort n (o.world p)
  | _, .typeAbs _, _ => .map (ValueSort.rename Fin.succ)
  | _, .bit _, _ | _, .lam _ _, _ | _, .app _ _, _ => .keep

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
  ambient := Op.ambient
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
    cases o <;> try first | rfl | exact Fin.elim0 p
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
  apply IPFunctor.ScopedFamily.Term.fold_map_rel parameterHom
    (fun _ x => Runtime.var x.index) (fun _ o next => eraseOp o next)
    (fun _ x => Runtime.var x.index) (fun _ o next => eraseOp o next)
    (fun _ x y => x = y) ?_ ?_ ρ t
  · intro n m μ Γ a x
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
    t.rename (fun _ x => x) = t := IPFunctor.ScopedFamily.Term.rename_id t

/-- Parameter maps preserve variable positions even when they identify type parameters. -/
theorem map_variable {n m : Nat} (ρ : Fin n → Fin m) {Γ : List (ValueSort n)}
    {s : ValueSort n} (x : ScopedVar Γ s) :
    erase ((IPFunctor.ScopedFamily.Term.var x).map parameterHom ρ) = .var x.index := by
  change Runtime.var (x.map (ValueSort.rename ρ)).index = _
  rw [ScopedVar.index_map]

/-- Parameter maps and local-variable maps can be applied in either order. -/
theorem parameters_rename {n m : Nat} (μ : Fin n → Fin m)
    {Γ Δ : List (ValueSort n)} {s : ValueSort n}
    (ρ : ScopedSignature.Renaming Γ Δ) (t : Term n Γ s) :
    (t.rename ρ).map parameterHom μ =
      (t.map parameterHom μ).rename (ScopedSignature.Renaming.map (ValueSort.rename μ) ρ) :=
  IPFunctor.ScopedFamily.Term.map_rename parameterHom μ ρ t

/-- A type binder and a value binder both preserve access to an ambient value.
The lambda's parameter is nearest; the free value remains one position farther away. -/
@[expose] def ambientValue : Term 1 [.mono (.param 0)]
    (.poly (.arrow (.param 0) (.param 1))) :=
  .liftBind (.typeAbs (.arrow (.param 0) (.param 1))) (fun _ =>
    .liftBind (.lam (.param 0) (.param 1)) (fun _ => .pure (.succ .zero)))

/-- Adding another ambient binding does not capture the free variable beneath the lambda. -/
theorem erase_rename_ambientValue :
    erase (ambientValue.rename fun _ => ScopedVar.succ (b := ValueSort.mono (n := 1) .bit)) =
      .lam (.var 2) := by
  simp only [erase, ambientValue, IPFunctor.ScopedFamily.Term.rename, IFreeM.fold_liftBind,
    IFreeM.fold_pure, eraseOp]
  rfl

/-! ## A lawful reindexing action

Family substitution takes a language's action on terms for each child's parameter-context
change. Only a type abstraction changes the parameter context; every other child keeps its
ambient context, so the action there is the identity. Below a type abstraction the action
renames parameters along `Fin.succ`:

1. `reindexAction` is the identity at children that keep their context, and parameter
   renaming along `Fin.succ` below a type abstraction.
2. `Term.map_var` and `Term.map_rename` give the variable and renaming laws.
3. `parameters_parameters_heq` composes whole-term renamings with `Term.map_map` and
   `Term.map_congr`, so `parameterHom_preservesReindex` follows from `lift ρ ∘ Fin.succ =
   Fin.succ ∘ ρ`. `Hom.PreservesReindex.preservesSubstitution` and `Term.map_subst` then give
   the substitution law.
-/

theorem lift_id {n : Nat} : lift (id : Fin n → Fin n) = id := by
  funext i
  cases i using Fin.cases <;> rfl

theorem Ty.rename_id {n : Nat} (a : Ty n) : a.rename id = a := by
  induction a <;> simp_all [rename]

theorem ValueSort.rename_id {n : Nat} (a : ValueSort n) : a.rename id = a := by
  cases a <;> simp only [rename, Ty.rename_id, lift_id]

namespace Op

/-- Renaming a head twice agrees with renaming it along the composite. -/
theorem rename_rename_heq {n m k : Nat} (ρ : Fin n → Fin m) (τ : Fin m → Fin k)
    {s : ValueSort n} (o : Op n s) : HEq ((o.rename ρ).rename τ) (o.rename (τ ∘ ρ)) := by
  cases o with
  | bit b => rfl
  | lam a b =>
      change HEq (Op.lam _ _) (Op.lam _ _)
      rw [Ty.rename_rename, Ty.rename_rename]
  | app a b =>
      change HEq (Op.app _ _) (Op.app _ _)
      rw [Ty.rename_rename, Ty.rename_rename]
  | typeAbs body =>
      change HEq (Op.typeAbs _) (Op.typeAbs _)
      rw [Ty.rename_rename, lift_comp]

end Op

/-- Move existing syntax into a child's parameter context: rename parameters along
`Fin.succ` below a type abstraction, and keep the term elsewhere. -/
@[expose] def reindexAction : signature.ReindexAction := fun {_ _} o p {_ _} t =>
  match o, p, t with
  | .typeAbs _, _, t => t.map parameterHom Fin.succ
  | .bit _, _, t => t
  | .lam _ _, _, t => t
  | .app _ _, _, t => t

/-- Reindexing keeps every variable at its binding position. -/
theorem reindexAction_preservesVars : reindexAction.PreservesVars signature := by
  intro _ _ o p _ _ x
  cases o <;> rfl

/-- Reindexing commutes with value renaming. -/
theorem reindexAction_preservesRenaming : reindexAction.PreservesRenaming signature := by
  intro _ _ o p _ _ _ ρ t
  cases o with
  | typeAbs => exact IPFunctor.ScopedFamily.Term.map_rename parameterHom Fin.succ ρ t
  | _ => rfl

/-- Successive parameter renamings compose throughout a term. -/
theorem parameters_parameters_heq {n m k : Nat} (ρ : Fin n → Fin m) (τ : Fin m → Fin k)
    {Γ : List (ValueSort n)} {s : ValueSort n} (t : Term n Γ s) :
    HEq ((t.map parameterHom ρ).map parameterHom τ) (t.map parameterHom (τ ∘ ρ)) := by
  apply (IPFunctor.ScopedFamily.Term.cast_heq _ _ _).symm.trans
  apply (heq_of_eq (IPFunctor.ScopedFamily.Term.map_map parameterHom parameterHom ρ τ t)).trans
  apply IPFunctor.ScopedFamily.Term.map_congr (parameterHom.comp parameterHom) parameterHom
    (fun {_ b c} μ ν => b = c ∧ HEq (μ.2.2 ∘ μ.2.1) ν) ?_ ?_ ?_ ?_ ?_ ⟨rfl, HEq.rfl⟩ t
  · intro _ _ _ _ _ hr
    exact hr.1
  · rintro _ _ _ μ _ ⟨rfl, hμ⟩
    cases eq_of_heq hμ
    exact heq_of_eq (funext fun s => ValueSort.rename_rename s μ.2.1 μ.2.2)
  · rintro _ _ _ μ _ ⟨rfl, hμ⟩ _ o
    cases eq_of_heq hμ
    exact Op.rename_rename_heq μ.2.1 μ.2.2 o
  · rintro _ _ _ μ _ ⟨rfl, hμ⟩ _ _ p q he
    cases eq_of_heq hμ
    exact Fin.ext (show p.val = q.val from Fin.val_eq_val_of_heq he)
  · rintro _ _ _ ⟨_, ρ, τ⟩ _ ⟨rfl, hμ⟩ _ o _ _ _
    cases eq_of_heq hμ
    cases o
    · exact ⟨rfl, HEq.rfl⟩
    · exact ⟨rfl, HEq.rfl⟩
    · exact ⟨rfl, HEq.rfl⟩
    · exact ⟨rfl, heq_of_eq (lift_comp ρ τ).symm⟩

/-- Entering a child commutes with parameter renaming on whole terms. -/
theorem parameterHom_preservesReindex :
    parameterHom.PreservesReindex reindexAction reindexAction := by
  intro _ _ ρ _ o p _ _ t
  cases o with
  | typeAbs =>
    change HEq ((t.map parameterHom Fin.succ).map parameterHom (lift ρ))
      ((t.map parameterHom ρ).map parameterHom Fin.succ)
    apply (parameters_parameters_heq _ _ t).trans
    apply HEq.trans ?_ (parameters_parameters_heq _ _ t).symm
    rfl
  | _ => rfl

/-- Parameter renaming and value substitution commute. -/
theorem parameters_subst {n m : Nat} (μ : Fin n → Fin m)
    {Γ Δ : List (ValueSort n)} {s : ValueSort n}
    (θ : signature.Substitution Γ Δ) (t : Term n Γ s) :
    (t.subst reindexAction θ).map parameterHom μ =
      (t.map parameterHom μ).subst reindexAction (θ.map parameterHom μ) :=
  IPFunctor.ScopedFamily.Term.map_subst parameterHom reindexAction reindexAction
    (parameterHom_preservesReindex.preservesSubstitution _ _ _) μ θ t

/-- Reindexing commutes with simultaneous value substitution. -/
theorem reindexAction_preservesSubstitution : reindexAction.PreservesSubstitution signature := by
  intro _ _ o p _ _ _ θ t
  cases o with
  | typeAbs => exact parameters_subst Fin.succ θ t
  | _ => rfl

/-- The action satisfies the whole substitution algebra. -/
theorem reindexAction_lawful : reindexAction.Lawful signature :=
  ⟨reindexAction_preservesVars, reindexAction_preservesRenaming,
    reindexAction_preservesSubstitution⟩

end Examples.ScopedFamily
