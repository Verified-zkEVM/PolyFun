/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import Lean.Meta.AppBuilder
import PolyFun.IPFunctor.Scoped.Stacked

/-!
# Quoting scoped syntax into Lean terms

An importer builds a typed term of a `ScopedSignature` or of a `Stacked` family in meta code and
hands it to the kernel. This module turns a meta-level `Tree` into that term. The frontend
supplies a head table: each node carries a `Head` that builds one constructor application,
usually a smart constructor, from its scope and its quoted children. The generic part keeps
scopes and writes variables.

* A `Scope` holds a subterm's type parameters and its value sorts, nearest first, with every
  suffix of the sorts as a list literal. A variable is a chain of `ScopedVar.succ` over
  `ScopedVar.zero`, with every implicit argument written from those suffixes.
* A child either keeps its parent's parameters and adds value binders (`Child.keep`), or enters
  type binders (`Child.enter`). Entering a binder block `Ξ` replaces the parameters `Θ` by
  `Ξ ++ Θ` and weakens every ambient sort, as `Stacked.enter` does.
* `Syntax.ofSignature` and `Syntax.ofStacked` say how one syntax writes sorts, variables and
  weakenings. The type level and the value level of a stacked family use the same quoter.

Nodes are applications built with `mkAppN`. The elaborator never compares the types of
value-level terms, because that comparison is what exceeds its budget on large instantiation
chains; the kernel checks typing when `Submit.submitDef` adds the result. A mistake in a head
table therefore appears as a kernel type mismatch.
-/

public meta section

namespace IPFunctor.Import

open Lean Meta

/-- How a smart constructor takes its scope before its own arguments: not at all, the value
context, or the type parameters followed by the value context. -/
inductive ScopeArgs where
  /-- No scope arguments. -/
  | none
  /-- The value context (a signature's context). -/
  | ctx
  /-- The type parameters, then the value context (a stacked family's). -/
  | paramsCtx

/-- The scope of a subterm. -/
structure Scope where
  /-- The type parameters `Θ`, nearest first. -/
  params : Array Expr
  /-- `params` as a list literal. -/
  paramsList : Expr
  /-- The type of the sorts at `params`. -/
  sortType : Expr
  /-- The universe level of `sortType`. -/
  level : Level
  /-- The value sorts `Γ`, nearest first. -/
  sorts : Array Expr
  /-- `suffixes[i]` is the list literal of `sorts` from position `i`; its last entry is `[]`. -/
  suffixes : Array Expr

/-- A list literal of `xs` with element type `α` at universe level `u`, sharing every suffix:
entry `i` of the result is the literal of `xs` from position `i`, and the last entry is `[]`. -/
def listSuffixes (α : Expr) (u : Level) (xs : Array Expr) : Array Expr := Id.run do
  let mut tails := #[mkApp (mkConst ``List.nil [u]) α]
  for x in xs.reverse do
    tails := tails.push (mkApp3 (mkConst ``List.cons [u]) α x tails.back!)
  return tails.reverse

/-- The value context of a scope as a list literal. -/
def Scope.ctx (sc : Scope) : Expr :=
  sc.suffixes[0]!

/-- The arguments a smart constructor takes for this scope. -/
def Scope.args (sc : Scope) : ScopeArgs → Array Expr
  | .none => #[]
  | .ctx => #[sc.ctx]
  | .paramsCtx => #[sc.paramsList, sc.ctx]

/-- The typed variable at de Bruijn position `i`: `ScopedVar.succ` applied `i` times to
`ScopedVar.zero`, with every implicit argument explicit. -/
def Scope.scopedVar (sc : Scope) (i : Nat) : MetaM Expr := do
  unless i < sc.sorts.size do
    throwError "variable {i} is out of scope: the context has {sc.sorts.size} sorts"
  let mut v := mkApp3 (mkConst ``ScopedVar.zero [sc.level]) sc.sortType sc.suffixes[i + 1]!
    sc.sorts[i]!
  for k in [0:i] do
    let j := i - 1 - k
    v := mkApp5 (mkConst ``ScopedVar.succ [sc.level]) sc.sortType sc.suffixes[j + 1]!
      sc.sorts[i]! sc.sorts[j]! v
  return v

/-- How a child's scope derives from its parent's. -/
inductive Child where
  /-- The same parameters, with value binders (nearest first) in front of the context. -/
  | keep (binders : List Expr)
  /-- Type binders `tbind` (nearest first) in front of the parameters; every ambient sort is
  weakened past them, and value binders, written at the new parameters, come first. -/
  | enter (tbind : List Expr) (binders : List Expr)

/-- A head of the frontend's table: it builds one constructor application from the node's
scope and its quoted children, in argument order. -/
structure Head where
  /-- Build the application. -/
  build : Scope → Array Expr → MetaM Expr

/-- A smart-constructor head: `c` at universe levels `levels`, applied to the scope arguments,
then `pre`, the children, and `post`. -/
def Head.const (c : Name) (levels : List Level := []) (scopeArgs : ScopeArgs := .paramsCtx)
    (pre post : Array Expr := #[]) : Head :=
  ⟨fun sc children => pure (mkAppN (mkConst c levels) (sc.args scopeArgs ++ pre ++ children ++
    post))⟩

/-- A meta-level term to quote: a variable at a de Bruijn position, or a node of the head table
with its children and the scopes they enter. -/
inductive Tree where
  /-- The variable at a de Bruijn position. -/
  | var (index : Nat)
  /-- A node and its children, in argument order. -/
  | node (head : Head) (children : Array (Child × Tree))

/-- How one syntax writes its sorts, variables and weakenings. -/
structure Syntax where
  /-- The type of the type parameters' kinds. -/
  paramType : Expr
  /-- The universe level of `paramType`. -/
  paramLevel : Level
  /-- The type of the sorts at the given parameters (a list literal). -/
  sortType : Expr → MetaM Expr
  /-- The term-level variable from parameters, value context, sort and `ScopedVar`. -/
  var : (params ctx sort v : Expr) → MetaM Expr
  /-- Weaken a sort at parameters `Θ` past a binder block `Ξ` (both list literals). -/
  weaken : (params tbind sort : Expr) → MetaM Expr

/-- A scope from its parameters and its sorts, both nearest first. -/
def Syntax.scope (syn : Syntax) (params sorts : Array Expr) : MetaM Scope := do
  let paramsList := (listSuffixes syn.paramType syn.paramLevel params)[0]!
  let sortType ← syn.sortType paramsList
  let level ← getDecLevel sortType
  return { params, paramsList, sortType, level, sorts,
           suffixes := listSuffixes sortType level sorts }

/-- The scope a child enters. -/
def Syntax.childScope (syn : Syntax) (sc : Scope) : Child → MetaM Scope
  | .keep binders => syn.scope sc.params (binders.toArray ++ sc.sorts)
  | .enter tbind binders => do
    let tbindList := (listSuffixes syn.paramType syn.paramLevel tbind.toArray)[0]!
    let weakened ← sc.sorts.mapM (syn.weaken sc.paramsList tbindList)
    syn.scope (tbind.toArray ++ sc.params) (binders.toArray ++ weakened)

/-- Quote a tree in a scope. It is `partial`, with no termination proof: it runs on trees that a
frontend builds from external input, and the kernel checks the resulting term when
`Submit.submitDef` adds it. -/
partial def Syntax.quote (syn : Syntax) (sc : Scope) : Tree → MetaM Expr
  | .var i => do syn.var sc.paramsList sc.ctx sc.sorts[i]! (← sc.scopedVar i)
  | .node head children => do
    let args ← children.mapM fun (child, tree) => do
      syn.quote (← syn.childScope sc child) tree
    head.build sc args

/-- The syntax of a binding signature `σ : ScopedSignature S`. It has no type parameters: the
scope's parameters stay empty, and a child cannot enter type binders. Variables are
`ScopedSignature.Term.var`. -/
def Syntax.ofSignature (σ : Expr) : MetaM Syntax := do
  let .app _ S := (← whnf (← inferType σ)) | throwError "not a binding signature{indentExpr σ}"
  let var ← mkAppOptM ``ScopedSignature.Term.var #[some S, some σ]
  return {
    paramType := mkConst ``Unit
    paramLevel := 1
    sortType := fun _ => pure S
    var := fun _ ctx sort v => pure (mkApp3 var ctx sort v)
    weaken := fun _ _ _ => throwError "a binding signature has no type binders" }

/-- The syntax of a stacked family `lang : Stacked τ k₀ H`. Sorts at parameters `Θ` are
`τ.Term Θ k₀`, variables are `ScopedFamily.Term.var` of `lang.toFamily`, and entering a binder
block `Ξ` weakens a sort by `Term.subst (Substitution.weakenMany Ξ)`, as `Stacked.enter` does. -/
def Syntax.ofStacked (lang : Expr) : MetaM Syntax := do
  let langType ← whnf (← inferType lang)
  let #[K, τ, k₀, _] := langType.getAppArgs | throwError "not a stacked family{indentExpr lang}"
  let family ← mkAppM ``ScopedSignature.Stacked.toFamily #[lang]
  let var ← mkAppOptM ``ScopedFamily.Term.var #[none, none, some family]
  let term ← mkAppOptM ``ScopedSignature.Term #[some K, some τ]
  let subst ← mkAppOptM ``ScopedSignature.Term.subst #[some K, some τ]
  let weakenMany ← mkAppOptM ``ScopedSignature.Substitution.weakenMany #[some K, some τ]
  return {
    paramType := K
    paramLevel := ← getDecLevel K
    sortType := fun params => pure (mkApp2 term params k₀)
    var := fun params ctx sort v => pure (mkApp4 var params ctx sort v)
    weaken := fun params tbind sort => do
      let target := mkApp3 (mkConst ``List.append [← getDecLevel K]) K tbind params
      return mkApp5 subst params target k₀ (mkApp2 weakenMany params tbind) sort }

end IPFunctor.Import
