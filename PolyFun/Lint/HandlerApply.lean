/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public meta import Batteries.Tactic.Lint.Basic
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.Instances
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# Application lemmas for handlers

A handler built by its structure's constructor is used through the equation for its application, as
bundled morphisms are in Mathlib. Unfolding the handler instead makes `simp` traverse its whole body
at every occurrence. The environment linter `handlerApply` reports such a definition when it has no
application lemma (`@[simps]` generates one) and when it is reducible, since `simp` unfolds
reducible definitions without consulting their lemmas. `handlerApplyFor` is the check for other
one-field function structures, so a library that wraps handlers can register its own.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

namespace PolyFun.Lint

/-- The projection of `declName`'s structure if `declName` is a definition whose value, under its
parameters, is the constructor of a structure in `structures` applied to all its arguments. -/
private def constructed? (structures : List (Name × Name)) (declName : Name) :
    MetaM (Option Name) := do
  let .defnInfo info ← getConstInfo declName | return none
  lambdaTelescope info.value fun _ body => do
    let body := body.consumeMData
    let .const c _ := body.getAppFn | return none
    let some (.ctorInfo ctor) := (← getEnv).find? c | return none
    if body.getAppNumArgs < ctor.numParams + ctor.numFields then return none
    return structures.lookup ctor.induct

/-- Whether the conclusion of `type` is an equation whose left side applies `declName` or is an
instance of it. -/
private def isApplicationEquation (declName proj : Name) (type : Expr) : Bool :=
  match type.getForallBody.eq? with
  | some (_, lhs, _) => lhs.getAppFn.isConstOf declName || (lhs.find? fun e =>
      e.isAppOf proj && e.getAppArgs.any (·.getAppFn.isConstOf declName)).isSome
  | none => false

/-- Whether `declName` has an application lemma: a stated theorem of its own module or a `simp`
lemma whose left side applies it. Equation lemmas that Lean derives from the definition do not
count. -/
private def hasApplicationLemma (declName proj : Name) : MetaM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? declName with
  | some idx =>
    for n in env.header.moduleData[idx.toNat]!.constNames do
      if let some (.thmInfo thm) := env.find? n then
        if !isReservedName env n && isApplicationEquation declName proj thm.type then return true
  | none =>
    let found := env.constants.foldStage2 (fun found _ info =>
      match info with
      | .thmInfo thm => found || (!isReservedName env thm.name &&
          isApplicationEquation declName proj thm.type)
      | _ => found) false
    if found then return true
  let c ← mkConstWithFreshMVarLevels declName
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType c)
  let e ← try mkAppM proj #[mkAppN c args] catch _ => return false
  let (ts, _, _) ← forallMetaTelescopeReducing (← inferType e)
  let some t := ts[0]? | return false
  for thm in ← (← getSimpTheorems).post.getUnify (mkApp e t) do
    if isApplicationEquation declName proj (← inferType (← thm.getValue)) then return true
  return false

/-- The check for definitions built by the constructor of a structure in `structures`, given as
pairs of a structure and the projection that applies it. -/
def handlerApplyFor (structures : List (Name × Name)) : Linter where
  noErrorsFound := "Every constructed handler has an application lemma."
  errorsFound := "HANDLERS WITHOUT APPLICATION LEMMAS."
  test declName := do
    if (← isAutoDecl declName) || (← isInstance declName) then return none
    let some proj ← constructed? structures declName | return none
    if ← isReducible declName then
      return m!"is reducible, so `simp` unfolds it instead of using its application lemmas"
    if ← hasApplicationLemma declName proj then return none
    return m!"has no application lemma; add `@[simps]` or state its equations"

/-- Report handlers built by the constructor of `PFunctor.Handler` that have no application lemma or
are reducible. -/
@[env_linter] def handlerApply : Linter :=
  handlerApplyFor [(`PFunctor.Handler, `PFunctor.Handler.toFun)]

end PolyFun.Lint
