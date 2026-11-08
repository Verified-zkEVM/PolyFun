/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import Lean.AddDecl
public meta import Lean.Meta.SynthInstance
public meta import Lean.Util.CollectLevelParams
public meta import Lean.Compiler.Old
public meta import Lean.DocString.Extension
public meta import Lean.Compiler.NoncomputableAttr

/-!
# Submitting imported declarations to the kernel

Every declaration an importer adds goes through `submit`, the only call of `addDecl` in the
import machinery. It runs the kernel check, and for a definition that is compiled the code
generator, in one synchronous step under fixed options:

* asynchronous elaboration off, so the check and the compilation finish, and any failure is
  raised, before `submit` returns. With it on, the default in the language server and on the
  command line, `addDecl` returns before the kernel has run, and a compilation error is reported
  only after the command.
* `debug.skipKernelTC` off. With that option set, `addDecl` admits any declaration unchecked,
  and nothing reports it afterwards: the declaration depends on no axiom. The option must never
  be set where imported declarations are accepted; `submit` overrides it.
* `maxHeartbeats` set to the declaration's `Budget`, which the kernel respects. A budget is at
  most the ambient `maxHeartbeats` and never `0`, which would mean unlimited.
* `pp.deepTerms` off, so a kernel error about a large term stays readable.

The kernel's allocations also count against the elaborator's heartbeats, which accumulate over a
whole command. `withBudget` gives one declaration a fresh count and the limit of its budget, so a
bundle of declarations that each fit the budget imports in one command.

When the kernel rejects a declaration, `addDecl` adds its statement as an axiom to avoid
follow-up errors, and the environment keeps that axiom even when the error is caught, or
swallowed by `#guard_msgs`. `atomically` restores the environment from before a step and
rethrows, also after a heartbeat or recursion-depth limit, which an ordinary handler lets pass.
It is the import machinery's only handler. `submit` runs every `addDecl` and every compilation
through it, and the driver runs each declaration and each whole import through it. A step can
fail in the kernel, in the code generator, in the frontend, or at a resource limit. In each case
the environment returns to its state before the import, so no declaration, compiled code,
docstring or fallback axiom of the import remains. Messages logged before the failure remain.

`check` asks the kernel for its verdict against a given kernel environment and commits nothing.
Rejection tests use it, so they need no handler at all.
-/

public meta section

namespace IPFunctor.Import

open Lean Meta

/-- A per-declaration kernel budget, in thousands of heartbeats, as `maxHeartbeats`. -/
structure Budget where
  /-- The kernel's heartbeat limit for one declaration. -/
  heartbeats : Nat

/-- The ambient `maxHeartbeats`. -/
def Budget.ambient : CoreM Budget :=
  return ⟨maxHeartbeats.get (← getOptions)⟩

/-- Refuse a budget of `0`, which the kernel reads as unlimited, and one above the ambient
`maxHeartbeats`, which would raise the limit without a visible option. -/
def Budget.validate (b : Budget) : CoreM Unit := do
  let ambient ← Budget.ambient
  if b.heartbeats == 0 then
    throwError "import budget 0 would leave the kernel unlimited; give a positive budget"
  if b.heartbeats > ambient.heartbeats then
    throwError "import budget {b.heartbeats} exceeds the ambient maxHeartbeats \
      {ambient.heartbeats}"

/-- The options of every kernel check: synchronous, never skipped, within the budget. -/
def guard (b : Budget) (opts : Options) : Options :=
  let opts := ((Elab.async.set opts false).setBool `debug.skipKernelTC false).setBool
    `pp.deepTerms false
  maxHeartbeats.set opts b.heartbeats

/-- Run `x` with its own heartbeat count, starting at zero, and the limit `b`. Kernel checks
allocate against the elaborator's count, so without this scope every declaration of an import
draws on what the earlier ones left of the command's budget. -/
def withBudget {m : Type → Type} [Monad m] [MonadControlT CoreM m]
    [MonadWithReaderOf Core.Context m] {α : Type} (b : Budget) (x : m α) : m α :=
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := b.heartbeats * 1000 }) x

/-- Run `x`; if it fails, restore the environment to its state before `x` and rethrow. This is
the import machinery's only exception handler. It never continues after a failure: it only
removes what the failed step added, including the axiom `addDecl` leaves for a declaration the
kernel rejects. It also handles heartbeat and recursion-depth limits, which `tryCatch` does not
catch. -/
def atomically {m : Type → Type} [Monad m] [MonadEnv m] [MonadExcept Exception m]
    [MonadRuntimeException m] {α : Type} (x : m α) : m α := do
  let env ← getEnv
  tryCatchRuntimeEx x fun ex => do
    setEnv env
    throw ex

/-- Add `decl` after the kernel has checked it within `b`, and compile it when `compile` holds.
Both run in one step, `atomically`: a declaration that the kernel rejects or that fails to compile
leaves nothing behind, and the error is rethrown. The result is the time the compilation took, in
nanoseconds, and `0` without one, so that a report can tell it from the kernel's time. -/
def submit (decl : Declaration) (b : Budget) (forceExpose := false) (compile := false) :
    CoreM Nat := do
  b.validate
  atomically <| withOptions (guard b) do
    addDecl decl (forceExpose := forceExpose)
    unless compile do return 0
    let start ← IO.monoNanosNow
    compileDecl decl
    return (← IO.monoNanosNow) - start

/-- The kernel's verdict on `decl` against `env`, within `b`. Nothing is committed: on success
the extended kernel environment is returned for later checks. -/
def check (env : Kernel.Environment) (decl : Declaration) (b : Budget) :
    CoreM (Except Kernel.Exception Kernel.Environment) := do
  b.validate
  return env.addDecl (guard b (← getOptions)) decl

/-- The universe parameters of `type` and `value`, in order of occurrence. -/
def levelParamsOf (type value : Expr) : List Name :=
  (collectLevelParams (collectLevelParams {} type) value).params.toList

/-- A definition with value `value : type`, regular reducibility hints and safe. -/
def defnDecl (name : Name) (type value : Expr) : CoreM Declaration := do
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
  return .defnDecl
    { name := name
      levelParams := levelParamsOf type value
      type := type
      value := value
      safety := .safe
      hints := hints }

/-- The theorem `lhs = rhs`, proved by `Eq.refl lhs`, which only the kernel checks. The two sides
have type `type?`, or the type inferred from `lhs` when it is `none`. With an explicit type, the
function reads nothing from the environment, so either side may name a constant that is not yet
added, such as an auxiliary definition of a declaration being imported. The kernel checks both
sides against the type. -/
def reflDecl (name : Name) (lhs rhs : Expr) (type? : Option Expr := none) :
    MetaM Declaration := do
  let α ← match type? with
    | some type => pure type
    | none => inferType lhs
  let u ← getLevel α
  let type := mkApp3 (mkConst ``Eq [u]) α lhs rhs
  let value := mkApp2 (mkConst ``Eq.refl [u]) α lhs
  return .thmDecl
    { name := name
      levelParams := levelParamsOf type value
      type := type
      value := value }

/-- The theorem `type`, proved by `proof`, which only the kernel checks against `type`. The
function reads nothing from the environment, so `proof` may name constants not yet added. -/
def theoremDecl (name : Name) (type proof : Expr) : Declaration :=
  .thmDecl
    { name := name
      levelParams := levelParamsOf type proof
      type := type
      value := proof }

/-- The theorem `prop`, proved by `of_decide_eq_true (Eq.refl true)`; the kernel evaluates the
`Decidable` instance. -/
def decideDecl (name : Name) (prop : Expr) : MetaM Declaration := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) prop)
  let rflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let value := mkApp3 (mkConst ``of_decide_eq_true) prop inst rflTrue
  return .thmDecl
    { name := name
      levelParams := levelParamsOf prop value
      type := prop
      value := value }

/-- The theorem `lhs = rhs`, proved by evaluating `DecidableEq` at the type of `lhs` in the
kernel. Only `lhs` is inspected, so `rhs` may name a constant that is not yet in the
environment. -/
def decideEqDecl (name : Name) (lhs rhs : Expr) : MetaM Declaration := do
  let α ← inferType lhs
  let u ← getLevel α
  let prop := mkApp3 (mkConst ``Eq [u]) α lhs rhs
  let inst := mkApp2 (← synthInstance (mkApp (mkConst ``DecidableEq [u]) α)) lhs rhs
  let rflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let value := mkApp3 (mkConst ``of_decide_eq_true) prop inst rflTrue
  return .thmDecl
    { name := name
      levelParams := levelParamsOf prop value
      type := prop
      value := value }

/-- `base` in the current namespace, refused if a declaration of that name exists. -/
def declName (base : Name) : CoreM Name := do
  let name := (← getCurrNamespace) ++ base
  if (← getEnv).contains name then
    throwError "cannot import `{name}`: a declaration of that name exists"
  return name

/-- Add an exposed definition, so that downstream modules and later acceptance checks can
unfold it. It is compiled within `submit`'s step when `compile` holds, and marked
`noncomputable` otherwise. The result is the compilation's time, as `submit` returns it. -/
def submitDef (name : Name) (type value : Expr) (b : Budget) (doc? : Option String := none)
    (compile := true) : CoreM Nat := do
  let compiled ← submit (← defnDecl name type value) b (forceExpose := true) (compile := compile)
  unless compile do modifyEnv (addNoncomputable · name)
  if let some doc := doc? then addDocStringCore name doc
  return compiled

/-- Add the theorem `lhs = rhs` by `Eq.refl lhs`. -/
def submitRefl (name : Name) (lhs rhs : Expr) (b : Budget) (doc? : Option String := none) :
    MetaM Unit := do
  discard <| submit (← reflDecl name lhs rhs) b
  if let some doc := doc? then addDocStringCore name doc

/-- Add the theorem `prop` by evaluating its `Decidable` instance in the kernel. -/
def submitDecide (name : Name) (prop : Expr) (b : Budget) (doc? : Option String := none) :
    MetaM Unit := do
  discard <| submit (← decideDecl name prop) b
  if let some doc := doc? then addDocStringCore name doc

end IPFunctor.Import
