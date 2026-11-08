/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import PolyFun.IPFunctor.Scoped.Import.Quote
public meta import PolyFun.IPFunctor.Scoped.Import.Submit
public meta import Lean.Data.Json.Parser

/-!
# Importing declarations with acceptance by erasure

A frontend reads declarations of an external language, elaborates each one in meta code into a
`Tree` of its typed syntax, and names an erasure back to the decoded source. `importDecls` then
adds, for each declaration `d` in order and in the current namespace:

* `d`, the quoted typed term, as an exposed definition; the kernel checks its type;
* `d.accepted : erase d = src`, the acceptance theorem, proved by `Eq.refl` (or by evaluating a
  `Decidable` instance), so the kernel decides that the term erases to its source;
* the frontend's equation lemmas, each by `Eq.refl`.

All three go through `Submit.submit`, under one per-declaration `Budget`, and the term is compiled
in the same step as its kernel check. The first failure stops the import and leaves nothing of the
failed declaration behind: a kernel rejection, a compilation error, an error of the frontend, or a
heartbeat or recursion-depth limit.

In check mode nothing is added. Each declaration is checked against a kernel environment that
accumulates the earlier ones, and the verdict of every step is reported as a message, so a
rejection test reads the kernel's answer under `#guard_msgs`.

The frontend's elaborator is untrusted: a mistake in it is either a kernel type mismatch or a
failed acceptance theorem. Errors in the source itself, such as an unbound name, belong in the
elaborator, which can report them with a location in the source.
-/

public meta section

namespace IPFunctor.Import

open Lean Meta

/-- Whether an import adds its declarations or only reports the kernel's verdicts. -/
inductive Mode where
  /-- Add every declaration; stop at the first rejection. -/
  | commit
  /-- Add nothing; report the kernel's verdict on each step. -/
  | check

/-- How the acceptance theorem is proved. -/
inductive AcceptBy where
  /-- `Eq.refl`: the kernel checks that both sides are definitionally equal. -/
  | refl
  /-- `of_decide_eq_true (Eq.refl true)`: the kernel evaluates a `Decidable` instance. -/
  | decide

/-- Import settings. -/
structure Config where
  /-- The kernel budget of each declaration, acceptance theorem and equation lemma. -/
  budget : Budget
  /-- Add declarations, or only check them. -/
  mode : Mode := .commit
  /-- How the acceptance theorem is proved. -/
  acceptBy : AcceptBy := .refl
  /-- Report each declaration's times as a message: the term's, which includes its compilation,
  and its acceptance theorem's. -/
  report : Bool := false

/-- One declaration, as a frontend elaborated it. -/
structure Elaborated where
  /-- The declaration's name relative to the current namespace. -/
  base : Name
  /-- The definition's docstring. -/
  doc : String := ""
  /-- The syntax the term belongs to. -/
  syn : Syntax
  /-- The scope of the whole term. -/
  scope : Scope
  /-- The type of the term. -/
  type : Expr
  /-- The term. -/
  tree : Tree
  /-- Given the term, the two sides of the acceptance theorem: its erasure and the source. -/
  acceptance : Expr → MetaM (Expr × Expr)
  /-- Given the term, equation lemmas `(suffix, lhs, rhs)`, each added as `base ++ suffix`. -/
  equations : Expr → MetaM (Array (Name × Expr × Expr)) := fun _ => pure #[]

/-- A frontend for declarations of type `D`. -/
structure Frontend (D : Type) where
  /-- Elaborate one declaration. -/
  elaborate : D → MetaM Elaborated

/-- The acceptance theorem of `lhs = rhs`. -/
def acceptanceDecl (acceptBy : AcceptBy) (name : Name) (lhs rhs : Expr) : MetaM Declaration :=
  match acceptBy with
  | .refl => reflDecl name lhs rhs
  | .decide => do decideDecl name (← mkEq lhs rhs)

/-- Commit one declaration with its acceptance theorem and equation lemmas, `atomically`: if any
step fails, none of them remains. -/
def commitDecl (cfg : Config) (e : Elaborated) : MetaM Unit := atomically do
  let name ← declName e.base
  let value ← e.syn.quote e.scope e.tree
  let start ← IO.monoNanosNow
  submitDef name e.type value cfg.budget (doc? := if e.doc.isEmpty then none else some e.doc)
  let typed ← IO.monoNanosNow
  let (lhs, rhs) ← e.acceptance (mkConst name)
  submit (← acceptanceDecl cfg.acceptBy (name ++ `accepted) lhs rhs) cfg.budget
  let accepted ← IO.monoNanosNow
  for (suffix, lhs, rhs) in ← e.equations (mkConst name) do
    submitRefl (name ++ suffix) lhs rhs cfg.budget
  if cfg.report then
    logInfo m!"{name}: typed in {(typed - start) / 1000000} ms, accepted in \
      {(accepted - typed) / 1000000} ms"

/-- Check one declaration against `env`; report each verdict and return the extended
environment, or `none` after a rejection. -/
def checkDecl (cfg : Config) (env : Kernel.Environment) (e : Elaborated) :
    MetaM (Option Kernel.Environment) := do
  let name := (← getCurrNamespace) ++ e.base
  let value ← e.syn.quote e.scope e.tree
  let opts ← getOptions
  match ← check env (← defnDecl name e.type value) cfg.budget with
  | .error ex =>
    logInfo m!"{e.base}: the kernel rejects the term: {ex.toMessageData opts}"
    return none
  | .ok env =>
    let (lhs, rhs) ← e.acceptance (mkConst name)
    match ← check env (← acceptanceDecl cfg.acceptBy (name ++ `accepted) lhs rhs) cfg.budget with
    | .error ex =>
      logInfo m!"{e.base}: the kernel rejects acceptance: {ex.toMessageData opts}"
      return none
    | .ok env =>
      let mut env := env
      for (suffix, lhs, rhs) in ← e.equations (mkConst name) do
        match ← check env (← reflDecl (name ++ suffix) lhs rhs) cfg.budget with
        | .error ex =>
          logInfo m!"{e.base}: the kernel rejects `{suffix}`: {ex.toMessageData opts}"
          return none
        | .ok env' => env := env'
      logInfo m!"{e.base}: the kernel accepts"
      return some env

/-- Import `decls` in order: add them in commit mode, or report the kernel's verdicts in check
mode, stopping at the first failure in either. Commit mode adds and compiles each declaration
`atomically`, so a failed declaration leaves nothing behind. Check mode adds and compiles
nothing. -/
def importDecls {D : Type} (fe : Frontend D) (decls : Array D) (cfg : Config) : MetaM Unit := do
  cfg.budget.validate
  match cfg.mode with
  | .commit =>
    for d in decls do
      commitDecl cfg (← fe.elaborate d)
  | .check =>
    let mut env := (← getEnv).toKernelEnv
    for d in decls do
      let some env' ← checkDecl cfg env (← fe.elaborate d) | return
      env := env'

/-- Read a JSON file whose path is relative to the importing package's root. The path is
resolved from the directory of the current source file upwards, so a dependent package can build
the importing module. Lake does not track the file: a module that reads it is not rebuilt when
only the file changes, unless the library declares it with an `input_file` or `input_dir`
target in `needs`. -/
def readJsonFile (path : String) : CoreM Json := do
  let relative : System.FilePath := path
  let mut resolved := relative
  unless relative.isAbsolute do
    let mut dir ← IO.FS.realPath ((← getFileName : System.FilePath).parent.getD ".")
    repeat
      if ← (dir / relative).pathExists then
        resolved := dir / relative
        break
      match dir.parent with
      | some parent => if parent == dir then break else dir := parent
      | none => break
  match Json.parse (← IO.FS.readFile resolved) with
  | .ok json => return json
  | .error err => throwError "{path}: invalid JSON: {err}"

end IPFunctor.Import
