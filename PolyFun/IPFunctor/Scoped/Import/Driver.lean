/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import PolyFun.IPFunctor.Scoped.Import.Quote
public meta import PolyFun.IPFunctor.Scoped.Import.Submit
public meta import Lean.Data.Json.Parser
public meta import Batteries.Tactic.Lint.Basic

/-!
# Importing declarations with acceptance by erasure

A frontend reads declarations of an external language, elaborates each one in meta code into a
`Tree` of its typed syntax, and names an erasure back to the decoded source. `importDecls` then
adds, for each declaration `d` in order and in the current namespace:

* `d`, the quoted typed term, as an exposed definition; the kernel checks its type;
* the frontend's auxiliary definitions of `d`, such as its source or its meaning, exposed, and
  compiled or marked `noncomputable`;
* `d.accepted : erase d = src`, the acceptance theorem, proved by `Eq.refl` (or by evaluating a
  `Decidable` instance), so the kernel decides that the term erases to its source;
* the frontend's equation lemmas, each by `Eq.refl`;
* the frontend's other theorems about `d`, each with a proof term the frontend assembles and only
  the kernel checks.

Bundle declarations, such as a table the acceptance theorems mention, come first. Everything goes
through `Submit.submit`, which compiles the term in the same step as its kernel check. Each
declaration runs `withBudget`: its elaboration, kernel checks and compilation share one `Budget`,
with a fresh heartbeat count, so an import of many declarations that each fit the budget succeeds
in one command. A failure stops the import and removes all of it: a kernel rejection, a
compilation error, an error of the frontend, or a heartbeat or recursion-depth limit.

A frontend can name, for each declaration it generates, environment linters that skip it
(`Extra.nolint`, `ExtraTheorem.nolint`, `Elaborated.nolint` and `Elaborated.equationNolint`).
`commitSteps` marks the declaration `@[nolint …]` in the step that adds it, so a rollback removes
the mark with the declaration. The marks are for findings that hold by construction, such as a
name that the source language dictates, and never reach a hand-written declaration.

In check mode nothing is added. Each step is checked against a kernel environment that
accumulates the earlier ones, and each declaration's verdict is reported as a message, so a
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
  /-- The budget of each declaration: of its elaboration together with its kernel checks and the
  term's compilation, and of each kernel check. -/
  budget : Budget
  /-- Add declarations, or only check them. -/
  mode : Mode := .commit
  /-- How the acceptance theorem is proved. -/
  acceptBy : AcceptBy := .refl
  /-- Report the time of each declaration's steps as a message: each kernel check, and the
  term's compilation separately. -/
  report : Bool := false

/-- An auxiliary definition of a declaration `d`, added as `d ++ suffix` after `d` and before its
acceptance theorem, exposed. -/
structure Extra where
  /-- The name relative to the declaration, such as `source` or `meaning`. -/
  suffix : Name
  /-- The definition's type. -/
  type : Expr
  /-- The definition's value. -/
  value : Expr
  /-- The definition's docstring. -/
  doc : String := ""
  /-- Compile the definition in the step of its kernel check, so that compiled code can run it.
  Otherwise it is marked `noncomputable`. -/
  compile : Bool := false
  /-- The environment linters that skip the definition, as `@[nolint]` names them. -/
  nolint : Array Name := #[]

/-- A theorem about a declaration `d`, added as `d ++ suffix` after its equation lemmas. The
frontend assembles the proof term in meta code, and only the kernel checks it against the
statement: the elaborator never infers its type or compares it with the statement. -/
structure ExtraTheorem where
  /-- The name relative to the declaration. -/
  suffix : Name
  /-- The statement. -/
  type : Expr
  /-- The proof term. -/
  proof : Expr
  /-- The theorem's docstring. -/
  doc : String := ""
  /-- The environment linters that skip the theorem, as `@[nolint]` names them. -/
  nolint : Array Name := #[]

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
  /-- Given the term, its auxiliary definitions. -/
  extras : Expr → MetaM (Array Extra) := fun _ => pure #[]
  /-- Given the term, the two sides of the acceptance theorem: its erasure and the source. -/
  acceptance : Expr → MetaM (Expr × Expr)
  /-- Given the term, equation lemmas `(suffix, lhs, rhs)`, each added as `base ++ suffix`. An
  equation whose left side is an auxiliary definition of `extras`, possibly applied, has that
  definition's type at its arguments; any other has the type of its left side. -/
  equations : Expr → MetaM (Array (Name × Expr × Expr)) := fun _ => pure #[]
  /-- Given the term, further theorems about it, added after the equation lemmas. -/
  theorems : Expr → MetaM (Array ExtraTheorem) := fun _ => pure #[]
  /-- The environment linters that skip the term, as `@[nolint]` names them. -/
  nolint : Array Name := #[]
  /-- The environment linters that skip each equation lemma, as `@[nolint]` names them. -/
  equationNolint : Array Name := #[]

/-- A declaration of the whole bundle, added before the bundle's declarations, under its base
name in the current namespace. -/
inductive BundleDecl where
  /-- An exposed, uncompiled definition. -/
  | defn (base : Name) (type value : Expr) (doc : String := "")
  /-- The theorem `lhs = rhs`, by `Eq.refl`. -/
  | refl (base : Name) (lhs rhs : Expr)
  /-- The theorem `prop`, by evaluating its `Decidable` instance. -/
  | decide (base : Name) (prop : Expr)

/-- The name of a bundle declaration relative to the current namespace. -/
def BundleDecl.base : BundleDecl → Name
  | .defn base .. | .refl base .. | .decide base .. => base

/-- A frontend for declarations of type `D`. -/
structure Frontend (D : Type) where
  /-- Elaborate one declaration. -/
  elaborate : D → MetaM Elaborated

/-- One kernel declaration of an import, with how to add it. -/
structure Step where
  /-- What the step adds, as named in reports: `the term`, `acceptance`, or a name. -/
  label : String
  /-- The declaration. -/
  decl : Declaration
  /-- For a definition: compile it, or mark it `noncomputable`. -/
  compile : Bool := false
  /-- The docstring. -/
  doc : String := ""
  /-- The environment linters that skip the declaration, as `@[nolint]` names them. -/
  nolint : Array Name := #[]

/-- The acceptance theorem of `lhs = rhs`. -/
def acceptanceDecl (acceptBy : AcceptBy) (name : Name) (lhs rhs : Expr) : MetaM Declaration :=
  match acceptBy with
  | .refl => reflDecl name lhs rhs
  | .decide => decideEqDecl name lhs rhs

/-- The type of `e` when its head is one of the auxiliary definitions `extras` of the declaration
`name`: that definition's type at `e`'s arguments. Steps are prepared before any of them is added,
so the elaborator cannot infer it. -/
def Extra.typeOf? (extras : Array Extra) (name : Name) (e : Expr) : MetaM (Option Expr) := do
  let .const head us := e.getAppFn | return none
  let some x := extras.find? (name ++ ·.suffix == head) | return none
  let type := x.type.instantiateLevelParams (levelParamsOf x.type x.value) us
  return some (← instantiateForall type e.getAppArgs)

/-- The steps of the declaration `name`: the term, its auxiliary definitions, its acceptance
theorem, its equation lemmas and its other theorems, in that order. -/
def Elaborated.steps (e : Elaborated) (cfg : Config) (name : Name) : MetaM (Array Step) := do
  let c := mkConst name
  let value ← e.syn.quote e.scope e.tree
  let term : Step :=
    { label := "the term"
      decl := ← defnDecl name e.type value
      compile := true
      doc := e.doc
      nolint := e.nolint }
  let extras ← e.extras c
  let extraSteps ← extras.mapM fun x => do
    let decl ← defnDecl (name ++ x.suffix) x.type x.value
    return ({ label := s!"`{x.suffix}`", decl, compile := x.compile, doc := x.doc
              nolint := x.nolint } : Step)
  let (lhs, rhs) ← e.acceptance c
  let decl ← acceptanceDecl cfg.acceptBy (name ++ `accepted) lhs rhs
  let accepted : Step := { label := "acceptance", decl }
  let equations ← (← e.equations c).mapM fun (suffix, lhs, rhs) => do
    let decl ← reflDecl (name ++ suffix) lhs rhs (← Extra.typeOf? extras name lhs)
    return ({ label := s!"`{suffix}`", decl, nolint := e.equationNolint } : Step)
  let theorems := (← e.theorems c).map fun t =>
    ({ label := s!"`{t.suffix}`", decl := theoremDecl (name ++ t.suffix) t.type t.proof
       doc := t.doc, nolint := t.nolint } : Step)
  return #[term] ++ extraSteps ++ #[accepted] ++ equations ++ theorems

/-- The single step of a bundle declaration `name`. -/
def BundleDecl.step (d : BundleDecl) (name : Name) : MetaM Step :=
  match d with
  | .defn _ type value doc => do
    let decl ← defnDecl name type value
    return { label := "the declaration", decl, doc }
  | .refl _ lhs rhs => do
    let decl ← reflDecl name lhs rhs
    return { label := "the declaration", decl }
  | .decide _ prop => do
    let decl ← decideDecl name prop
    return { label := "the declaration", decl }

/-- Mark the declaration `name` with `@[nolint linters]`, so that the environment linters
`linters` skip it. -/
def markNolint (name : Name) (linters : Array Name) : CoreM Unit := do
  match Batteries.Tactic.Lint.nolintAttr.setParam (← getEnv) name linters with
  | .ok env => setEnv env
  | .error err => throwError err

/-- Add the steps of the declaration `name` in order, `atomically`: if any fails, none remains.
Each step's `nolint` marks its declaration in the same step. -/
def commitSteps (cfg : Config) (name : Name) (steps : Array Step) : MetaM Unit := atomically do
  let mut times := #[]
  for step in steps do
    let start ← IO.monoNanosNow
    let doc? := if step.doc.isEmpty then none else some step.doc
    let compiled ← match step.decl with
      | .defnDecl d => submitDef d.name d.type d.value cfg.budget doc? (compile := step.compile)
      | decl => do
        let compiled ← submit decl cfg.budget
        if let some doc := doc? then addDocStringCore decl.getTopLevelNames.head! doc
        pure compiled
    unless step.nolint.isEmpty do markNolint step.decl.getTopLevelNames.head! step.nolint
    let total := (← IO.monoNanosNow) - start
    times := times.push m!"{step.label} {(total - compiled) / 1000000} ms"
    if step.compile then times := times.push m!"compilation {compiled / 1000000} ms"
  if cfg.report then
    logInfo m!"{name}: {MessageData.joinSep times.toList ", "}"

/-- Commit one elaborated declaration with all its steps, `atomically`. -/
def commitDecl (cfg : Config) (e : Elaborated) : MetaM Unit := do
  let name ← declName e.base
  commitSteps cfg name (← e.steps cfg name)

/-- Check the steps of `owner` in order against `env`; report the verdict and return the extended
environment, or `none` after a rejection. -/
def checkSteps (cfg : Config) (owner : Name) (env : Kernel.Environment) (steps : Array Step) :
    MetaM (Option Kernel.Environment) := do
  let opts := guard cfg.budget (← getOptions)
  let mut env := env
  for step in steps do
    match ← check env step.decl cfg.budget with
    | .error ex =>
      logInfo m!"{owner}: the kernel rejects {step.label}: {ex.toMessageData opts}"
      return none
    | .ok env' => env := env'
  logInfo m!"{owner}: the kernel accepts"
  return some env

/-- Import a bundle: first the bundle declarations `bundle`, then `decls` in order. Each
declaration is elaborated, checked and compiled `withBudget`, so it draws on its own budget rather
than on what the earlier ones left. Commit mode adds them `atomically`: a failure anywhere,
including a compilation error, restores the environment from before the import. Check mode adds
and compiles nothing, reports each verdict, and stops at the first rejection. -/
def importDecls {D : Type} (fe : Frontend D) (decls : Array D) (cfg : Config)
    (bundle : Array BundleDecl := #[]) : MetaM Unit := do
  cfg.budget.validate
  match cfg.mode with
  | .commit => atomically do
    for d in bundle do
      withBudget cfg.budget do
        let name ← declName d.base
        commitSteps cfg name #[← d.step name]
    for d in decls do
      withBudget cfg.budget do commitDecl cfg (← fe.elaborate d)
  | .check =>
    let ns ← getCurrNamespace
    let mut env := (← getEnv).toKernelEnv
    for d in bundle do
      let some env' ← withBudget cfg.budget do
          checkSteps cfg d.base env #[← d.step (ns ++ d.base)]
        | return
      env := env'
    for d in decls do
      let some env' ← withBudget cfg.budget do
          let e ← fe.elaborate d
          checkSteps cfg e.base env (← e.steps cfg (ns ++ e.base))
        | return
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
