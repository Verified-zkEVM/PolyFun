/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Do.Attr

/-!
# Checks for the core program-logic rules

Two of the core program-logic rules (`AGENTS.md`, "Core program-logic rules") are properties of
the elaborated environment rather than of source text. The commands here check them over the
imported modules whose names start with one of the given prefixes:

* `#check_wp_instances` reports every global instance, declared in such a module, of core's `WP`
  or `WPMonad` (of `Std.WP` or of `Std.Do`), of `MAlgOrdered` or `MAlgRelOrdered`, or of a class
  that extends one of them. Scoped instances pass, and so do `Prop`-valued classes keyed on a
  construction, such as `ExactWPMonad`, which extend none of these.
* `#check_wp_specs` reports every global `@[spec]` registration, made by such a module in the
  rule database of `vcgen` or of the deprecated `mvcgen`, of a rule that is not on
  `specAllowlist`. A rule tied to one reading is registered `scoped`, in the scope of that reading.
* `#check_wp_allowlist` reports every rule on `specAllowlist` that no such module registers
  globally, so that the list stays current.

When a check finds nothing to report, it says so in one line. `#wp_registrations` lists how the
imported modules register one declaration as an instance or as a `@[spec]` rule.

The checks read the entries that each imported module adds to core's instance and `@[spec]`
extensions. They therefore see an `attribute [instance]` or `attribute [spec]` command as well as
a declaration attribute, whichever module declares the constant. `PolyFunTest.Policy.WP` runs them
over PolyFun's libraries, and `PolyFunTest.Policy.WP.Violations` shows that they report planted
violations.
-/

public section

namespace PolyFunTest.Policy.WP

open Lean Meta Elab Command

/-- The data classes of an interpretation, which no PolyFun module instantiates globally. -/
meta def dataClasses : List Name :=
  [`Std.WP.WP, `Std.WP.WPMonad, `Std.Do.WP, `Std.Do.WPMonad, `MAlgOrdered, `MAlgRelOrdered]

/-- The rules that a PolyFun module may register as global `@[spec]` rules. Each rule holds for
every interpretation that it mentions, or is stated against a construction for all of the
construction's parameters, so it applies only where that construction is installed. -/
meta def specAllowlist : List Name := [
  -- `PolyFun.PFunctor.Free.Do`: every interpretation of `FreeM P`; the interpretation through a
  -- handler, for every handler; the upper-bound reading of a spec, for every spec.
  `PFunctor.FreeM.Spec.bind,
  `PFunctor.FreeM.Spec.lift_ofHandler,
  `PFunctor.FreeM.Spec.lift_upper,
  -- `PolyFun.Control.Do.MOfFn`: every `WPMonad` on the monad of `Fin.mOfFn`.
  `Fin.Spec.mOfFn,
  -- `PolyFun.Control.Do.Spec`: every `WPMonad` on the base monad, through core's interpretations
  -- of its own transformers. The registration of core's `Spec.tryCatch_MonadExcept` is here.
  `Std.WP.Spec.tryCatch_MonadExcept,
  `Std.WP.Spec.forM_list,
  `Std.WP.Spec.mapM_list,
  `Std.WP.Spec.seqLeft,
  `Std.WP.Spec.seqRight,
  `Std.WP.Spec.failure_OptionT,
  `Std.WP.Spec.lift_OptionT,
  `Std.WP.Spec.guard_OptionT,
  `Std.WP.Spec.guard_OptionT_iInf,
  `Std.WP.Spec.mk_OptionT,
  `Std.WP.Spec.run_OptionT_some_none,
  `Std.WP.Spec.lift_StateT,
  `Std.WP.Spec.mk_StateT,
  `Std.WP.Spec.run'_StateT,
  `Std.WP.Spec.lift_ExceptT,
  `Std.WP.Spec.mk_ExceptT,
  `Std.WP.Spec.run_ExceptT_ok_error]

/-- The imported modules whose names start with one of `prefixes`, with their indices. -/
meta def modulesUnder (env : Environment) (prefixes : Array Name) : Array (Nat × Name) :=
  (env.header.moduleNames.mapIdx fun i mod => (i, mod)).filter fun (_, mod) =>
    prefixes.any (·.isPrefixOf mod)

/-- Whether a class is one of `dataClasses` or extends one of them. -/
meta partial def extendsDataClass (env : Environment) (cls : Name) : Bool :=
  dataClasses.contains cls || (isStructure env cls &&
    (getStructureParentInfo env cls).any fun parent => extendsDataClass env parent.structName)

/-- Whether `declName` projects a class to one of its parent structures. That instance comes with
the declaration of the class, and the check reads the instances of the class instead. -/
meta def isParentProjection (env : Environment) (declName : Name) : Bool :=
  match declName with
  | .str cls _ => isStructure env cls &&
      (getStructureParentInfo env cls).any (·.projFn == declName)
  | _ => false

/-- The class of an instance: the head of the conclusion of its type. -/
meta def instanceClass? (inst : Expr) : MetaM (Option Name) := do
  forallTelescopeReducing (← inferType inst) fun _ body => return body.getAppFn.constName?

/-- The global instances of a data class that the modules under `prefixes` declare, as triples of
a module, an instance and its class. -/
meta def globalDataInstances (prefixes : Array Name) : MetaM (Array (Name × Name × Name)) := do
  let env ← getEnv
  let mut found := #[]
  for (i, mod) in modulesUnder env prefixes do
    for entry in instanceExtension.ext.getModuleEntries env i do
      let .global e := entry | continue
      let some inst := e.globalName? | continue
      if isParentProjection env inst then continue
      let some cls ← instanceClass? e.val | continue
      if extendsDataClass env cls then
        found := found.push (mod, inst, cls)
  return found

/-- How the module `mod` registers declarations in a `@[spec]` database: a scope, or `none` for
a global rule, with the declaration of the rule. -/
meta def specRegistrations (env : Environment) (i : Nat) : Array (Option Name × Name) := Id.run do
  let mut found := #[]
  for entry in Tactic.VCGen.SpecAttr.specAttr.ext.getModuleEntries env i do
    match entry with
    | .global e => if let .global decl := e.proof then found := found.push (none, decl)
    | .scoped ns e => if let .global decl := e.proof then found := found.push (some ns, decl)
  for entry in Tactic.Do.SpecAttr.specAttr.ext.getModuleEntries env i do
    match entry with
    | .global e => if let .global decl := e.proof then found := found.push (none, decl)
    | .scoped ns e => if let .global decl := e.proof then found := found.push (some ns, decl)
  return found

/-- The global `@[spec]` registrations that the modules under `prefixes` make, as pairs of a
module and a rule. -/
meta def globalSpecs (env : Environment) (prefixes : Array Name) : Array (Name × Name) := Id.run do
  let mut found := #[]
  for (i, mod) in modulesUnder env prefixes do
    for (scope?, decl) in specRegistrations env i do
      if scope?.isNone && !found.contains (mod, decl) then
        found := found.push (mod, decl)
  return found

/-- Report every global instance of a data class that a module under the prefixes declares. -/
syntax (name := checkWPInstances) "#check_wp_instances" (ppSpace ident)+ : command

@[command_elab checkWPInstances]
meta def elabCheckWPInstances : CommandElab := fun stx => do
  let prefixes := stx[1].getArgs.map (·.getId)
  let found ← liftTermElabM (globalDataInstances prefixes)
  for (mod, inst, cls) in found do
    logError m!"{mod} declares {inst}, a global instance of {cls}. Install an interpretation as \
      a construction, and as a `scoped` instance where a scope should select it."
  if found.isEmpty then
    logInfo m!"no global instance of an interpretation class"

/-- Report every global `@[spec]` registration, by a module under the prefixes, of a rule that is
not on `specAllowlist`. -/
syntax (name := checkWPSpecs) "#check_wp_specs" (ppSpace ident)+ : command

@[command_elab checkWPSpecs]
meta def elabCheckWPSpecs : CommandElab := fun stx => do
  let prefixes := stx[1].getArgs.map (·.getId)
  let found := globalSpecs (← getEnv) prefixes
  let outside := found.filter fun (_, decl) => !specAllowlist.contains decl
  for (mod, decl) in outside do
    logError m!"{mod} registers {decl} as a global `@[spec]` rule, and the rule is not on \
      `specAllowlist`. Register a rule tied to one reading with `scoped spec` in the scope of \
      that reading."
  if outside.isEmpty then
    logInfo m!"{found.size} global `@[spec]` registrations, all of rules on `specAllowlist`"

/-- Report every rule on `specAllowlist` that no module under the prefixes registers globally. -/
syntax (name := checkWPAllowlist) "#check_wp_allowlist" (ppSpace ident)+ : command

@[command_elab checkWPAllowlist]
meta def elabCheckWPAllowlist : CommandElab := fun stx => do
  let prefixes := stx[1].getArgs.map (·.getId)
  let registered := (globalSpecs (← getEnv) prefixes).map (·.2)
  let missing := specAllowlist.filter (!registered.contains ·)
  for decl in missing do
    logError m!"{decl} is on `specAllowlist`, and no module under the prefixes registers it as \
      a global `@[spec]` rule."
  if missing.isEmpty then
    logInfo m!"every rule on `specAllowlist` is registered globally"

/-- List how the imported modules register a declaration as an instance or as a `@[spec]`
rule. -/
syntax (name := wpRegistrations) "#wp_registrations " ident : command

@[command_elab wpRegistrations]
meta def elabWPRegistrations : CommandElab := fun stx => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let env ← getEnv
  let mut lines : Array MessageData := #[]
  for h : i in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]
    for entry in instanceExtension.ext.getModuleEntries env i do
      match entry with
      | .global e =>
        if e.globalName? == some declName then lines := lines.push m!"global instance, from {mod}"
      | .scoped ns e =>
        if e.globalName? == some declName then
          lines := lines.push m!"instance scoped in {ns}, from {mod}"
    for (scope?, decl) in specRegistrations env i do
      if decl == declName then
        lines := lines.push <| match scope? with
          | none => m!"global `@[spec]` rule, from {mod}"
          | some ns => m!"`@[spec]` rule scoped in {ns}, from {mod}"
  logInfo m!"{declName}:{indentD (MessageData.joinSep lines.toList Format.line)}"

end PolyFunTest.Policy.WP
