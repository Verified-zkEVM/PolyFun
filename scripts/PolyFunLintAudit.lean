/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public meta import Lean
public meta import Batteries.Tactic.Lint

/-!
# Read-only environment linter audit

Imports each production root independently, matching Batteries' runner. Reports registered
linters, raw findings (including declarations tagged `nolint`), and annotations whose checks
now pass. JSON allowlist matching is performed by the Python frontend across all roots.
The default private-level import matches Batteries and includes private bodies.
The optional exported-level import diagnoses why ordinary imports are insufficient for linting.
-/

open Lean Batteries.Tactic.Lint

public meta section

private def str (n : Name) : Json := toJson n.toString

private def auditRoot (root : Name) (extra : Array Name) : CoreM Json := do
  let env ← getEnv
  let decls ← getDeclsInPackage root.getRoot
  for name in extra do
    unless (batteriesLinterExt.getState env).contains name do
      throwError "Unknown environment linter {name}"
  let linters ← getChecks (slow := true) (runOnly := none)
    (runAlways := if extra.isEmpty then none else some extra.toList)
  if linters.isEmpty then throwError "No environment linters registered for {root}"
  let results ← lintCore decls linters
  let mut findings : Array Json := #[]
  let mut annotations : Array Json := #[]
  for (linter, msgs) in results do
    for (decl, msg) in msgs.toArray do
      findings := findings.push <| Json.mkObj [
        ("linter", str linter.name), ("declaration", str decl),
        ("message", toJson (← msg.toString)), ("annotation", toJson false)]
    -- The normal runner filters these before invoking a linter. Test them directly,
    -- without modifying the imported environment or any committed suppression file.
    for decl in decls do
      if !(← shouldBeLinted linter.name decl) then
        let result ← try
            linter.test decl |>.run' Lean.Elab.Command.mkMetaContext
          catch e => pure <| some m!"LINTER FAILED: {e.toMessageData}"
        annotations := annotations.push <| Json.mkObj [
          ("linter", str linter.name), ("declaration", str decl),
          ("needed", toJson result.isSome)]
        if let some msg := result then
          findings := findings.push <| Json.mkObj [
            ("linter", str linter.name), ("declaration", str decl),
            ("message", toJson (← msg.toString)), ("annotation", toJson true)]
  let registered := (batteriesLinterExt.getState env).toArray.map fun (name, decl, enabled) =>
    Json.mkObj [("name", str name), ("declaration", str decl), ("default", toJson enabled)]
  let sets := (Lean.Linter.linterSetsExt.getState env).merged.toArray.map fun (name, members) =>
    Json.mkObj [("option", str name), ("sets", toJson (members.map Name.toString))]
  return Json.mkObj [
    ("root", str root), ("declarations", toJson decls.size),
    ("registered", toJson registered),
    ("active", toJson (linters.map fun l => l.name.toString)),
    ("set_membership", toJson sets), ("findings", toJson findings), ("annotations", toJson annotations)]

/-- Print a JSON audit without updating exception files or compiling target modules. -/
unsafe def main (args : List String) : IO UInt32 := do
  let exported := args.contains "--exported"
  let extra := args.toArray.filterMap fun arg =>
    if arg.startsWith "--extra=" then some (arg.drop 8 |>.toString.toName) else none
  for arg in args do
    if arg.startsWith "--" && arg != "--exported" && !arg.startsWith "--extra=" then
      IO.eprintln s!"Unknown audit option: {arg}"
      return 2
  let roots := (args.filter (!·.startsWith "--")).toArray.map String.toName
  let roots := if roots.isEmpty then #[`PolyFun, `ToCslib] else roots
  initSearchPath (← findSysroot)
  let mut reports : Array Json := #[]
  for root in roots do
    enableInitializersExecution
    let env ← importModules #[{ module := root }, { module := `Batteries.Tactic.Lint }] {}
      (trustLevel := 1024) (loadExts := true)
      (level := if exported then .exported else .private)
    let (report, _) ← (auditRoot root extra).toIO
      { fileName := "<linter-audit>", fileMap := default } { env }
    reports := reports.push report
  IO.println <| (Json.mkObj [
    ("visibility", toJson (if exported then "exported" else "private")),
    ("roots", toJson reports)]).compress
  return 0
