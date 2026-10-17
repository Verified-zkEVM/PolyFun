/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Pipeline.App
public import Cli

/-! # A local file-reporting CLI composed from polynomial components -/

public section

/-- Generated argument validation precedes all filesystem access. -/
def runReport (parsed : Cli.Parsed) : IO UInt32 := do
  let paths := parsed.variableArgsAs! String |>.toList
  let fuel := (parsed.flag? "fuel").map (·.as! Nat) |>.getD (Pipeline.activationBudget paths)
  let splitAt := (parsed.flag? "split-at").map (·.as! Nat)
  Pipeline.report paths fuel splitAt

/-- Ordinary reporting and explicitly bounded execution use the same network. -/
def reportCommand : Cli.Cmd := `[Cli|
  report VIA runReport;
  "Read files without modifying them; report byte and LF-byte counts in input order."
  FLAGS:
    fuel : Nat; "Total network activations; default is nine per supplied path, not a time limit."
    "split-at" : Nat; "Pause and continue in-process at this activation (capped by fuel)."
  ARGS:
    ...files : String; "Paths to read; repeated paths are separate requests."
]

/-- The upstream CLI library owns parsing and help rendering. -/
def command : Cli.Cmd := `[Cli|
  pipeline NOOP;
  "A cooperative, read-only file pipeline. No threads, checkpoints, or input-file writes."
  SUBCOMMANDS:
    reportCommand
  EXTENSIONS:
    Cli.helpSubCommand
]

/-- Execute the selected workflow with generated help for an empty invocation. -/
def main (args : List String) : IO UInt32 :=
  command.validate (if args.isEmpty then ["--help"] else args)
