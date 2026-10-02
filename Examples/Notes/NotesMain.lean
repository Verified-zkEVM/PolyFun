/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Notes.Runtime
public import Cli

/-! # Standalone local Notes executable -/

public section

/-- Open a new notebook after upstream argument validation. -/
def runNew (parsed : Cli.Parsed) : IO UInt32 :=
  Notes.main true (parsed.positionalArg! "directory" |>.as! String)

/-- Open an existing notebook after upstream argument validation. -/
def runOpen (parsed : Cli.Parsed) : IO UInt32 :=
  Notes.main false (parsed.positionalArg! "directory" |>.as! String)

/-- Generated new-notebook help and parsing. -/
def newCommand : Cli.Cmd := `[Cli|
  new VIA runNew;
  "Create a local notebook in a new directory."
  ARGS:
    directory : String; "Explicit notebook directory; existing directories are never reset."
]

/-- Generated reopen help and parsing. -/
def openCommand : Cli.Cmd := `[Cli|
  "open" VIA runOpen;
  "Reopen and validate an existing notebook."
  ARGS:
    directory : String; "Directory containing journal.json."
]

/-- Select the short prompt or the full edit dialogue. -/
def runDemo (parsed : Cli.Parsed) : IO UInt32 := do
  match parsed.variableArgsAs! String |>.toList with
  | [model] => Notes.Walkthrough.demo model
  | ["edit", model] => Notes.Walkthrough.demoEdit model
  | _ =>
    (← IO.getStderr).putStrLn "Use demo MODEL or demo edit MODEL."
    return 2

/-- Generated demo help. -/
def demoCommand : Cli.Cmd := `[Cli|
  demo VIA runDemo;
  "In-memory demos: MODEL or edit MODEL; free/indexed/system/machine/resumption/tree."
  ARGS:
    ...arguments : String; "A model, optionally preceded by edit."
]

/-- Notebook workflows and executable representation demos. -/
def command : Cli.Cmd := `[Cli|
  notes NOOP;
  "Local versioned notes. Interactive commands: new, edit, preview, list, history, back, \
   forward, live, quit. No files are written by demos."
  SUBCOMMANDS:
    newCommand;
    openCommand;
    demoCommand
  EXTENSIONS:
    Cli.helpSubCommand
]

/-- Upstream argument validation supplies consistent errors and generated help. -/
public def main (args : List String) : IO UInt32 :=
  command.validate (if args.isEmpty then ["--help"] else args)
