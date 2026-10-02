/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Parliament.App.Storage
public import Cli

/-! # Command-line workflows for new meetings, recovery, reconstruction, and verification -/

@[expose] public section

namespace Parliament.App

open System

/-- Versioned configuration template printed by the executable's `example-config` command. -/
def exampleConfiguration : Configuration := {
  rules := { quorum := 3 },
  members := [⟨0, true, true⟩, ⟨1, true, true⟩, ⟨2, true, true⟩, ⟨3, true, true⟩],
  chair := 0,
  calendar := { today := ⟨2026, 1, 15⟩, nextRegular := ⟨2026, 2, 15⟩ },
  committees := [7],
  metadata := { organization := "Example Assembly", title := "Regular meeting" } }

/-- Parsed workflows keep argument validation separate from filesystem execution. -/
inductive Workflow where
  | exampleConfig
  | create (configPath directory : String)
  | resume (directory : String)
  | replay (journalPath directory : String)
  | verify (journalPath directory : String)

/-- Execute the selected workflow; all interactive procedure is delegated to the application
machine. -/
def runWorkflow (workflow : Workflow) : IO UInt32 := do
  match workflow with
  | .exampleConfig => Terminal.print (encodeJson exampleConfiguration); return 0
  | .create configPath directory =>
    let config : Configuration ← match decodeJson (← IO.FS.readFile configPath) with
      | .ok value => pure value
      | .error error => throw (IO.userError ("configuration parse failed: " ++ error))
    let journal ← match config.start with
      | .ok value => pure value
      | .error error => throw (IO.userError error)
    let directory := (directory : FilePath).normalize
    if ← directory.pathExists then
      throw (IO.userError "meeting directory already exists; use resume")
    let directory : FilePath :=
      (directory.toString.dropEndWhile (fun c => FilePath.pathSeparators.contains c)).toString
    if let some parent := directory.parent then IO.FS.createDirAll parent
    -- Exclusive creation also prevents racing `new` processes from resetting one another.
    IO.FS.createDir directory
    withWriter directory do
      persistJournal directory (snapshot config journal)
      runTerminal config directory journal
  | .resume directory =>
    let directory : FilePath := directory
    withWriter directory do
      let wire ← readJournal (directory / "journal.json")
      let journal ← restoreJournal wire
      runTerminal wire.config directory journal
  | .replay journalPath directory =>
    let wire ← readJournal journalPath
    let journal ← restoreJournal wire
    let directory : FilePath := directory
    IO.FS.createDirAll directory
    withWriter directory do
      publishArtifacts directory journal (artifacts wire.config.metadata journal)
      Terminal.print s!"Replayed {wire.commands.length} commands; \
        exported revision {journal.state.revision}.\n"
      pure 0
  | .verify journalPath directory =>
    let wire ← readJournal journalPath
    let journal ← restoreJournal wire
    checkExport directory (artifacts wire.config.metadata journal)
    Terminal.print s!"Verified draft revision {journal.state.revision}.\n"
    pure 0

/-- Execute a parsed create request. -/
def runNew (p : Cli.Parsed) : IO UInt32 :=
  runWorkflow (.create (p.flag! "config" |>.as! String) (p.flag! "dir" |>.as! String))

/-- Execute a parsed resume request. -/
def runResume (p : Cli.Parsed) : IO UInt32 :=
  runWorkflow (.resume (p.positionalArg! "directory" |>.as! String))

/-- Execute a parsed replay request. -/
def runReplay (p : Cli.Parsed) : IO UInt32 :=
  runWorkflow (.replay (p.positionalArg! "journal" |>.as! String) (p.flag! "out" |>.as! String))

/-- Execute a parsed verification request. -/
def runVerify (p : Cli.Parsed) : IO UInt32 :=
  runWorkflow (.verify (p.positionalArg! "journal" |>.as! String)
    (p.positionalArg! "export" |>.as! String))

/-- Print the configuration template without acquiring any storage resources. -/
def runConfig (_ : Cli.Parsed) : IO UInt32 := runWorkflow .exampleConfig

/-- Generated new-meeting help and flag validation. -/
def newCommand : Cli.Cmd := `[Cli|
  new VIA runNew;
  "Create a new meeting; existing directories are never reset."
  FLAGS:
    config : String; "Configuration JSON file."
    dir : String; "New meeting directory."
  EXTENSIONS:
    Cli.require! #["config", "dir"]
]

/-- Generated recovery help and parsing. -/
def resumeCommand : Cli.Cmd := `[Cli|
  resume VIA runResume;
  "Validate and resume a recorded meeting."
  ARGS:
    directory : String; "Meeting directory."
]

/-- Generated reconstruction help and parsing. -/
def replayCommand : Cli.Cmd := `[Cli|
  replay VIA runReplay;
  "Replay all commands and reconstruct draft artifacts."
  FLAGS:
    out : String; "Output directory."
  ARGS:
    journal : String; "Versioned journal JSON."
  EXTENSIONS:
    Cli.require! #["out"]
]

/-- Generated artifact-verification help and parsing. -/
def verifyCommand : Cli.Cmd := `[Cli|
  verify VIA runVerify;
  "Compare exact exported bytes with the replayed journal."
  ARGS:
    journal : String; "Versioned journal JSON."
    "export" : String; "Revision directory containing minutes.json and minutes.md."
]

/-- Generated configuration-template help. -/
def configCommand : Cli.Cmd := `[Cli|
  "example-config" VIA runConfig;
  "Print a sample configuration to standard output."
]

/-- Upstream CLI parsing supplies generated help and nonzero statuses for invalid arguments. -/
def command : Cli.Cmd := `[Cli|
  parliament NOOP;
  "Record a meeting with explicit human judgments and a replay-checked journal."
  SUBCOMMANDS:
    newCommand;
    resumeCommand;
    replayCommand;
    verifyCommand;
    configCommand
  EXTENSIONS:
    Cli.helpSubCommand
]

/-- Parse a workflow before opening any filesystem resources. -/
def cli (args : List String) : IO UInt32 :=
  command.validate (if args.isEmpty then ["--help"] else args)

/-- Convert backend failures to a visible diagnostic and nonzero process status. -/
def main (args : List String) : IO UInt32 := do
  try cli args
  catch error =>
    (← IO.getStderr).putStrLn ("parliament: " ++ error.toString)
    return 1

end Parliament.App
