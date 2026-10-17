/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Basic
public import PolyFun.PFunctor.Handler
public import Lean.Data.Json

/-!
# Typed terminal forms and interchangeable console handlers

A form is an ordinary free program with explicit input errors. Parsing and branching
are Lean functions; interpreting the same program in `IO` or `StateM` changes only
the terminal backend. Reading a line preserves its contents, apart from its line ending.
-/

@[expose] public section

namespace PolyFunIO

/-- Line-oriented terminal operations. A read includes the prompt to flush before blocking. -/
inductive ConsoleOp where
  | readLine (prompt : String)
  | write (text : String)
  deriving DecidableEq, Repr

/-- A line read distinguishes EOF from a successfully read empty line. -/
def Console : PFunctor where
  A := ConsoleOp
  B
    | .readLine _ => Option String
    | .write _ => Unit

instance : DecidableEq Console.A := inferInstanceAs (DecidableEq ConsoleOp)

/-- Input outcomes are distinct from backend IO exceptions and domain rejections. -/
inductive InputError where
  | endOfInput
  | cancelled
  | invalid (message : String)
  deriving DecidableEq, Repr

/-- Render an input problem without exposing Lean constructor syntax. -/
def InputError.message : InputError → String
  | .endOfInput => "End of input; no command submitted."
  | .cancelled => "Cancelled; no command submitted."
  | .invalid message => message

/-- A finite typed dialogue using the existing free monad and exception transformer. -/
abbrev Form := ExceptT InputError (PFunctor.FreeM Console)

namespace Form

/-- Request one complete line. Empty input is a value, not EOF or cancellation. -/
def text (prompt : String) : Form String := do
  let answer ← monadLift (PFunctor.FreeM.lift (P := Console) (.readLine prompt))
  match answer with
  | none => throw .endOfInput
  | some value => pure value

/-- Display text without advancing any application model. -/
def write (message : String) : Form Unit :=
  monadLift (PFunctor.FreeM.lift (P := Console) (.write message))

/-- Read a field using an application-supplied, pure parser. -/
def parsed {α : Type} (prompt : String) (parse : String → Except String α) : Form α := do
  match parse (← text prompt) with
  | .ok value => pure value
  | .error message => throw (.invalid message)

/-- Read a natural number, accepting surrounding whitespace. -/
def natural (prompt : String) : Form Nat :=
  parsed prompt fun value ↦
    match value.trimAscii.toString.toNat? with
    | some n => .ok n
    | none => .error "Enter a nonnegative whole number."

/-- Select one of a finite list of named values. -/
def choice {α : Type} (prompt : String) (choices : List (String × α)) : Form α :=
  parsed prompt fun value ↦
    match choices.find? (fun entry ↦ entry.1 == value.trimAscii.toString) with
    | some entry => .ok entry.2
    | none => .error ("Choose " ++ String.intercalate ", " (choices.map Prod.fst) ++ ".")

/-- Read a yes/no field; the JSON Boolean spellings also remain convenient in scripts. -/
def boolean (prompt : String) : Form Bool :=
  choice prompt [("yes", true), ("no", false), ("true", true), ("false", false)]

/-- An explicit JSON field for structured input requiring the upstream codec. -/
def json {α : Type} [Lean.FromJson α] (prompt : String) : Form α :=
  parsed prompt fun value ↦ Lean.Json.parse value >>= Lean.fromJson?

/-- Interpret a form through any console handler, preserving its explicit input outcome. -/
def interpret {m : Type → Type} [Monad m] {α : Type}
    (form : Form α) (handler : PFunctor.Handler m Console) : m (Except InputError α) :=
  form.run.liftM handler

end Form

/-- Scripted terminal state. Exhausting input implements EOF. -/
structure ConsoleMemory where
  /-- Lines still available; line terminators have already been removed. -/
  input : List String := []
  /-- Output fragments, including prompts, in emission order. -/
  output : Array String := #[]
  deriving Inhabited, Repr

/-- Deterministic interpretation of the same console used by the executable. -/
def consoleMemoryHandler : PFunctor.Handler (StateM ConsoleMemory) Console
  | .write message => modify fun state ↦ { state with output := state.output.push message }
  | .readLine prompt => do
    modify fun state ↦ { state with output := state.output.push prompt }
    match (← get).input with
    | [] => pure none
    | value :: rest =>
      modify fun state ↦ { state with input := rest }
      pure (some value)

/-- Interpret through explicit streams; acquiring ambient streams is a separate IO boundary. -/
def consoleIOHandler (stdin stdout : IO.FS.Stream) : PFunctor.Handler IO Console
  | .write text => do
    stdout.putStr text
    stdout.flush
  | .readLine prompt => do
    stdout.putStr prompt
    stdout.flush
    let line ← stdin.getLine
    if line.isEmpty then return none
    let line := if line.endsWith "\n" then (line.dropEnd 1).toString else line
    let line := if line.endsWith "\r" then (line.dropEnd 1).toString else line
    return some line

/-- Run a form on the process's standard streams. -/
def Form.runIO {α : Type} (form : Form α) : IO (Except InputError α) := do
  form.interpret (consoleIOHandler (← IO.getStdin) (← IO.getStdout))

end PolyFunIO
