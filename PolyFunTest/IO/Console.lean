/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunIO.Console
meta import PolyFunIO.Console

/-!
# Scripted console forms

The deterministic console handler runs the same typed forms as the IO handler: whitespace
around a number is accepted, an unparsable line is an input error, exhausted input is the end
of input, and prompts and writes are emitted in order.
-/

public section

namespace PolyFunTest.IO

open PolyFunIO

/-- Run a form against scripted input lines, returning its outcome and the emitted output. -/
def runScripted {α : Type} (form : Form α) (input : List String) :
    Except InputError α × Array String :=
  let (result, state) := (form.interpret consoleMemoryHandler).run { input := input }
  (result, state.output)

/-- Check the scripted outcomes of a few forms. -/
def checks : IO Unit := do
  unless (runScripted (Form.natural "n? ") [" 42 "]).1.toOption == some 42 do
    throw (IO.userError "a padded number was not read")
  unless (match (runScripted (Form.natural "n? ") ["many"]).1 with
      | .error (.invalid _) => true | _ => false) do
    throw (IO.userError "an unparsable number was accepted")
  unless (match (runScripted (Form.natural "n? ") []).1 with
      | .error .endOfInput => true | _ => false) do
    throw (IO.userError "exhausted input was not the end of input")
  unless (runScripted (Form.boolean "ok? ") ["yes"]).1.toOption == some true do
    throw (IO.userError "a yes/no choice was not read")
  unless (runScripted (do Form.write "hi"; Form.text "name? ") ["Ada"]).2 == #["hi", "name? "] do
    throw (IO.userError "writes and prompts were not emitted in order")
  IO.println "console forms: ok"

/-- info: console forms: ok -/
#guard_msgs in
#eval checks

end PolyFunTest.IO
