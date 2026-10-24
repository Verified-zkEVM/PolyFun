/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunCryptol.Translation.CLI
import PolyFunCryptol.Translation.SourceCLI

/-! # Executable Cryptol model and importer workflows -/

/-- Dispatch model observations and typed-AST source checks. -/
public def main (args : List String) : IO UInt32 :=
  match args with
  | "model" :: args => Cryptol.CLI.run args
  | "source" :: args => Cryptol.Translation.SourceCLI.run args
  | _ => do
    (← IO.getStderr).putStrLn "Usage: polyfun-cryptol {model | source} COMMAND ..."
    return 1
