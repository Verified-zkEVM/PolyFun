/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Parliament.App.Main

/-! # Entry point for the Parliament worked example -/

/-- Run the example's command-line application. -/
public def main (args : List String) : IO UInt32 := Parliament.App.main args
