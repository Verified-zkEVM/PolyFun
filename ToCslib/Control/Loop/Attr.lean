/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# The `loop_norm` simp set

This module declares the `loop_norm` simp attribute. `ToCslib.Control.Loop.Basic` registers its
rules, which rewrite the `forIn` loops that `Id.run do` elaborates to into folds over lists.
-/

@[expose] public section

/-- Simp set that rewrites effect-free `for` loops into folds over lists: `Id.run`, legacy ranges
`[a:b]` as `List.range'`, bodies that only yield as `List.foldl`, and the monad laws that expose
those bodies. -/
register_simp_attr loop_norm
