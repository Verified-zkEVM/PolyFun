/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# The `wp_norm` attribute

This module declares the `wp_norm` simp attribute. `PolyFun.Control.Do.Normalization` registers
its lemmas: the rewrites that turn the assertion vocabulary of core's `Std.WP` in the verification
conditions of `vcgen` into the vocabulary of the assertion carrier.
-/

@[expose] public section

/-- Simp set that rewrites the assertion vocabulary of core's `Std.WP` in the verification
conditions of `vcgen` into the vocabulary of the assertion carrier. -/
register_simp_attr wp_norm
