/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Open.OpenTheory.Family

/-!
# Compatibility module for `PolyFun.Interaction.UC.OpenTheory.Family`

The content now lives in `PolyFun.Interaction.Open.OpenTheory.Family`.
This module only re-exports it, so existing imports of the former path keep resolving. It
carries no declarations of its own and is removed on the schedule in
`docs/development/compatibility.md`.
-/

deprecated_module "use `PolyFun.Interaction.Open.OpenTheory.Family`"
  (since := "2026-09-26")

public section
