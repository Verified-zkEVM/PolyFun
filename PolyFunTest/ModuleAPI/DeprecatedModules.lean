/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFun.Interaction.UC.OpenProcess -- deprecated_module: ignore
import PolyFun.Interaction.UC.ReactiveNetwork.Serial -- deprecated_module: ignore

/-!
# Compatibility module shims

The retired `PolyFun.Interaction.UC` paths are `deprecated_module` shims that re-export their
replacements (`docs/development/compatibility.md`). This ordinary-import canary checks two of them
from a consumer's position: the environment records exactly these deprecations with their
replacement modules, and a name owned by the replacement resolves through the shim alone.
Lean reports a deprecated import as a header warning, which `#guard_msgs` cannot capture, so the
imports carry Lean's per-import ignore suffix and the deprecation record is read back with
`#show_deprecated_modules` instead.
-/

/--
info: Deprecated modules

'PolyFun.Interaction.UC.OpenProcess' deprecates to
#[PolyFun.Interaction.Open.OpenProcess]
with message 'use `PolyFun.Interaction.Open.OpenProcess`'

'PolyFun.Interaction.UC.ReactiveNetwork.Serial' deprecates to
#[PolyFun.Interaction.Execution.ReactiveNetwork.Serial]
with message 'use `PolyFun.Interaction.Execution.ReactiveNetwork.Serial`'
-/
#guard_msgs in
#show_deprecated_modules

/-- The replacement's declarations are visible through the shim's `public import`. -/
example := @Interaction.Open.OpenProcess

/-- The execution-side shim re-exports its replacement as well. -/
example := @Interaction.Execution.ReactiveNetwork.runSerial_eq_runToken
