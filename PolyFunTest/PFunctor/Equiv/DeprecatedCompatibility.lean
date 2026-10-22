/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Equiv.Basic

/-!
# Direct-import compatibility for the deprecated equivalence API

These canaries import only `PFunctor.Equiv.Basic`. They ensure downstream files
using the deprecated `instIsEmptySigma` keep elaborating without relying on an
aggregate import.
-/

@[expose] public section

section IsEmptySigma

set_option linter.deprecated false

universe u v

-- Old universe arity and named instance binder remain available without an aggregate import.
example {α : Sort u} {β : α → Sort v} (inst : IsEmpty α) : IsEmpty ((a : α) ×' β a) :=
  instIsEmptySigma.{u, v} (α := α) (β := β) (inst := inst)

-- The old declaration can still supply the local instance used by instance search.
example {α : Sort u} {β : α → Sort v} (inst : IsEmpty α) : IsEmpty ((a : α) ×' β a) := by
  let := @instIsEmptySigma.{u, v} α β inst
  infer_instance

-- Old instance registration remains usable when the preferred instance is locally removed.
attribute [-instance] PSigma.isEmpty_left in
example {α : Sort u} {β : α → Sort v} [IsEmpty α] : IsEmpty ((a : α) ×' β a) :=
  inferInstance

end IsEmptySigma
