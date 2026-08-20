/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Do

/-!
# `mvcgen` smoke tests over the free monad

These examples demonstrate that core `Std.Do`'s `mvcgen` decomposes `do`-programs
over `FreeM P` with uninterpreted operations, under the scoped demonic
weakest-precondition instances of `PolyFun.PFunctor.Free.Do`. Each query is
discharged through the registered `Spec.lift` specification: an uninterpreted
operation guarantees its postcondition for every possible response.
-/

@[expose] public section

set_option mvcgen.warning false

open Std.Do
open scoped PFunctor.FreeM.DemonicWP

/-- A single-position query interface with boolean responses. -/
abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

open PFunctor in
/-- Two coin flips, combined with `&&`. -/
def flipTwo : FreeM coinP Bool := do
  let a ← FreeM.lift (P := coinP) PUnit.unit
  let b ← FreeM.lift (P := coinP) PUnit.unit
  pure (a && b)

/-- `mvcgen` decomposes a two-query bind chain; the leaf VCs quantify over each
uninterpreted response. -/
example : ⦃⌜True⌝⦄ flipTwo ⦃⇓ r => ⌜r = true ∨ r = false⌝⦄ := by
  mvcgen [flipTwo]
  intro a b
  cases a && b <;> simp

open PFunctor in
/-- A query whose result is post-processed deterministically. -/
def flipNot : FreeM coinP Bool := do
  let a ← FreeM.lift (P := coinP) PUnit.unit
  pure (!a)

/-- The postcondition can depend on the (universally quantified) response. -/
example : ⦃⌜True⌝⦄ flipNot ⦃⇓ r => ⌜r = true ∨ r = false⌝⦄ := by
  mvcgen [flipNot]
  intro a
  cases a <;> simp
