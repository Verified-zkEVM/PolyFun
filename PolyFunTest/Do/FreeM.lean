/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Do

/-!
# `vcgen` smoke tests over the free monad

Core's `vcgen` decomposes `do`-programs over `FreeM P` with uninterpreted operations under the
scoped demonic interpretation of `PolyFun.PFunctor.Free.Do`. Each query is discharged through
the registered `Spec.lift` specification — an operation guarantees its postcondition for every
possible response — and a discharged triple converts back into a fact about the program's
possible outputs.
-/

@[expose] public section

set_option mvcgen.warning false

open Std.Internal.Do PFunctor
open scoped PFunctor.FreeM.DemonicWP

/-- A single-position query interface with boolean responses. -/
abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

/-- Two coin flips, combined with `&&`. -/
def flipTwo : FreeM coinP Bool := do
  let a ← FreeM.lift (P := coinP) PUnit.unit
  let b ← FreeM.lift (P := coinP) PUnit.unit
  pure (a && b)

/-- `vcgen` decomposes a two-query bind chain; the leaf VCs quantify over each response. -/
example : ⦃ True ⦄ flipTwo ⦃ fun r => r = true ∨ r = false ⦄ := by
  vcgen [flipTwo]
  exact Bool.eq_false_or_eq_true _

/-- A query whose result is post-processed deterministically. -/
def flipNot : FreeM coinP Bool := do
  let a ← FreeM.lift (P := coinP) PUnit.unit
  pure (!a)

example : ⦃ True ⦄ flipNot ⦃ fun r => r = true ∨ r = false ⦄ := by
  vcgen [flipNot]
  exact Bool.eq_false_or_eq_true _

/-! ## From weakest preconditions back to supports -/

/-- A query whose result is forced to `false`, giving a program-specific postcondition. -/
def maskFalse : FreeM coinP Bool := do
  let a ← FreeM.lift (P := coinP) PUnit.unit
  pure (a && false)

theorem maskFalse_spec : ⦃ True ⦄ maskFalse ⦃ fun r => r = false ⦄ := by
  vcgen [maskFalse]
  simp

/-- Soundness transports the verification condition to every reachable result. -/
example (a : Bool) (h : MonadAttach.CanReturn maskFalse a) : a = false :=
  LawfulWPMonadAttach.of_canReturn_wp (P := fun r => r = false) h <| by
    intro _
    simpa only [Lean.Order.ofProp_prop_eq] using maskFalse_spec.le_wp trivial

/-- The same, phrased as the "always" judgment over the support. -/
example : MonadAttach.AllOutputs (fun b => b = false) maskFalse := by
  refine MonadAttach.allOutputs_of_wp fun _ => ?_
  simpa only [Lean.Order.ofProp_prop_eq] using maskFalse_spec.le_wp trivial

/-! ## The angelic reading -/

/-- Under the angelic interpretation the same program can return `true`: one response suffices. -/
example : (letI := PFunctor.FreeM.AngelicWP.instWPMonadSome (P := coinP);
    Triple flipNot True (fun r => r = true) Lean.Order.bot) := by
  let inst := PFunctor.FreeM.AngelicWP.instWPMonadSome (P := coinP)
  refine ⟨fun _ => ?_⟩
  change MonadAttach.SomeOutput _ _
  refine ⟨true, MonadAttach.canReturn_bind_iff.mpr
    ⟨false, ?_, ExactMonadAttach.canReturn_pure true⟩, rfl⟩
  rw [← MonadAttach.mem_support, FreeM.support_lift]
  exact Set.mem_univ _
