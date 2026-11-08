/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

import PolyFun.Logic.KernelRfl
meta import PolyFun.Logic.KernelRfl
public meta import Lean.Elab.Command

/-!
# `kernel_rfl`

The kernel proves an equation that elaborator `rfl` cannot reach within the default limits.
The tactic handles hypotheses, binders and universe parameters, and names its auxiliary lemma
after the enclosing declaration. A false equation fails at the tactic, also when
`debug.skipKernelTC` or `Elab.async` is set, and leaves no axiom in the environment. Under
`Elab.async`, `KernelRfl.addKernelLemma` adds no constant for it. Without the restore in
`KernelRfl.addKernelLemma`, `mkAuxLemma` would leave one. A heartbeat or recursion-depth limit
also makes the tactic fail loudly, with nothing left behind.
-/

public section

namespace PolyFunTest.KernelRfl

open Lean Meta Elab Command

/-- The axioms declared in the current module. -/
meta def localAxioms (env : Environment) : Array Name :=
  env.constants.map₂.foldl (init := #[]) fun acc name info =>
    if info matches .axiomInfo _ then acc.push name else acc

/-- The number of constants declared in the current module. -/
meta def localConstants (env : Environment) : Nat :=
  env.constants.map₂.foldl (init := 0) fun n _ _ => n + 1

/-- Report the axioms declared in the current module. -/
elab "#local_axioms" : command => do
  logInfo m!"local axioms: {localAxioms (← getEnv)}"

/-- Report the constants of the current module that belong to an `example`, such as the
auxiliary lemmas of a `kernel_rfl` inside one. -/
elab "#example_constants" : command => do
  let names := (← getEnv).constants.map₂.foldl (init := #[]) fun acc name _ =>
    if (privateToUserName name).components.contains `_example then acc.push name else acc
  logInfo m!"example constants: {names}"

/-- A sum of `n` ones by a list fold, cheap for the kernel and deep for the elaborator. -/
@[expose] def sumList (n : Nat) : Nat := (List.replicate n 1).foldr (· + ·) 0

/-! ## Accepted equations -/

theorem sumList_eq : sumList 20000 = 20000 := by kernel_rfl

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : sumList 20000 = 20000 := by rfl

theorem id_apply.{u} (α : Sort u) (a : α) : (fun x : α => x) a = a := by kernel_rfl

theorem add_zero_of_eq (n : Nat) (_h : n = 3) : n + 0 = n := by kernel_rfl

theorem sumList_forall : ∀ k : Fin 3, sumList (k.val + 2) = k.val + 2 := by
  intro k
  match k with
  | 0 => kernel_rfl
  | 1 => kernel_rfl
  | 2 => kernel_rfl

namespace Inner

theorem sumList_three : sumList 3 = 3 := by kernel_rfl

end Inner

-- The auxiliary lemma lives below the enclosing declaration's name.
/-- info: true -/
#guard_msgs in
run_meta do
  let .thmInfo info ← withoutExporting (getConstInfo ``Inner.sumList_three)
    | throwError "not a theorem"
  let .const name _ := info.value | throwError "unexpected proof term"
  logInfo m!"{(privateToUserName name).getPrefix == ``Inner.sumList_three}"

/-! ## Rejected equations -/

/--
error: (kernel) declaration type mismatch, '_private.PolyFunTest.Logic.KernelRfl.0.PolyFunTest.KernelRfl._example._proof_1' has type
  1 = 1
but it is expected to have type
  1 = 2
-/
#guard_msgs in
example : (1 : Nat) = 2 := by kernel_rfl

-- `debug.skipKernelTC` does not switch the check off.
/--
error: (kernel) declaration type mismatch, '_private.PolyFunTest.Logic.KernelRfl.0.PolyFunTest.KernelRfl._example._proof_1' has type
  1 = 1
but it is expected to have type
  1 = 2
-/
#guard_msgs in
set_option debug.skipKernelTC true in
example : (1 : Nat) = 2 := by kernel_rfl

-- `Elab.async` does not defer the check past the tactic.
/--
error: (kernel) declaration type mismatch, '_private.PolyFunTest.Logic.KernelRfl.0.PolyFunTest.KernelRfl._example._proof_1' has type
  1 = 1
but it is expected to have type
  1 = 2
-/
#guard_msgs in
set_option Elab.async true in
example : (1 : Nat) = 2 := by kernel_rfl

/--
error: kernel_rfl: the goal is not an equation
  1 ≤ 2
-/
#guard_msgs in
example : (1 : Nat) ≤ 2 := by kernel_rfl

-- A heartbeat limit stops the kernel check.
/-- error: (kernel) deterministic timeout -/
#guard_msgs in
example : sumList 20000 = 20000 := by
  set_option maxHeartbeats 1 in
  -- Lowered for this proof only, below what the kernel check needs.
  kernel_rfl

-- A recursion-depth limit stops the tactic itself.
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : sumList 20000 = 20000 := by
  set_option maxRecDepth 8 in
  kernel_rfl

-- None of the failures leaves an auxiliary lemma behind.
/-- info: example constants: [] -/
#guard_msgs in
#example_constants

-- No rejected statement remains as an axiom.
/-- info: local axioms: [] -/
#guard_msgs in
#local_axioms

-- `mkAuxLemma` alone leaves a fallback axiom after a kernel failure; `addKernelLemma` does not.
-- Both runs discard their environment afterwards.
/--
info: mkAuxLemma leaves an axiom: true
---
info: addKernelLemma leaves an axiom: false
-/
#guard_msgs in
run_meta do
  let type ← mkEq (mkNatLit 1) (mkNatLit 2)
  let value ← mkEqRefl (mkNatLit 1)
  withoutModifyingEnv do
    try discard <| withOptions PolyFun.Logic.KernelRfl.checkedOptions <| mkAuxLemma [] type value
    catch _ => pure ()
    logInfo m!"mkAuxLemma leaves an axiom: {!(localAxioms (← getEnv)).isEmpty}"
  withoutModifyingEnv do
    try discard <| PolyFun.Logic.KernelRfl.addKernelLemma [] type value
    catch _ => pure ()
    logInfo m!"addKernelLemma leaves an axiom: {!(localAxioms (← getEnv)).isEmpty}"

-- With `Elab.async` set, `addKernelLemma` still rejects the false statement and adds no constant.
/--
info: addKernelLemma rejects it: true
---
info: addKernelLemma adds no constant: true
-/
#guard_msgs in
run_meta do
  let type ← mkEq (mkNatLit 1) (mkNatLit 2)
  let value ← mkEqRefl (mkNatLit 1)
  withoutModifyingEnv do
    let before := localConstants (← getEnv)
    let rejected ← withOptions (Elab.async.set · true) do
      try discard <| PolyFun.Logic.KernelRfl.addKernelLemma [] type value; pure false
      catch _ => pure true
    logInfo m!"addKernelLemma rejects it: {rejected}"
    logInfo m!"addKernelLemma adds no constant: {localConstants (← getEnv) == before}"

/-- info: local axioms: [] -/
#guard_msgs in
#local_axioms

end PolyFunTest.KernelRfl
