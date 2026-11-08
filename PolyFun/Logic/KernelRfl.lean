/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.AuxLemma
public meta import Lean.Meta.Tactic.Cleanup
public meta import Lean.Meta.Tactic.Revert

/-!
# Definitional equations checked by the kernel alone

`kernel_rfl` closes a goal `lhs = rhs`, possibly under hypotheses and binders, with the proof
`Eq.refl lhs`, and leaves the definitional check to the kernel. The elaborator never compares the
two sides. So the tactic proves equations that are cheap for the kernel but exceed the elaborator's
recursion depth or heartbeats, such as an equation lemma that unfolds a large interpreted term.

The tactic works like core's `decide +kernel`: it reverts the local context, adds the closed
statement as an auxiliary lemma through `mkAuxLemma`, and assigns the goal to that lemma. The
lemma is named after the enclosing declaration, in its namespace, and takes the universe
parameters that occur in the goal. The kernel check runs at once, with asynchronous elaboration
off and `debug.skipKernelTC` forced off, so a failure is reported at the tactic.

A failed kernel check never leaves an axiom behind. `addDecl` adds a statement the kernel
rejects as an axiom, to avoid follow-up errors, and the environment keeps it even when the error
is caught. `KernelRfl.addKernelLemma` restores the environment from before the check and rethrows,
also when a heartbeat or recursion-depth limit stops it.

The kernel unfolds a definition from another module only if its body is exposed, so under the
module system `kernel_rfl` fails on equations that need a hidden body.

Core Lean has `decide +kernel` for decidable propositions but no kernel-only `rfl`. This tactic is
a candidate for upstream as `rfl +kernel`.
-/

public section

/-- `kernel_rfl` closes `lhs = rhs`, possibly under hypotheses and binders, with `Eq.refl lhs`,
which only the kernel checks. It fails when the kernel does not accept the two sides as
definitionally equal; nothing is added to the environment then. -/
syntax (name := kernelRfl) "kernel_rfl" : tactic

namespace PolyFun.Logic.KernelRfl

open Lean Meta Elab Tactic

/-- Options for a kernel check that cannot be deferred or skipped: asynchronous elaboration off
and `debug.skipKernelTC` off. -/
meta def checkedOptions (opts : Options) : Options :=
  (Elab.async.set opts false).setBool `debug.skipKernelTC false

/-- Add `value : type` as an auxiliary lemma with universe parameters `levels`, checked by the
kernel now. If the check fails, the environment is restored to its state before the call, which
removes the axiom `addDecl` adds in place of a rejected lemma, and the error is rethrown. The
handler also covers heartbeat and recursion-depth limits, which `try … catch` lets pass. -/
meta def addKernelLemma (levels : List Name) (type value : Expr) : MetaM Name := do
  let env ← getEnv
  tryCatchRuntimeEx (withOptions checkedOptions <| mkAuxLemma levels type value) fun ex => do
    setEnv env
    throw ex

/-- The proof `fun xs => Eq.refl lhs` of a closed statement `∀ xs, lhs = rhs`. -/
meta def reflProof (type : Expr) : MetaM Expr :=
  forallTelescope type.cleanupAnnotations fun xs body => do
    let some (α, lhs, _) := body.cleanupAnnotations.eq?
      | throwError "kernel_rfl: the goal is not an equation{indentExpr body}"
    mkLambdaFVars xs (mkApp2 (mkConst ``Eq.refl [← getLevel α]) α lhs)

/-- Elaborate `kernel_rfl`. -/
@[tactic kernelRfl] meta def evalKernelRfl : Tactic := fun _ => do
  let levelNames ← Term.getLevelNames
  liftMetaFinishingTactic fun goal => do
    let goal ← goal.cleanup
    let (_, goal) ← goal.revert (clearAuxDeclsInsteadOfRevert := true)
      (← goal.getDecl).lctx.getFVarIds
    goal.withContext do
      let type ← instantiateMVars (← goal.getType)
      if type.hasMVar then
        throwError "kernel_rfl: the goal contains metavariables{indentExpr type}"
      let value ← reflProof type
      let used := (collectLevelParams {} type).params
      let levels := levelNames.reverse.filter used.contains
      let name ← addKernelLemma levels type value
      goal.assign (mkConst name (levels.map Level.param))

end PolyFun.Logic.KernelRfl
