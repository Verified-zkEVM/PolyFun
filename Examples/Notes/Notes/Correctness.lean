/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Notes.Walkthrough
public import PolyFun.ITree.Bisim.Bind
public import PolyFun.PFunctor.Bound

/-! # What the representation walkthrough preserves

The indexed dialogue expands to the same console program, for every lawful handler.
Returning machines and resumptions have exactly the source's behavior. The tree's extra
silent step preserves weak behavior, not its activation budget. The continuing system
retains completed syntax and silently stutters rather than returning a second result.
-/

public section

namespace Notes.Walkthrough

open PolyFunIO PFunctor PFunctor.DynSystem

/-- Indexed collection and confirmation preserve every effect of the common console program. -/
theorem indexedEdit_interpret {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : Handler m Console) :
    (indexedEdit.toSigmaFreeM EditProtocol).liftM (editProtocolHandler handler) =
      (Preview.form demoNotebook).interpret handler := by
  have expand := IPFunctor.FreeM.toSigmaFreeM_liftBind EditProtocol EditPhase.collect ()
    (fun result ↦ match result with
      | .error error => IPFunctor.FreeM.pure EditPhase.done (Except.error error)
      | .ok proposal => IPFunctor.FreeM.liftBind (EditPhase.confirm proposal) ()
          fun answer ↦ IPFunctor.FreeM.pure EditPhase.done answer)
  have expand' := congrArg (FreeM.liftM (editProtocolHandler handler)) expand
  apply expand'.trans
  rw [FreeM.liftBind_eq, FreeM.bind_eq_bind, FreeM.liftM_lift_bind]
  unfold Preview.form Form.interpret
  change ((Preview.prepare demoNotebook).run.liftM handler >>= fun result ↦ _) =
    ((Preview.prepare demoNotebook).run >>= fun result ↦
      ExceptT.bindCont Preview.confirm result).liftM handler
  rw [FreeM.liftM_bind]
  apply bind_congr
  intro result
  cases result with
  | error error =>
    rw [IPFunctor.FreeM.toSigmaFreeM_pure EditProtocol EditPhase.done (Except.error error)]
    rfl
  | ok proposal =>
    rw [IPFunctor.FreeM.toSigmaFreeM_liftBind EditProtocol (EditPhase.confirm proposal) ()]
    rw [FreeM.liftBind_eq, FreeM.bind_eq_bind, FreeM.liftM_lift_bind]
    simp only [IPFunctor.FreeM.toSigmaFreeM_pure EditProtocol EditPhase.done]
    change ((Preview.confirm proposal).interpret handler >>= fun answer ↦ pure answer) =
      (Preview.confirm proposal).interpret handler
    exact bind_pure _

/-- The returning machine implements the exact source resumption. -/
theorem edit_machine_denote :
    (DynComputation.ofFreeM (fun (_ : Unit) ↦ (Preview.form demoNotebook).run)).denote () =
      (Preview.form demoNotebook).run.toResumption :=
  DynComputation.denote_ofFreeM _ _

/-- Realizing a resumption does not add an observable operation. -/
theorem edit_resumption_denote :
    (DynComputation.ofResumption
      (fun (_ : Unit) ↦ (Preview.form demoNotebook).run.toResumption)).denote () =
      (Preview.form demoNotebook).run.toResumption :=
  DynComputation.denote_ofResumption _ _

/-- An explicit tau is invisible to weak behavior, but still consumes execution fuel. -/
theorem edit_tree_weakBisim :
    ITree.WeakBisim (ITree.step (Preview.form demoNotebook).run.toResumption.toITree)
      (Preview.form demoNotebook).run.toResumption.toITree :=
  ITree.step_weakBisim _

/-- The ongoing representation retains its result after completion, without console effects. -/
theorem editSystem_pure (result : EditResult) :
    editSystem.toFunA (.pure result) = .inr PUnit.unit ∧
      editSystem.toFunB (.pure result) PUnit.unit = .pure result := ⟨rfl, rfl⟩

private theorem form_bind_bound {α β : Type} (first : Form α) (next : α → Form β)
    {a b : Nat} (hfirst : first.run.IsTotalRollBound a)
    (hnext : ∀ value, (next value).run.IsTotalRollBound b) :
    (first >>= next).run.IsTotalRollBound (a + b) := by
  apply FreeM.isTotalRollBound_bind hfirst
  intro result
  cases result with
  | error error => exact FreeM.isTotalRollBound_pure _ _
  | ok value => exact hnext value

private theorem text_bound (prompt : String) : (Form.text prompt).run.IsTotalRollBound 1 := by
  change (FreeM.liftBind (P := Console) (.readLine prompt) _).IsTotalRollBound 1
  refine ⟨by change 0 < 1; decide, fun answer ↦ ?_⟩
  cases answer <;> trivial

private theorem natural_bound (prompt : String) : (Form.natural prompt).run.IsTotalRollBound 1 := by
  apply form_bind_bound (a := 1) (b := 0) _ _ (text_bound prompt)
  intro value
  dsimp only
  cases value.trimAscii.toString.toNat? <;> exact FreeM.isTotalRollBound_pure _ _

private theorem prepare_bound (notes : Notebook) :
    (Preview.prepare notes).run.IsTotalRollBound 3 := by
  apply form_bind_bound (a := 1) (b := 2) _ _ (natural_bound _)
  intro id
  apply form_bind_bound (a := 1) (b := 1) _ _ (natural_bound _)
  intro version
  apply form_bind_bound (a := 1) (b := 0) _ _ (text_bound _)
  intro text
  dsimp only
  cases step notes (.edit id version text) with
  | error error => exact FreeM.isTotalRollBound_pure _ _
  | ok next =>
    cases notes[id]? <;> exact FreeM.isTotalRollBound_pure _ _

private theorem confirm_bound (proposal : Preview.Proposal) :
    (Preview.confirm proposal).run.IsTotalRollBound 2 := by
  change (FreeM.liftBind (P := Console) (.write _) _).IsTotalRollBound 2
  refine ⟨by change 0 < 2; decide, fun _ ↦ ?_⟩
  change (FreeM.liftBind (P := Console) Preview.decision _).IsTotalRollBound 1
  refine ⟨by change 0 < 1; decide, fun answer ↦ ?_⟩
  change (ExceptT.run (match answer.map (·.trimAscii.toString) with
    | some "save" => (pure (some proposal.command) : Form (Option Command))
    | some "cancel" => pure none
    | none => throw InputError.endOfInput
    | _ => throw (.invalid "Choose save or cancel; no command submitted."))).IsTotalRollBound 0
  split <;> exact FreeM.isTotalRollBound_pure _ _

/-- Every branch of the real preview dialogue uses at most five console operations.
Validation failures and EOF may stop sooner; this is independent of a scripted input. -/
theorem edit_query_bound (notes : Notebook) :
    (Preview.form notes).run.IsTotalRollBound editQueryBudget :=
  form_bind_bound _ _ (prepare_bound notes) confirm_bound

end Notes.Walkthrough
