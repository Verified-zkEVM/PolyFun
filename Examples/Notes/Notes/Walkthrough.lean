/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunIO.Console
public import Notes.Preview
public import PolyFun.ITree.Execution
public import PolyFun.IPFunctor.Free.Basic
public import PolyFun.PFunctor.Dynamical.Game
public import PolyFun.PFunctor.Free.Cursor.Occurrence

/-! # Six executable representations, one small input task

The programs ask for text or prepare a note edit using an arbitrary console handler.
`Notes.Runtime` runs them with real streams; memory handlers make their behavior inspectable.
The indexed version tracks whether the prompt has happened; the dynamical system keeps a list;
the returning machine and the two coinductive representations retain their own native semantics.
-/

@[expose] public section

namespace Notes.Walkthrough

open PolyFunIO PFunctor PFunctor.DynSystem

/-- The representations offered by the CLI; parsing is confined to its outer boundary. -/
inductive Model where
  | free | indexed | system | machine | resumption | tree
  deriving DecidableEq, Repr

/-- Stable command-line spellings for each representation. -/
def Model.name : Model → String
  | .free => "free"
  | .indexed => "indexed"
  | .system => "system"
  | .machine => "machine"
  | .resumption => "resumption"
  | .tree => "tree"

/-- Every representation, in the introductory reading order. -/
def Model.all : List Model := [.free, .indexed, .system, .machine, .resumption, .tree]

/-- Reject unknown CLI spellings before interpreting any effects. -/
def Model.parse (name : String) : Except String Model :=
  match Model.all.find? (fun model ↦ model.name == name) with
  | some model => .ok model
  | none => .error "Choose free, indexed, system, machine, resumption, or tree."

/-- Three field reads, one preview write, and one decision read; errors can finish earlier. -/
def editQueryBudget : Nat := 5

/-- A single note prompt as a well-founded free program. -/
def ask : FreeM Console (Option String) := FreeM.lift (P := Console) (.readLine "Note: ")

/-- The index distinguishes a fresh request from its completed phase. -/
def Capture : IPFunctor.Endo Bool where
  A _ := Unit
  B _ _ := Option String
  src _ _ _ := true

/-- Indexed free syntax cannot silently forget its post-input state. -/
def indexed : IPFunctor.FreeM Capture false (Option String) :=
  .liftBind false () fun answer ↦ .pure true answer

/-- Erasure keeps the source index in the signature; this handler ignores only that tag. -/
def indexedHandler {m : Type → Type} (handler : Handler m Console) :
    Handler m Capture.sigmaPFunctor := fun _ ↦ handler (.readLine "Note: ")

/-- A nonreturning recorder: one input per step, with EOF leaving the log unchanged. -/
def recorder : DynSystem (List String) Console :=
  (fun _ ↦ ConsoleOp.readLine "Note: ") ⇆
    fun notes answer ↦ notes ++ answer.toList

/-- The returning dynamical realization supplied by the library. -/
def machine : DynComputation Console Unit (Option String) := .ofFreeM (fun _ ↦ ask)

/-- Coinductive, tau-free behavior obtained by the standard free-to-resumption map. -/
def resumed : Resumption Console (Option String) := ask.toResumption

/-- A tree with a genuine silent step before asking; tau does not read a line. -/
def tree : ITree Console (Option String) :=
  ITree.step (ITree.query (.readLine "Note: ") ITree.pure)

/-- Select a representation without introducing a second interpreter for its constructors. -/
def run {m : Type → Type} [Monad m] (model : Model) (handler : Handler m Console) :
    m (Except String (Option String)) := do
  match model with
  | .free => return .ok (← ask.liftM handler)
  | .indexed =>
    return .ok (← (indexed.toSigmaFreeM Capture).liftM (indexedHandler handler))
  | .system =>
    let notes ← DynSystem.kleisliIterate handler recorder 1 []
    return .ok notes.head?
  | .machine =>
    match ← machine.runChunk handler 1 ask with
    | .done result => return .ok result
    | .paused _ => return .error "Unexpected pause in the one-request machine."
  | .resumption =>
    let machine := DynComputation.ofResumption (fun (_ : Unit) ↦ resumed)
    match ← machine.runChunk handler 1 resumed with
    | .done result => return .ok result
    | .paused _ => return .error "Unexpected pause in the one-request resumption."
  | .tree =>
    match ← ITree.machine.startChunk (ITree.withSilentSteps handler) 2 tree with
    | .done result => return .ok result
    | .paused _ => return .error "Unexpected pause after tau and one request."

/-- A finite branch experiment. The first answer is shared, while the second answer is varied.
This forks in memory; it does not roll back a filesystem or undo an external effect. -/
def branchProgram : FreeM Console (String × String) := do
  let first ← FreeM.lift (P := Console) (.readLine "Original: ")
  let second ← FreeM.lift (P := Console) (.readLine "Edit: ")
  return (first.getD "", second.getD "")

/-- Retain a shared typed cursor and run two completions at the edit occurrence. -/
def branch := FreeM.Cursor.forkAt (ConsoleOp.readLine "Edit: ") branchProgram 0

/-! ## A complete edit dialogue

The indexed representation distinguishes collecting fields from confirming a validated proposal.
The ongoing system stutters silently after completion. Machines and resumptions return; the tree
adds an explicit tau. Compare visible effects and results, not these different notions of fuel.
-/

/-- The demo never opens a directory: its single note is fixed in memory. -/
def demoNotebook : Notebook := [⟨"First local note", []⟩]

/-- Preparation errors, cancellation, or an ordinary command ready for revalidation. -/
abbrev EditResult := Except InputError (Option Command)

/-- Collect fields, then confirm only a successfully validated proposal. -/
inductive EditPhase where
  | collect
  | confirm (proposal : Preview.Proposal)
  | done

/-- Available operations depend on the phase; a completed dialogue has no further operation.
The family computes in response and continuation types, including across ordinary imports. -/
@[implicit_reducible] def EditProtocol : IPFunctor.Endo EditPhase where
  A
    | .collect | .confirm _ => Unit
    | .done => Empty
  B
    | .collect, _ => Except InputError Preview.Proposal
    | .confirm _, _ => EditResult
    | .done, impossible => nomatch impossible
  src
    | .collect, _, .ok proposal => .confirm proposal
    | .collect, _, .error _ => .done
    | .confirm _, _, _ => .done
    | .done, impossible, _ => nomatch impossible

/-- The response-dependent index retains the exact proposal selected during preparation. -/
def indexedEdit : IPFunctor.FreeM EditProtocol .collect EditResult :=
  .liftBind EditPhase.collect () fun result => match result with
    | .error error => .pure EditPhase.done (Except.error error)
    | .ok proposal =>
      .liftBind (EditPhase.confirm proposal) () fun answer => .pure EditPhase.done answer

/-- Interpret indexed operations through the same console-only forms as the free program. -/
def editProtocolHandler {m : Type → Type} [Monad m] (handler : Handler m Console) :
    Handler m EditProtocol.sigmaPFunctor
  | ⟨.collect, _⟩ => (Preview.prepare demoNotebook).interpret handler
  | ⟨.confirm proposal, _⟩ => (Preview.confirm proposal).interpret handler
  | ⟨.done, impossible⟩ => nomatch impossible

/-- An ongoing system over residual syntax. Completion becomes a silent stuttering state. -/
def editSystem : DynSystem (FreeM Console EditResult) (Console + PFunctor.y) where
  toFunA
    | .pure _ => .inr PUnit.unit
    | .liftBind operation _ => .inl operation
  toFunB program := match program with
    | .pure value => fun _ => .pure value
    | .liftBind _ next => next

/-- Run the full read-only edit workflow in each representation. Chunk sizes are explicit
observations, not a universal bound for arbitrary console programs. -/
def runEdit {m : Type → Type} [Monad m] (model : Model) (handler : Handler m Console) :
    m (Except String EditResult) := do
  let program := (Preview.form demoNotebook).run
  match model with
  | .free => return .ok (← program.liftM handler)
  | .indexed =>
    return .ok (← (indexedEdit.toSigmaFreeM EditProtocol).liftM (editProtocolHandler handler))
  | .system =>
    let residual ← DynSystem.kleisliIterate (ITree.withSilentSteps handler)
      editSystem editQueryBudget program
    match residual with
    | .pure result => return .ok result
    | .liftBind .. => return .error "Edit system is still waiting for an operation."
  | .machine =>
    let machine : DynComputation Console Unit EditResult := .ofFreeM (fun _ => program)
    let first ← machine.startChunk handler 2 ()
    match ← machine.continueChunk handler (editQueryBudget - 2) first with
    | .done result => return .ok result
    | .paused _ => return .error "Edit machine paused."
  | .resumption =>
    let machine := DynComputation.ofResumption (fun (_ : Unit) => program.toResumption)
    match ← machine.startChunk handler editQueryBudget () with
    | .done result => return .ok result
    | .paused _ => return .error "Edit resumption paused."
  | .tree =>
    let tree := ITree.step program.toResumption.toITree
    match ← ITree.machine.startChunk (ITree.withSilentSteps handler) (editQueryBudget + 1) tree with
    | .done result => return .ok result
    | .paused _ => return .error "Edit tree paused."

end Notes.Walkthrough
