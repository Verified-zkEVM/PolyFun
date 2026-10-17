/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Pipeline.Model
public import PolyFun.Interaction.Execution.ReactiveNetwork.HandledAssembly
public import PolyFun.Interaction.Execution.ReactiveNetwork.Budget

/-! # A collector composed with a loader and an analyser

The collector requests one file at a time, passes the returned bytes to the analyser, and
retains reports in input order. Workers are persistent machines; the collector is a finite
free program. `par` and `plug` supply every route. Token execution is cooperative, not threaded.
Read errors travel through the same typed messages as successful reads.
-/

@[expose] public section

namespace Pipeline

open PFunctor DynSystem Interaction Interaction.Execution
open ReactiveProcess ReactiveNetwork

/-- One packet label carrying a value of the indicated type. -/
def packet (α : Type) : Interface := ⟨Unit, fun _ ↦ α⟩

/-- Loader requests are paths; replies retain both the path and its read outcome. -/
def loaderBoundary : PortBoundary := ⟨packet String, packet Loaded⟩

/-- Analysis accepts loaded bytes and returns one report entry. -/
def analyserBoundary : PortBoundary := ⟨packet Loaded, packet Entry⟩

/-- The collector sees the two distinct service ports, with their directions reversed. -/
def collectorBoundary : PortBoundary :=
  (PortBoundary.tensor loaderBoundary analyserBoundary).swap

/-- No external effect is available to either the collector or the analyser. -/
abbrev NoEffect := Assembly.relayEffect

/-- Loader phases retain an actual read result until its send is performed. -/
inductive LoaderState where
  | waiting
  | reading (path : String)
  | sending (input : Loaded)

/-- Read exactly once per request; a later activation sends the retained outcome. -/
def loader : Process Files loaderBoundary Unit (List Entry) :=
  DynComputation.ofStep (S := LoaderState) (fun
    | .waiting => .inr ⟨.receive, fun request ↦ .reading request.2⟩
    | .reading path => .inr ⟨.effect path, fun result ↦ .sending (path, result)⟩
    | .sending input => .inr ⟨.send ⟨(), input⟩, fun _ ↦ .waiting⟩) (fun _ ↦ .waiting)

/-- Analysis has no IO capability; it retains the entry until the send activation. -/
def analyser : Process NoEffect analyserBoundary Unit (List Entry) :=
  DynComputation.ofStep (S := Option Entry) (fun
    | none => .inr ⟨.receive, fun input ↦ some (analyse input.2)⟩
    | some entry => .inr ⟨.send ⟨(), entry⟩, fun _ ↦ none⟩) (fun _ ↦ none)

/-- Typed requests and replies for each input occurrence. Unexpected service ports abort;
the composed workers always answer on their own declared port. -/
def collect : List String → List Entry →
    FreeM (signature NoEffect collectorBoundary) (Outcome (List Entry))
  | [], entries => .pure (.returned entries.reverse)
  | path :: paths, entries => .liftBind (.send ⟨.inl (), path⟩) fun _ ↦
    .liftBind .receive fun
      | ⟨.inl _, input⟩ => .liftBind (.send ⟨.inr (), input⟩) fun _ ↦
        .liftBind .receive fun
          | ⟨.inr _, entry⟩ => collect paths (entry :: entries)
          | ⟨.inl _, _⟩ => .pure .aborted
      | ⟨.inr _, _⟩ => .pure .aborted

/-- Compose real components with their handlers; no application-written routing function. -/
def assembly {m : Type → Type} (read : Handler m Files) (paths : List String) :
    HandledAssembly m PortBoundary.empty (List Entry) :=
  ((HandledAssembly.atom loader read).par
    (HandledAssembly.atom analyser fun operation ↦ operation.elim)).plug
      (HandledAssembly.atom (DynComputation.ofFreeM fun _ ↦ collect paths [])
        fun operation ↦ operation.elim)

/-- The collector is the selected environment of the closed assembly. -/
def collectorId {m : Type → Type} (read : Handler m Files) (paths : List String) :
    (assembly read paths).Node := .inr ()

/-- One file requires four collector operations, three loader operations, and two analyser
operations. The initial empty report is already terminal and costs no activation. -/
def activationBudget (paths : List String) : Nat := 9 * paths.length

/-- Execute a finite prefix and retain the exact residual network, including partial work. -/
def run {m : Type → Type} [Monad m] (read : Handler m Files) (paths : List String)
    (fuel : Nat) :=
  (assembly read paths).diagram.runToken (collectorId read paths) fuel
    ((assembly read paths).diagram.initial (collectorId read paths))

/-- Consume a list of chunk budgets without reinitializing the network between chunks. -/
def runChunks {m : Type → Type} [Monad m] (read : Handler m Files) (paths : List String)
    (chunks : List Nat) :=
  chunks.foldlM (fun state fuel ↦
    (assembly read paths).diagram.runToken (collectorId read paths) fuel state)
    ((assembly read paths).diagram.initial (collectorId read paths))

/-- A resumed run preserves the entire computation, including reads already performed. -/
theorem run_add {m : Type → Type} [Monad m] [LawfulMonad m]
    (read : Handler m Files) (paths : List String) (first rest : Nat) :
    run read paths (first + rest) =
      (run read paths first >>= (assembly read paths).diagram.runToken
        (collectorId read paths) rest) :=
  HandledDiagram.runToken_add _ _ _ _ _

end Pipeline
