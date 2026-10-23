/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Examples.Tutorials.Requests
import Examples.Tutorials.Machines
import Examples.Tutorials.IndexedPrograms
import Examples.Tutorials.InteractionTrees
import Examples.Tutorials.ParallelReports
import Examples.Tutorials.VersionedRequests
import Examples.Tutorials.UpdatePolicies
import PolyFun.PFunctor.Handler.Sum
import Examples.Tutorials.ScopedPrograms
import Examples.Tutorials.ScopedExecution
import Examples.Tutorials.ScopedFamily
import Examples.Tutorials.ScopedDomains
import PolyFun.IPFunctor.Scoped.DomainRelation
import PolyFun.Interaction.Interface
import PolyFun.Interaction.Execution.ReactiveProcess
import PolyFun.Interaction.Execution.RequestNetwork
import PolyFun.Interaction.Open.OpenSyntax.Expr
import PolyFun.Interaction.Open.Emulates

/-!
# Documentation examples as a separate package

Ordinary imports expose the teaching programs and the interface, execution, and open-system
APIs. These checks consume public equations and constructor contracts across a package boundary.
-/

open PolyFunExamples
open Interaction

example : Requests.twoRequests.liftM Requests.increment = (4, 5) := rfl

example : Requests.twoRequests.liftM Requests.double = (6, 12) :=
  Requests.twoRequests_double

example (initial : Nat) (xs ys : List Nat) :
    Machines.counter.run initial (xs ++ ys) =
      Machines.counter.run (Machines.counter.run initial xs) ys :=
  Machines.counter_run_append initial xs ys

example : IPFunctor.FreeM₂ PolyFunExamples.IndexedPrograms.proto
    PolyFunExamples.IndexedPrograms.Phase.opn PolyFunExamples.IndexedPrograms.Phase.counting Nat :=
  PolyFunExamples.IndexedPrograms.TwoIndex.run

example :
    (ITree.interp InteractionTrees.refuse InteractionTrees.bump).run =
      ITree.query (F := ITree.StateE Nat) .get fun _ => ITree.step (ITree.pure none) :=
  InteractionTrees.run_interp_refuse_bump

example (I : Interface) : Type := Interface.Packet I

example (effect : PFunctor.{0, 0}) (boundary : PortBoundary) :
    (Execution.ReactiveProcess.signature effect boundary).A := .tick

example : Execution.RequestNetwork.Activation Unit := .deliver

-- An ordinary import across a Lake package boundary: the coproduct injection law needs only
-- `Monad`.
example {P Q : PFunctor.{0, 0}} {m : Type → Type} [Monad m]
    (left : PFunctor.Handler m P) (right : PFunctor.Handler m Q)
    (program : PFunctor.FreeM P Nat) :
    (program.mapLens PFunctor.Lens.inl).liftM (PFunctor.Handler.sum left right) =
      program.liftM left := PFunctor.Handler.liftM_sum_mapLens_inl left right program

example : UpdatePolicies.checked 10 |>.wpFold (PFunctor.OpSpec.demonic _) (· ≤ 10) :=
  UpdatePolicies.checked_safe 10

example : VersionedRequests.finished.service = ⟨1, "first"⟩ := rfl

/-- error: Type mismatch
  true
has type
  Bool
but is expected to have type
  VersionedRequests.Store.B VersionedRequests.Request.read -/
#guard_msgs in
example : VersionedRequests.Store.B .read := true

example (T : Open.OpenTheory) (Δ : PortBoundary) (system : T.Obj Δ) :
    Open.Emulates system system (Open.Observation.eq T) :=
  Open.Emulates.refl _ _

example : Examples.ScopedPrograms.captureExample.denote Examples.ScopedPrograms.algebra
    IPFunctor.ScopedSignature.Env.empty 3 = 10 := rfl

example (n : Nat) : Examples.ScopedPrograms.FirstOrder.sumCertificate.meaning n =
    (Examples.ScopedPrograms.sumTo n).denote Examples.ScopedPrograms.algebra
      IPFunctor.ScopedSignature.Env.empty :=
  Examples.ScopedPrograms.FirstOrder.sumCertificate.correct n

example {S R : Type} (step : Control.Transition S R) (fuel : Nat) (state : S) :
    (Control.Transition.toMachine step).runChunk Control.Transition.tickHandler fuel
      (.inr state) = Control.Transition.toChunk (Control.Transition.run step fuel state) :=
  Control.Transition.runChunk_toMachine step fuel state

example {n m : Nat} (ρ : Fin n → Fin m)
    {Γ : List (Examples.ScopedFamily.ValueSort n)} {s : Examples.ScopedFamily.ValueSort n}
    (t : Examples.ScopedFamily.Term n Γ s) :
    Examples.ScopedFamily.erase (t.map Examples.ScopedFamily.parameterHom ρ) =
      Examples.ScopedFamily.erase t := Examples.ScopedFamily.erase_parameters ρ t

example {n m : Nat} (μ : Fin n → Fin m)
    {Γ Δ : List (Examples.ScopedFamily.ValueSort n)} {s : Examples.ScopedFamily.ValueSort n}
    (ρ : IPFunctor.ScopedSignature.Renaming Γ Δ) (t : Examples.ScopedFamily.Term n Γ s) :
    (t.rename ρ).map Examples.ScopedFamily.parameterHom μ =
      (t.map Examples.ScopedFamily.parameterHom μ).rename
        (IPFunctor.ScopedSignature.Renaming.map (Examples.ScopedFamily.ValueSort.rename μ) ρ) :=
  Examples.ScopedFamily.parameters_rename μ ρ t

/-- A separate package can recover transported environments from positional correspondence. -/
example {S T : Type*} {D : S → PointedDomain} {E : T → PointedDomain}
    {Γ : List S} (f : S → T) (hf : ∀ a, E (f a) = D a)
    (η : IPFunctor.ScopedDomain.Env D Γ) (ζ : IPFunctor.ScopedDomain.Env E (Γ.map f))
    (h : IPFunctor.ScopedDomain.Env.Pointwise η ζ) :
    IPFunctor.ScopedDomain.Env.reindex D E f hf η = ζ :=
  IPFunctor.ScopedDomain.Env.pointwise_reindex_eq hf h
