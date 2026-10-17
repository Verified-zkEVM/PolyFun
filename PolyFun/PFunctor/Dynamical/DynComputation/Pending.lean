/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Dynamical.DynComputation

/-!
# Suspended machine queries

A `Pending` query stores a machine state and proof that it exposes the selected
operation. Resumption recomputes the continuation from that state. The stored
data contains no function-valued continuation, so representation and cost
certificates can use the machine's state representation directly.
-/

public section

universe u uA uB uα uβ

namespace PFunctor.DynSystem.DynComputation

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-- A retained state that exposes a particular dependent operation. -/
structure Pending (machine : DynComputation.{u} p α β) (position : p.A) where
  /-- The suspended caller state. -/
  val : machine.State
  /-- The state exposes this operation. -/
  property : ∃ next, machine.view val = .inr ⟨position, next⟩

namespace Pending

variable {machine : DynComputation.{u} p α β} {position : p.A}

/-- Retain a state whose computational view is a query. -/
@[expose] def ofView {state : machine.State} {next : p.B position → machine.State}
    (h : machine.view state = .inr ⟨position, next⟩) : Pending machine position :=
  ⟨state, next, h⟩

/-- Recompute the selected continuation and feed it the typed answer. -/
@[expose] def resume (pending : Pending machine position) (answer : p.B position) :
    machine.State :=
  match h : machine.view pending.val with
  | .inl _ => False.elim (by
      obtain ⟨next, hn⟩ := pending.property
      rw [h] at hn
      cases hn)
  | .inr ⟨operation, next⟩ => next (cast (congrArg p.B (by
      obtain ⟨rest, hr⟩ := pending.property
      exact (congrArg PFunctor.Obj.fst (Sum.inr.inj (h.symm.trans hr))).symm)) answer)

/-- Resuming a known query is exactly its machine transition. -/
@[simp] theorem resume_ofView {state : machine.State} {next : p.B position → machine.State}
    (h : machine.view state = .inr ⟨position, next⟩) (answer : p.B position) :
    (ofView h).resume answer = next answer := by
  simp only [resume, ofView]
  split
  · rename_i value hv
    have heq := hv.symm.trans h
    cases heq
  · rename_i operation rest hr
    have heq := Sum.inr.inj (hr.symm.trans h)
    cases heq
    rfl

/-- Every pending query can be described by its actual computational continuation. -/
theorem exists_view (pending : Pending machine position) :
    ∃ next, machine.view pending.val = .inr ⟨position, next⟩ := pending.property

end Pending
end PFunctor.DynSystem.DynComputation
