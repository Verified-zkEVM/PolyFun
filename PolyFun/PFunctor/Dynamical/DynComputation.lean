/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Trajectory
public import PolyFun.PFunctor.Resumption

/-!
# Returning dynamical computations

A `DynComputation p α β` is a hidden-state realization of an `α`-indexed
family of `Resumption p β` computations. Its underlying `Machine` runs over
the return-or-query polynomial `C β + p`: a state either returns a value and
has no directions, or exposes a visible `p`-query whose direction selects the
next state.

Unlike a partial readout stored separately from the dynamics, this
representation carries no unreachable `p`-interaction data at returned
states. In particular, `DynComputation.ofFn` and the `Pure` instance are
available for every interface and do not require a chosen `Point p`.
-/

@[expose] public section

universe u uA uB uα uβ

namespace PFunctor

namespace DynSystem

/-- A stateful realization of a returning computation over `p`. Its dynamics
are uniformly available as `.toDynSystem`, while `init` selects the
initial state for each input. -/
structure DynComputation (p : PFunctor.{uA, uB}) (α : Type uα) (β : Type uβ)
    extends Machine.{u, max uβ uA, uB} (C.{uβ, uB} β + p) where
  /-- Where the computation starts, given an input. -/
  init : α → State

namespace DynComputation

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-- The computational one-step view of a state: either a returned value or a
visible query paired with its state-valued continuation. -/
def view (M : DynComputation.{u} p α β) (state : M.State) : β ⊕ p.Obj M.State :=
  Resumption.unpack (M.toDynSystem.out state)

/-- The canonical state-free semantics of a dynamical computation. -/
def denote (M : DynComputation.{u} p α β) (input : α) : Resumption p β :=
  M.toDynSystem.behavior (M.init input)

/-- An immediately returning computation determined by its input. No point of
`p` is needed because a return is represented by a directionless position of
`C β`. -/
def ofFn (f : α → β) : DynComputation.{uβ} p α β where
  State := β
  toDynSystem := Sum.inl ⇆ fun _ => PEmpty.elim
  init := f

@[simp] theorem ofFn_State (f : α → β) : (ofFn (p := p) f).State = β := rfl

@[simp] theorem ofFn_init (f : α → β) (input : α) :
    (ofFn (p := p) f).init input = f input := rfl

@[simp] theorem view_ofFn (f : α → β) (value : β) :
    (ofFn (p := p) f).view value = Sum.inl value := rfl

@[simp] theorem view_init_ofFn (f : α → β) (input : α) :
    (ofFn (p := p) f).view ((ofFn (p := p) f).init input) = Sum.inl (f input) := rfl

@[simp] theorem denote_ofFn (f : α → β) (input : α) :
    (ofFn (p := p) f).denote input = Resumption.pure (f input) := by
  apply M.eq_of_dest_eq
  unfold denote Resumption.pure ofFn
  rw [DynSystem.dest_behavior, M.dest_mk]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext direction
    exact PEmpty.elim direction

/-- The `Pure` operation is the input-independent specialization of `ofFn`. -/
instance : Pure (DynComputation.{uβ} p α) where
  pure value := ofFn fun _ => value

theorem pure_eq_ofFn (value : β) :
    (pure value : DynComputation.{uβ} p α β) = ofFn (fun _ => value) := rfl

@[simp] theorem pure_State (value : β) :
    (pure value : DynComputation.{uβ} p α β).State = β := rfl

@[simp] theorem pure_init (value : β) (input : α) :
    (pure value : DynComputation.{uβ} p α β).init input = value := rfl

@[simp] theorem view_pure (value state : β) :
    (pure value : DynComputation.{uβ} p α β).view state = Sum.inl state := rfl

@[simp] theorem view_init_pure (value : β) (input : α) :
    (pure value : DynComputation.{uβ} p α β).view
      ((pure value : DynComputation.{uβ} p α β).init input) = Sum.inl value := rfl

@[simp] theorem denote_pure (value : β) (input : α) :
    (pure value : DynComputation.{uβ} p α β).denote input = Resumption.pure value := by
  change (ofFn (p := p) (fun _ : α => value)).denote input = Resumption.pure value
  exact denote_ofFn (fun _ : α => value) input

/-- The denotation exposes exactly the computational view at the initialized
state, recursively denoting every query continuation. -/
@[simp] theorem dest_denote (M : DynComputation.{u} p α β) (input : α) :
    Resumption.dest (M.denote input) =
      Sum.map (fun value : β => value) (p.map M.toDynSystem.behavior)
        (M.view (M.init input)) := by
  unfold denote Resumption.dest view
  rw [DynSystem.dest_behavior]
  change Resumption.unpack
      ((C.{uβ, uB} β + p).map M.toDynSystem.behavior
        (M.toDynSystem.out (M.init input))) = _
  exact Resumption.unpack_map _ _

/-! ## Resumption realizations -/

/-- Realize a family of resumptions directly, using the resumption itself as
the hidden state. This is the canonical (generally infinite-state) realization
of state-free resumption semantics. -/
def ofResumption (semantics : α → Resumption p β) : DynComputation p α β where
  State := Resumption p β
  toDynSystem := (fun state => (M.dest state).1) ⇆ fun state => (M.dest state).2
  init := semantics

@[simp] theorem ofResumption_State (semantics : α → Resumption p β) :
    (ofResumption semantics).State = Resumption p β := rfl

@[simp] theorem ofResumption_init (semantics : α → Resumption p β) (input : α) :
    (ofResumption semantics).init input = semantics input := rfl

@[simp] theorem view_ofResumption (semantics : α → Resumption p β)
    (state : Resumption p β) :
    (ofResumption semantics).view state = Resumption.dest state := by
  unfold view ofResumption Resumption.dest
  rfl

@[simp] theorem denote_ofResumption (semantics : α → Resumption p β) (input : α) :
    (ofResumption semantics).denote input = semantics input := by
  unfold denote ofResumption
  exact M.corec_dest _

end DynComputation

end DynSystem

end PFunctor
