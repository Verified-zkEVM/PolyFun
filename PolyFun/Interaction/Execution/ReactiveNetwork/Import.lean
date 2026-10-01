/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork.Conserving
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Import-bounded ledgers

An `ImportBounded T` certificate is the ledger form of the runtime notion of universal
composability (`Can20`), where a machine's steps are bounded by a function of its net import. Each
node keeps, as functions of its own local state:

* its net import `net`: credit consumed, minus credit attached to sent packets, plus any initial
  endowment;
* its steps so far, `steps`.

Activations update the ledger (`ledger`), and the steps never exceed `T` of the net import
(`bounded`). Unlike in a `Conserving` certificate, a received packet's worth in steps depends on the
receiver's balance, so this is not a fixed-rate potential.

* `ImportBounded.work_runTokenOpen_le`: if `T` is monotone and superadditive
  (`T a + T b ≤ T (a + b)`), then along any open token execution, work plus the ledgers' initial
  steps is at most `T` of the initial import and the funded ingress credit. The local bounds compose
  by superadditivity, not by telescoping.
* `ImportBounded.toConserving`: for `T = id`, the ledger is a conserving certificate with
  potential `net - steps`.
-/

public section

namespace Interaction.Execution.ReactiveNetwork

open PFunctor ReactiveProcess MonadAttach

variable {Node result S : Type} {boundary : PortBoundary}
  {network : Network Node boundary result} [DecidableEq Node]
  {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

/-- A superadditive function of a sum dominates the sum of its values. -/
theorem sum_le_of_superadditive {ι : Type} (s : Finset ι) (f : ι → ℕ) (T : ℕ → ℕ)
    (hsuper : ∀ a b, T a + T b ≤ T (a + b)) : ∑ i ∈ s, T (f i) ≤ T (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (Nat.add_le_add_left ih _) (hsuper _ _)

/-- **An import ledger.** Each node's net import and step count, as functions of its own local
state: activations move import with packets and record their charge, and steps never exceed `T`
of the net import. -/
structure ImportBounded (impl : (id : Node) → Handler (StateT S m) (network.effect id))
    (discipline : Discipline) (charge : Charge network S) (credit : CreditModel network)
    (invariant : State network S → Prop) (T : ℕ → ℕ) where
  /-- Net import: credit consumed minus credit attached, plus any initial endowment. -/
  net : (id : Node) → (network.component id).State → ℕ
  /-- Charged steps so far. -/
  steps : (id : Node) → (network.component id).State → ℕ
  /-- The runtime bound, in every local state. -/
  bounded : ∀ id s, steps id s ≤ T (net id s)
  /-- Activations move import with packets and record their charge. -/
  ledger : ∀ id state next, invariant state → Schedulable discipline id state →
    CanReturn (activate impl discipline id state) next →
      net id (next.localState id) + credit.emitted id state ≤
          net id (state.localState id) + credit.consumed id state ∧
        steps id (state.localState id) + charge (.node id) state ≤
          steps id (next.localState id)

namespace ImportBounded

variable {impl : (id : Node) → Handler (StateT S m) (network.effect id)}
  {discipline : Discipline} {charge : Charge network S} {credit : CreditModel network}
  {invariant : State network S → Prop} {T : ℕ → ℕ} [Fintype Node]

/-- Import held by the network: node ledgers plus credit held by packets. -/
@[expose] def imported (c : ImportBounded impl discipline charge credit invariant T)
    (state : State network S) : ℕ :=
  (∑ id, c.net id (state.localState id)) + credit.held state

/-- The ledgers' total step count. -/
@[expose] def stepsTotal (c : ImportBounded impl discipline charge credit invariant T)
    (state : State network S) : ℕ :=
  ∑ id, c.steps id (state.localState id)

/-- An activation never raises the network's import. -/
theorem imported_activate (c : ImportBounded impl discipline charge credit invariant T)
    {id : Node} {state next : State network S} (hinv : invariant state)
    (hsched : Schedulable discipline id state)
    (h : CanReturn (activate impl discipline id state) next) :
    c.imported next ≤ c.imported state := by
  have hstep := (c.ledger id state next hinv hsched h).1
  have hheld := credit.held_activate impl discipline id state next h
  have hframe := sum_frame (fun i s => c.net i s) state.localState next.localState id
    (fun i hi => localState_activate_of_ne impl discipline id i state next h hi)
  simp only [imported]
  omega

/-- An activation records its charge in the total step count. -/
theorem stepsTotal_activate (c : ImportBounded impl discipline charge credit invariant T)
    {id : Node} {state next : State network S} (hinv : invariant state)
    (hsched : Schedulable discipline id state)
    (h : CanReturn (activate impl discipline id state) next) :
    c.stepsTotal state + charge (.node id) state ≤ c.stepsTotal next := by
  have hstep := (c.ledger id state next hinv hsched h).2
  have hframe := sum_frame (fun i s => c.steps i s) state.localState next.localState id
    (fun i hi => localState_activate_of_ne impl discipline id i state next h hi)
  simp only [stepsTotal]
  omega

omit [LawfulMonad m] [ExactMonadAttach m] in
/-- An external input raises the network's import by exactly the credit it is funded with. -/
theorem imported_input (c : ImportBounded impl discipline charge credit invariant T)
    (packet : Interface.Packet boundary.In) (state : State network S) :
    c.imported (input packet state) = c.imported state + credit.ingress packet := by
  have hloc : (input packet state).localState = state.localState := by
    simp only [input, dispatch]
  simp only [imported, hloc, credit.held_input]
  omega

omit [LawfulMonad m] [ExactMonadAttach m] in
/-- Superadditivity composes the local runtime bounds. -/
theorem stepsTotal_le (c : ImportBounded impl discipline charge credit invariant T)
    (hsuper : ∀ a b, T a + T b ≤ T (a + b)) (hmono : Monotone T) (state : State network S) :
    c.stepsTotal state ≤ T (c.imported state) := by
  calc c.stepsTotal state ≤ ∑ id, T (c.net id (state.localState id)) :=
        Finset.sum_le_sum fun id _ => c.bounded id _
    _ ≤ T (∑ id, c.net id (state.localState id)) :=
        sum_le_of_superadditive _ _ T hsuper
    _ ≤ T (c.imported state) := hmono (Nat.le_add_right _ _)

/-- **Composition of import-bounded nodes.** With a monotone superadditive `T`, the work of any
open token execution plus the ledgers' initial steps is at most `T` of the initial import plus
the funded ingress credit. -/
theorem work_runTokenOpen_le (c : ImportBounded impl .token charge credit invariant T)
    (hsuper : ∀ a b, T a + T b ≤ T (a + b)) (hmono : Monotone T)
    (preserves : TokenInvariant impl invariant)
    (preserves_input : ∀ packet state, invariant state → invariant (input packet state))
    {events : List (TokenEvent boundary)} {state next : State network S} {work : ℕ}
    (hinv : invariant state)
    (h : CanReturn (runTokenOpen impl charge events state) (next, work)) :
    work + c.stepsTotal state ≤ T (c.imported state + (events.map credit.funded).sum) := by
  have hwork := (chargedRun_ledger invariant c.stepsTotal
    (fun event s s' hs hstep => by
      cases event with
      | input packet =>
        have heq : s' = input packet s := canReturn_pure_iff.mp hstep
        subst heq
        refine ⟨preserves_input packet s hs, ?_⟩
        have hloc : (input packet s).localState = s.localState := by
          simp only [input, dispatch]
        simp [tokenEventCharge, stepsTotal, hloc]
      | step =>
        exact ⟨preserves s s' hs hstep, c.stepsTotal_activate hs rfl hstep⟩)
    _ state next work hinv h).2
  have himport := (chargedRun_bounded invariant c.imported credit.funded
    (fun event s s' hs hstep => by
      cases event with
      | input packet =>
        have heq : s' = input packet s := canReturn_pure_iff.mp hstep
        subst heq
        exact ⟨preserves_input packet s hs, by simp [CreditModel.funded, c.imported_input]⟩
      | step =>
        exact ⟨preserves s s' hs hstep, by
          simpa [CreditModel.funded] using c.imported_activate hs rfl hstep⟩)
    _ state next work hinv h).2
  calc work + c.stepsTotal state ≤ c.stepsTotal next := hwork
    _ ≤ T (c.imported next) := c.stepsTotal_le hsuper hmono next
    _ ≤ T (c.imported state + (events.map credit.funded).sum) := hmono himport

omit [Fintype Node] in
/-- **Linear budgets are conservation.** For `T = id`, the ledger is a conserving certificate
with potential `net - steps`. -/
@[expose] def toConserving (c : ImportBounded impl discipline charge credit invariant id) :
    Conserving impl discipline charge credit invariant where
  pot id s := c.net id s - c.steps id s
  step id state next hinv hsched h := by
    obtain ⟨hnet, hsteps⟩ := c.ledger id state next hinv hsched h
    have hb := c.bounded id (state.localState id)
    have hb' := c.bounded id (next.localState id)
    simp only [_root_.id] at hb hb'
    omega

end ImportBounded

end Interaction.Execution.ReactiveNetwork
