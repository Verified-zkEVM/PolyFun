/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.Execution.ReactiveNetwork
public import PolyFun.Control.Monad.Support

/-!
# Global activation budgets for reactive execution

Each successful finite prefix retains its exact activation count, including blocked and
administrative steps. A global rank on invariant network states bounds the fuel after which
every successful token result has a terminal environment. Progress supplies at least one
successful result; it does not assert that all branches of an effect interpreter return.
Local reaction bounds alone do not provide such a rank in the presence of feedback.

These are activation bounds. Atomic handlers and the runtime's routing, queue, scheduling,
initialization, and output operations still require quantitative implementation witnesses.
-/

public section

namespace Interaction.Execution.ReactiveNetwork

open PFunctor ReactiveProcess MonadAttach

variable {Node result S : Type} {boundary : PortBoundary}
  {network : Network Node boundary result} [DecidableEq Node]
  {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

attribute [local implicit_reducible] signature Response

/-- Every successful activation consumes one unit, even when it performs no local transition. -/
theorem elapsed_activate
    (impl : (node : Node) → Handler (StateT S m) (network.effect node))
    (discipline : Discipline) (node : Node) (state next : State network S)
    (h : CanReturn (activate impl discipline node state) next) :
    next.elapsed = state.elapsed + 1 := by
  rcases hv : (network.component node).view (state.localState node) with value | ⟨action, cont⟩
  · simp only [activate, hv, canReturn_pure_iff] at h
    subst next
    rfl
  · cases action with
    | effect operation =>
      simp only [activate, hv, canReturn_bind_iff, canReturn_pure_iff] at h
      obtain ⟨answer, _, rfl⟩ := h
      rfl
    | receive =>
      cases hi : state.inbox node <;> simp [activate, hv, hi] at h <;> subst next <;> rfl
    | send packet =>
      cases discipline <;> cases hr : network.route node packet <;>
        simp [activate, hv, hr, dispatch] at h <;> subst next <;> rfl
    | tick => simp [activate, hv] at h; subst next; rfl
    | yield => simp [activate, hv] at h; subst next; rfl

/-- The complete token prefix retains exactly the number of consumed activations. -/
theorem elapsed_runToken
    (impl : (node : Node) → Handler (StateT S m) (network.effect node))
    (fuel : ℕ) (state next : State network S)
    (h : CanReturn (runToken impl fuel state) next) :
    next.elapsed = state.elapsed + fuel := by
  induction fuel generalizing state with
  | zero => simpa [runToken] using congrArg State.elapsed (canReturn_pure_iff.mp h)
  | succ fuel ih =>
    obtain ⟨mid, hstep, hrest⟩ := canReturn_bind_iff.mp h
    rw [ih mid hrest, elapsed_activate impl .token state.focus state mid hstep]
    omega

/-- A FIFO activation charges either one local action or one delivery action. -/
theorem elapsed_fifoStep
    (impl : (node : Node) → Handler (StateT S m) (network.effect node))
    (activation : Activation Node) (state next : State network S)
    (h : CanReturn (fifoStep impl activation state) next) :
    next.elapsed = state.elapsed + 1 := by
  cases activation with
  | node node => exact elapsed_activate impl .fifo node state next h
  | deliver =>
    have heq : next = deliver state := canReturn_pure_iff.mp h
    subst next
    cases hp : state.pending with
    | nil => simp [deliver, hp]
    | cons packet rest => cases packet <;> simp [deliver, hp, dispatch]

/-- The complete FIFO prefix retains its schedule length, including empty deliveries. -/
theorem elapsed_runFIFO
    (impl : (node : Node) → Handler (StateT S m) (network.effect node))
    (schedule : List (Activation Node)) (state next : State network S)
    (h : CanReturn (runFIFO impl schedule state) next) :
    next.elapsed = state.elapsed + schedule.length := by
  induction schedule generalizing state with
  | nil => simpa [runFIFO] using congrArg State.elapsed (canReturn_pure_iff.mp h)
  | cons activation rest ih =>
    obtain ⟨mid, hstep, hrest⟩ := canReturn_bind_iff.mp h
    rw [ih mid hrest, elapsed_fifoStep impl activation state mid hstep]
    simp only [List.length_cons]
    omega

/-- A terminal component stays terminal under every successful network activation. -/
theorem outcome_activate_of_some
    (impl : (node : Node) → Handler (StateT S m) (network.effect node))
    (discipline : Discipline) (node observer : Node) (state next : State network S)
    (value : Outcome result) (hout : outcome observer state = some value)
    (h : CanReturn (activate impl discipline node state) next) :
    outcome observer next = some value := by
  by_cases hn : node = observer
  · subst node
    unfold outcome at hout
    cases hv : (network.component observer).view (state.localState observer) with
    | inl result =>
      simp only [activate, hv, canReturn_pure_iff] at h
      subst next
      exact hout
    | inr action => simp [hv] at hout
  · rcases hv : (network.component node).view (state.localState node) with result | ⟨action, cont⟩
    · simp only [activate, hv, canReturn_pure_iff] at h
      subst next
      exact hout
    · cases action with
      | effect operation =>
        simp only [activate, hv, canReturn_bind_iff, canReturn_pure_iff] at h
        obtain ⟨answer, _, rfl⟩ := h
        simpa [outcome, Function.update, hn, Ne.symm hn] using hout
      | receive =>
        cases hi : state.inbox node <;> simp [activate, hv, hi] at h <;> subst next <;>
          simpa [outcome, Function.update, hn, Ne.symm hn] using hout
      | send packet =>
        cases discipline <;> cases hr : network.route node packet <;>
          simp [activate, hv, hr, dispatch] at h <;> subst next <;>
          simpa [outcome, Function.update, hn, Ne.symm hn] using hout
      | tick =>
        simp [activate, hv] at h
        subst next
        simpa [outcome, Function.update, hn, Ne.symm hn] using hout
      | yield =>
        simp [activate, hv] at h
        subst next
        simpa [outcome, Function.update, hn, Ne.symm hn] using hout

/-- Every successful token continuation preserves a component's terminal outcome. -/
theorem outcome_runToken_of_some
    (impl : (node : Node) → Handler (StateT S m) (network.effect node))
    (fuel : ℕ) (observer : Node) (state next : State network S)
    (value : Outcome result) (hout : outcome observer state = some value)
    (h : CanReturn (runToken impl fuel state) next) :
    outcome observer next = some value := by
  induction fuel generalizing state with
  | zero =>
    have heq : next = state := canReturn_pure_iff.mp h
    exact heq ▸ hout
  | succ fuel ih =>
    obtain ⟨mid, hstep, hrest⟩ := canReturn_bind_iff.mp h
    exact ih mid (outcome_activate_of_some impl .token state.focus observer
      state mid value hout hstep) hrest

/-- A global rank bounds activations through feedback. Progress rules out vacuous completion
through an interpreter with no possible result. The invariant may restrict reachable states. -/
structure TokenBudgetCertificate
    (impl : (node : Node) → Handler (StateT S m) (network.effect node))
    (invariant : State network S → Prop) where
  /-- Remaining activations until the designated environment has a terminal outcome. -/
  rank : State network S → ℕ
  /-- Zero potential cannot describe an unfinished state. -/
  zero : ∀ state, invariant state → rank state = 0 →
    ∃ value, outcome network.environment state = some value
  /-- Every actual successor remains in the certified invariant. -/
  preserves : ∀ state next, invariant state →
    CanReturn (activate impl .token state.focus state) next → invariant next
  /-- Every unfinished activation strictly decreases the global potential. -/
  decreases : ∀ state next, invariant state → outcome network.environment state = none →
    CanReturn (activate impl .token state.focus state) next → rank next < rank state
  /-- Every invariant state has at least one actual successor. -/
  progress : ∀ state, invariant state →
    ∃ next, CanReturn (activate impl .token state.focus state) next

namespace TokenBudgetCertificate

variable
  {impl : (node : Node) → Handler (StateT S m) (network.effect node)}
  {invariant : State network S → Prop}

/-- Every actual result after sufficient fuel is terminal at the designated environment. -/
theorem runToken_terminal (certificate : TokenBudgetCertificate impl invariant)
    (fuel : ℕ) (state next : State network S) (hinv : invariant state)
    (hbound : certificate.rank state ≤ fuel)
    (h : CanReturn (runToken impl fuel state) next) :
    ∃ value, outcome network.environment next = some value := by
  induction fuel generalizing state with
  | zero =>
    have heq : next = state := canReturn_pure_iff.mp h
    subst next
    exact certificate.zero state hinv (by omega)
  | succ fuel ih =>
    obtain ⟨mid, hstep, hrest⟩ := canReturn_bind_iff.mp h
    have hmid := certificate.preserves state mid hinv hstep
    cases hout : outcome network.environment state with
    | none =>
      exact ih mid hmid (by have := certificate.decreases state mid hinv hout hstep; omega) hrest
    | some value =>
      have hterminal := outcome_activate_of_some impl .token state.focus network.environment
        state mid value hout hstep
      exact ⟨value, outcome_runToken_of_some impl fuel network.environment
        mid next value hterminal hrest⟩

omit [LawfulMonad m] in
/-- Progress is preserved through every finite token prefix. -/
theorem runToken_nonempty (certificate : TokenBudgetCertificate impl invariant)
    (fuel : ℕ) (state : State network S) (hinv : invariant state) :
    ∃ next, CanReturn (runToken impl fuel state) next := by
  induction fuel generalizing state with
  | zero => exact ⟨state, ExactMonadAttach.canReturn_pure _⟩
  | succ fuel ih =>
    obtain ⟨mid, hstep⟩ := certificate.progress state hinv
    obtain ⟨next, hrest⟩ := ih mid (certificate.preserves state mid hinv hstep)
    exact ⟨next, ExactMonadAttach.canReturn_bind hstep hrest⟩

end TokenBudgetCertificate

end Interaction.Execution.ReactiveNetwork
