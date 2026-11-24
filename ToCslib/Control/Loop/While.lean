/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Init.Internal.Order.While

/-!
# `while` and `repeat` loops

`while c do body` and `repeat body` elaborate to `forIn Lean.Loop.mk init f`, a loop over the
infinite container `Lean.Loop` whose body decides when to stop by returning `.done`. Core unfolds
such a loop one step at a time in every monad with a `Lean.Order.MonadTail` instance
(`Lean.Loop.forIn_eq_of_monadTail`), which covers `Id`, `Option`, `Except`, `StateT`, `ReaderT`,
`ExceptT`, `OptionT`, `ST`, and `IO`.

This module gives two ways to characterize such a loop:

* `Lean.Loop.forIn_eq_of_trace`: the loop runs through prescribed states `S 0, …, S n` and stops
  at `S n`, so it returns what the body returns there. This holds in every such monad.
* `Lean.Loop.idRun_forIn_of_measure`: in `Id`, an invariant preserved by every step that yields,
  together with a natural-number measure that every such step decreases, proves the postcondition
  that every step that stops establishes.
-/

public section

universe u v

namespace Lean.Loop

variable {m : Type u → Type v} {σ : Type u}

/-- A loop that runs through the states `S 0, …, S n`, yielding `S (i + 1)` from `S i` and
stopping at `S n` with the value `r`, returns `r`. -/
theorem forIn_eq_of_trace [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m]
    {body : Unit → σ → m (ForInStep σ)} {n : Nat} (S : Nat → σ) {r : σ}
    (hstep : ∀ i < n, body () (S i) = pure (.yield (S (i + 1))))
    (hdone : body () (S n) = pure (.done r)) :
    forIn Lean.Loop.mk (S 0) body = pure r := by
  have hu (b : σ) : forIn Lean.Loop.mk b body = (do
      match ← body () b with
      | .done b => pure b
      | .yield b => forIn Lean.Loop.mk b body) :=
    Lean.Loop.forIn_eq_of_monadTail
  suffices h : ∀ k i, i + k = n → forIn Lean.Loop.mk (S i) body = pure r from
    h n 0 (Nat.zero_add n)
  intro k
  induction k with
  | zero =>
    intro i hi
    rw [Nat.add_zero] at hi
    subst hi
    rw [hu, hdone, pure_bind]
  | succ k ih =>
    intro i hi
    rw [hu, hstep i (by omega), pure_bind]
    exact ih (i + 1) (by omega)

/-- In `Id`, a loop whose steps preserve `inv` and decrease the measure `μ` whenever they yield,
and establish `post` whenever they stop, returns a state satisfying `post`. -/
theorem idRun_forIn_of_measure {body : Unit → σ → Id (ForInStep σ)} (inv post : σ → Prop)
    (μ : σ → Nat) {init : σ} (hinit : inv init)
    (step : ∀ s, inv s → match Id.run (body () s) with
      | .yield s' => inv s' ∧ μ s' < μ s
      | .done s' => post s') :
    post (Id.run (forIn Lean.Loop.mk init body)) := by
  induction hμ : μ init using Nat.strongRecOn generalizing init with
  | ind k ih =>
    have hu : forIn Lean.Loop.mk init body = (do
        match ← body () init with
        | .done b => pure b
        | .yield b => forIn Lean.Loop.mk b body) :=
      Lean.Loop.forIn_eq_of_monadTail
    have hs := step init hinit
    rw [hu]
    revert hs
    cases body () init with
    | done s' => exact id
    | yield s' => exact fun ⟨hinv, hlt⟩ => ih (μ s') (hμ ▸ hlt) hinv rfl

end Lean.Loop
