/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Bisimulation

/-!
# Worked example: internal oracle state representation is unobservable

A deterministic "lookup oracle" with a fixed underlying answer function
`f : Q → A` (a crypto-free, structural stand-in for a random oracle: sampling
lives downstream in VCV-io). We model the *same* observable oracle two ways,
differing only in the internal bookkeeping state:

* `oracleLog` keeps the full query **log** as a `List Q`;
* `oracleCount` keeps only the query **count** as a `Nat`.

Both expose the answer to the most recent query and both answer `q` with `f q`.
The point of the example is that the choice of internal state carrier — a full
log versus a bare counter — is **unobservable**: the two systems have *equal*
behaviour trees. This is the strongest form of state hiding, honest `Eq` of
`behavior` trees via the terminal-coalgebra bisimulation principle
(`DynSystem.behavior_eq_of_isSimulation`). The generic LTS adapter below shows
that the same proof boundary can be reached from a labelled strong simulation.
-/

@[expose] public section

universe u

namespace PFunctor
namespace OracleObsEqExample

variable {Q : Type u} {A : Type u} (f : Q → A)

/-- The oracle interface: at each step the system exposes the answer to the last
query (`Option A`, `none` before any query) and accepts a new query `Q`. This is
`monomial (Option A) Q` spelled with the constructor so its constant direction
family `B _ = Q` projects transparently. -/
abbrev oraclePoly (A Q : Type u) : PFunctor.{u, u} := ⟨Option A, fun _ => Q⟩

/-- The log-carrying oracle: state is `(lastAnswer, queryLog)`. On query `q` it
answers `f q`, records the answer, and appends `q` to the log. -/
def oracleLog : DynSystem (Option A × List Q) (oraclePoly A Q) :=
  (fun s => s.1) ⇆ (fun s q => (some (f q), s.2 ++ [(q : Q)]))

/-- The count-carrying oracle: state is `(lastAnswer, queryCount)`. On query `q`
it answers `f q`, records the answer, and increments the counter. -/
def oracleCount : DynSystem (Option A × Nat) (oraclePoly A Q) :=
  (fun s => s.1) ⇆ (fun s q => (some (f q), s.2 + 1))

/-- The two carriers agree exactly on the observable part (the last answer);
the log/count bookkeeping is unconstrained. -/
def logCountRel : (Option A × List Q) → (Option A × Nat) → Prop :=
  fun s₁ s₂ => s₁.1 = s₂.1

/-- The observable-agreement relation is a simulation: related states expose the
same answer, and one query step keeps them related (both set the last answer to
`some (f q)`, regardless of how they record the query). -/
def sim : DynSystem.IsSimulation (oracleLog f) (oracleCount f) logCountRel where
  expose_eq h := h
  update_rel {s₁ s₂} h d := by
    -- `oraclePoly` has a constant direction family, so the transported query
    -- equals `d`; both updates then set the last answer to `some (f d)`.
    simp only [logCountRel, oracleLog, oracleCount, DynSystem.update]
    exact congrArg (fun x => some (f x)) (eq_of_heq (eqRec_heq h d)).symm

/-- **State hiding.** The full-log oracle and the bare-counter oracle, started
from empty bookkeeping and the same initial answer, have *equal* behaviour
trees: the internal state representation is unobservable. -/
theorem behavior_oracleLog_eq_oracleCount (a : Option A) :
    (oracleLog f).behavior (a, []) = (oracleCount f).behavior (a, 0) :=
  DynSystem.behavior_eq_of_isSimulation (sim f) rfl

/-- The same fact packaged as observational equivalence. -/
theorem obsEq_oracleLog_oracleCount (a : Option A) :
    DynSystem.ObsEq (oracleLog f) (oracleCount f) (a, []) (a, 0) :=
  DynSystem.obsEq_of_isSimulation (sim f) rfl

/-- The concrete log/count simulation induces a generic strong LTS simulation,
so the generic adapter—not merely an assumed witness—recovers the oracle
state-hiding result. -/
def ltsSim : Control.IsStrongSimulation
    (oracleLog f).toLTS (oracleCount f).toLTS logCountRel :=
  DynSystem.isStrongSimulation_of_isSimulation (sim f)

example (a : Option A) :
    (oracleLog f).behavior (a, []) = (oracleCount f).behavior (a, 0) :=
  DynSystem.obsEq_of_isStrongSimulation (ltsSim f) rfl

/-- The adapter is an equivalence on the concrete oracle relation. -/
example :
    Control.IsStrongSimulation (oracleLog f).toLTS (oracleCount f).toLTS logCountRel ↔
      DynSystem.IsSimulation (oracleLog f) (oracleCount f) logCountRel :=
  DynSystem.isStrongSimulation_toLTS_iff_isSimulation

end OracleObsEqExample
end PFunctor
