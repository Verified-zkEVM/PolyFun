/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Combinators
public import PolyFun.PFunctor.Dynamical.Trajectory

/-!
# Closed-loop behaviour of Moore machines

Closing a Moore machine on itself with a feedback map `f : O → I`
(`MooreMachine.feedback`) yields an autonomous closed system that runs forever. Its
observable behaviour is the ℕ-indexed stream of outputs read off the iterated states.
This file ties the `feedback` combinator (the "pattern") to the `iterate` /
`trajectory` of the resulting closed system (the "matter" it runs on, in the
Niu–Spivak slogan).

* `MooreMachine.feedbackStep` — the closed-loop transition, equal to
  `(feedback f m).step` by `feedback_step`.
* `MooreMachine.feedbackStream` — the output stream of the closed-loop system.
* `MooreMachine.next_iterate_feedback` — its trajectory spine is the state iterate.
-/

@[expose] public section

universe u uO uI

namespace PFunctor

namespace MooreMachine

variable {S : Type u} {O : Type uO} {I : Type uI}

/-- The closed-loop transition: advance the state by feeding the current output back
through `f` as the next input. This is definitionally `(feedback f m).step` (see
`feedback_step`); it is phrased directly on `m` so the resulting stream's universes do
not depend on the phantom direction universe of the closed interface `X`. -/
def feedbackStep (f : O → I) (m : MooreMachine S O I) (st : S) : S :=
  m.transition st (f (m.output st))

/-- The output observed at time `n` once the machine is closed on itself by feeding
its output back through `f`: the original Moore output read off each closed-loop state. -/
def feedbackStream (f : O → I) (m : MooreMachine S O I) (st : S) (n : ℕ) : O :=
  m.output ((m.feedbackStep f)^[n] st)

@[simp] theorem feedbackStream_zero (f : O → I) (m : MooreMachine S O I) (st : S) :
    m.feedbackStream f st 0 = m.output st := rfl

/-- The closed-loop output stream advances by feeding the current output back as the
next input. -/
theorem feedbackStream_succ (f : O → I) (m : MooreMachine S O I) (st : S) (n : ℕ) :
    m.feedbackStream f st (n + 1) = m.feedbackStream f (m.transition st (f (m.output st))) n := by
  simp only [feedbackStream, Function.iterate_succ_apply, feedbackStep]

/-- The trajectory spine of the closed-loop system is the iterate of its states:
the closed system's "matter" is exactly its state stream. -/
theorem next_iterate_feedback (f : O → I) (m : MooreMachine S O I) (st : S) (n : ℕ) :
    (CofreeC.next)^[n] (DynSystem.trajectory (feedback f m) st)
      = DynSystem.trajectory (feedback f m) ((feedback f m).iterate st n) :=
  DynSystem.next_iterate_trajectory (feedback f m) st n

end MooreMachine

end PFunctor
