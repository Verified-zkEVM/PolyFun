/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Basic
public import PolyFun.PFunctor.Cofree
public import PolyFun.PFunctor.M

/-!
# Trajectories of dynamical systems

The infinite behaviour of a `p`-dynamical system, started from a state, is a
cofree-`p` tree whose node label is the currently exposed position and whose
`p`-indexed children are the trajectories from each successor state. This is the
cofree comonad `CofreeC p p.A` (the "matter" that the system's "pattern" runs
on, in the Niu–Spivak slogan).

* `DynSystem.trajectory` — the behaviour tree from a starting state.
* `DynSystem.head_trajectory` / `DynSystem.tail_trajectory` — its one-step
  unfolding (exposed position and successor trajectories).
-/

@[expose] public section

universe uA uB w

namespace PFunctor

/-- The unique successor of a node in a unary (`X`-)cofree tree: read off the single
child indexed by the lone direction `PUnit.unit`. -/
def CofreeC.next {α : Type w} (t : CofreeC X.{uA, uB} α) : CofreeC X.{uA, uB} α :=
  (CofreeC.tail t).2 PUnit.unit

namespace DynSystem

variable {p : PFunctor.{uA, uB}}

/-- The behaviour tree of a `p`-system started from `st`: a cofree-`p` tree whose
head label is the exposed position and whose `p.B`-indexed children are the
trajectories from each successor state. -/
def trajectory (s : DynSystem p) (st : s.State) : CofreeC p p.A :=
  M.corec (fun st => ⟨(s.expose st, s.expose st), fun d => s.update st d⟩) st

/-- One-step unfolding of a trajectory's `M.dest`: the stored label and position
are the exposed position, and the children are the successor trajectories. -/
theorem dest_trajectory (s : DynSystem p) (st : s.State) :
    M.dest (trajectory s st)
      = ⟨(s.expose st, s.expose st), fun d => trajectory s (s.update st d)⟩ := by
  simp only [trajectory, M.dest_corec_apply]

@[simp] theorem head_trajectory (s : DynSystem p) (st : s.State) :
    (trajectory s st).head = s.expose st := by
  simp only [CofreeC.head, dest_trajectory]

@[simp] theorem tail_trajectory (s : DynSystem p) (st : s.State) :
    (trajectory s st).tail = ⟨s.expose st, fun d => trajectory s (s.update st d)⟩ := by
  simp only [CofreeC.tail]; rw [dest_trajectory]; rfl

/-! ## Closed-system spine

A closed system's interface is `X`, whose lone direction gives every cofree node a
single successor `CofreeC.next`. Iterating it traces the system's spine, which is
exactly the `iterate` of its states. -/

/-- One step along a closed system's trajectory is the trajectory from the next
state. -/
theorem next_trajectory (s : Closed) (st : s.State) :
    CofreeC.next (trajectory s st) = trajectory s (s.step st) := by
  simp only [CofreeC.next]; rfl

/-- The `n`-fold successor of a closed system's trajectory is the trajectory from
its `n`-th iterated state: the trajectory's spine is the `iterate` of states. -/
theorem next_iterate_trajectory (s : Closed) (st : s.State) (n : ℕ) :
    (CofreeC.next)^[n] (trajectory s st) = trajectory s ((s.step)^[n] st) := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, next_trajectory, ih, Function.iterate_succ_apply]

end DynSystem

end PFunctor
