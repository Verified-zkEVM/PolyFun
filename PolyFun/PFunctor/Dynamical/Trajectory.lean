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

universe uA uB

namespace PFunctor

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

end DynSystem

end PFunctor
