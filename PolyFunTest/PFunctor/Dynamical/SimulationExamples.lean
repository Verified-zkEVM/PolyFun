/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Dynamical.Simulation

/-!
# Examples for simulations between dynamical systems

Regression tests: equality is a simulation of a system by itself, and
`implements_of_isSimulation` turns a simulation into behaviour equality.
-/

@[expose] public section

universe u

namespace PFunctor

variable {p : PFunctor.{u, u}}

/-- Equality is a simulation of any dynamical system by itself. -/
def idSim (D : DynSystem.{u} p) : DynSystem.IsSimulation D D (· = ·) where
  expose_eq h := congrArg D.expose h
  update_rel h _ := by subst h; rfl

/-- A simulation turns into behaviour equality. -/
example (D : DynSystem.{u} p) (s : D.State) : D.behavior s = D.behavior s :=
  DynSystem.implements_of_isSimulation (idSim D) rfl

/-- ...and hence observational equivalence. -/
example (D : DynSystem.{u} p) (s : D.State) : DynSystem.ObsEq D D s s :=
  DynSystem.obsEq_of_isSimulation (idSim D) rfl

end PFunctor
