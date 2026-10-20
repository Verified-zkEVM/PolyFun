/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Dynamical.Basic

/-!
# Direct-import compatibility for deprecated step relations

The deprecated relation spellings support plain `simp` through the ordinary
dynamical-system import, including under reversal.
-/

@[expose] public section

set_option linter.deprecated false

open PFunctor DynSystem

universe u v uA uB vA vB

variable {S : Type u} {T : Type v} {P : PFunctor.{uA, uB}} {Q : PFunctor.{vA, vB}}
  (s : DynSystem S P) (t : DynSystem T Q)

-- Old import surface: `simp` closes an application of the permissive relation.
example (a : s.Step) (b : t.Step) : (StepRel.top : StepRel s t) a b := by simp

-- Old import surface: `simp` exposes conjunction through the deprecated head.
example (r q : StepRel s t) (a : s.Step) (b : t.Step) :
    StepRel.inter r q a b ↔ r a b ∧ q a b := by simp

-- Old import surface: `simp` distributes reversal through deprecated intersection.
example (r q : StepRel s t) :
    StepRel.reverse (StepRel.inter r q) =
      StepRel.inter (StepRel.reverse r) (StepRel.reverse q) := by simp

-- Old import surface: reversal also simplifies the deprecated permissive relation.
example : StepRel.reverse (StepRel.top : StepRel s t) = StepRel.top := by simp
