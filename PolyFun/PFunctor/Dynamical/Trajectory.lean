/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Cofree
public import PolyFun.PFunctor.Dynamical.Basic
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
* `DynSystem.behavior` — the plain terminal-coalgebra semantics: the unique
  coalgebra homomorphism into `M p`, with the universal property
  `DynSystem.behavior_unique` and the induced observational equivalence
  `DynSystem.ObsEq`.
* `M.selfLabel` / `DynSystem.trajectory_eq_selfLabel_behavior` — `trajectory`
  is `behavior` relabeled so each node carries its own position, so the two
  semantics have the same information.
-/

@[expose] public section

universe uA uB w

namespace PFunctor

/-- The unique successor of a node in a unary (`X`-)cofree tree: read off the single
child indexed by the lone direction `PUnit.unit`. -/
def CofreeC.next {α : Type w} (t : CofreeC X.{uA, uB} α) : CofreeC X.{uA, uB} α :=
  t.tail.2 PUnit.unit

/-- Relabel a `p`-tree into the cofree tree whose label at each node is that node's
own position. The label carries no information beyond the tree itself; this is the
comparison map between the plain terminal-coalgebra semantics `M p` and the cofree
semantics `CofreeC p p.A` (see `DynSystem.trajectory_eq_selfLabel_behavior`). -/
def M.selfLabel {p : PFunctor.{uA, uB}} : M p → CofreeC p p.A :=
  M.corec fun t => ⟨((M.dest t).1, (M.dest t).1), (M.dest t).2⟩

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

/-! ## Terminal-coalgebra behavior

`M p` is the terminal coalgebra of the extension functor of `p`, so the coalgebra
structure map `DynSystem.out` induces a unique coalgebra homomorphism from each
`p`-system into it. Equality of behavior trees is the canonical observational
equivalence on states. -/

/-- The unique coalgebra homomorphism from a `p`-system into the terminal
`p.Obj`-coalgebra `M p`: the observable behavior tree from each state. -/
def behavior (s : DynSystem p) : s.State → M p :=
  M.corec s.out

/-- The defining equation of `behavior`: destructing the behavior tree at a state
recovers the exposed position, with each subtree the behavior of the corresponding
successor state. -/
@[simp] theorem dest_behavior (s : DynSystem p) (st : s.State) :
    M.dest (s.behavior st) = ⟨s.expose st, fun d => s.behavior (s.update st d)⟩ := by
  simp only [behavior, M.dest_corec_apply]; rfl

/-- **Bisimulation by uniqueness.** Any function into `M p` that commutes with the
coalgebra structure map `out` agrees with `behavior` on the nose: the universal
property of `M p` as the terminal `p.Obj`-coalgebra. -/
theorem behavior_unique (s : DynSystem p) (f : s.State → M p)
    (hf : ∀ st, M.dest (f st) = p.map f (s.out st)) : f = s.behavior :=
  M.corec_unique _ f hf

/-- Two states (possibly of different `p`-systems) are **observationally
equivalent** when their behavior trees are equal. By `behavior_unique`, this is
the strongest equivalence preserved by every `p.Obj`-coalgebra homomorphism. -/
def ObsEq (s₁ s₂ : DynSystem p) (st₁ : s₁.State) (st₂ : s₂.State) : Prop :=
  s₁.behavior st₁ = s₂.behavior st₂

/-- Observational equivalence is reflexive (within a fixed system). -/
@[refl] theorem ObsEq.refl (s : DynSystem p) (st : s.State) : ObsEq s s st st := rfl

/-- Observational equivalence is symmetric. -/
@[symm] theorem ObsEq.symm {s₁ s₂ : DynSystem p} {st₁ : s₁.State} {st₂ : s₂.State}
    (h : ObsEq s₁ s₂ st₁ st₂) : ObsEq s₂ s₁ st₂ st₁ := Eq.symm h

/-- Observational equivalence is transitive. -/
theorem ObsEq.trans {s₁ s₂ s₃ : DynSystem p}
    {st₁ : s₁.State} {st₂ : s₂.State} {st₃ : s₃.State}
    (h₁₂ : ObsEq s₁ s₂ st₁ st₂) (h₂₃ : ObsEq s₂ s₃ st₂ st₃) :
    ObsEq s₁ s₃ st₁ st₃ := Eq.trans h₁₂ h₂₃

/-- The cofree trajectory is the behavior tree relabeled with its own positions:
the two coinductive semantics of a dynamical system carry the same information. -/
theorem trajectory_eq_selfLabel_behavior (s : DynSystem p) (st : s.State) :
    s.trajectory st = M.selfLabel (s.behavior st) := by
  refine congrFun (Eq.symm (M.corec_unique _ (fun st => M.selfLabel (s.behavior st)) ?_)) st
  intro st
  simp only [M.selfLabel, M.dest_corec_apply]
  rfl

/-! ## Closed-system spine

A closed system's interface is `X`, whose lone direction gives every cofree node a
single successor `CofreeC.next`. Iterating it traces the system's spine, which is
exactly the `iterate` of its states. -/

/-- One step along a closed system's trajectory is the trajectory from the next
state. -/
theorem next_trajectory (s : Closed) (st : s.State) :
    CofreeC.next (trajectory s st) = trajectory s (s.step st) := rfl

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
