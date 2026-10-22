/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.Basic.StateChain

/-!
# Deprecated state-chain family contracts

The type-tree facade keeps its specialised binders and unfolding equations through ordinary imports.
-/

@[expose] public section

set_option linter.deprecated false

universe u

open Interaction

namespace Interaction.TypeTree

variable {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → TypeTree}
variable {advance : (i : Nat) → (s : Stage i) → Path (spec i s) → Stage (i + 1)}

-- Old binder names, including the specialised `spec` family and the zero lemma's `tr`.
example (Family : (i : Nat) → Stage i → Type u) (i : Nat) (s : Stage i) (tr : PUnit) :
    PFunctor.FreeM.Path.stateChainFamily (spec := spec) (advance := advance)
      (Family := Family) (n := 0) (i := i) (stage := s) tr = Family i s := by
  rw [PFunctor.FreeM.Path.stateChainFamily_zero (spec := spec) (advance := advance)
    (Family := Family) (i := i) (s := s) (tr := tr)]

-- Old universe and positional arity: no polynomial, leaf type, or leaf value arguments.
example : ((Family : (i : Nat) → Stage i → Type u) → (n i : Nat) → (stage : Stage i) →
    Path (_root_.PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i stage) → Type u) :=
  @PFunctor.FreeM.Path.stateChainFamily.{u} Stage spec advance

example (Family : (i : Nat) → Stage i → Type u) (i : Nat) (s : Stage i) (tr : PUnit) :
    PFunctor.FreeM.Path.stateChainFamily (spec := spec) (advance := advance) Family 0 i s tr =
      Family i s :=
  @PFunctor.FreeM.Path.stateChainFamily_zero.{u} Stage spec advance Family i s tr

-- Old constant-family binder names and statement, including the `α` argument.
example (α : Type u) (n i : Nat) (s : Stage i)
    (tr : Path (_root_.PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s)) :
    PFunctor.FreeM.Path.stateChainFamily (spec := spec) (advance := advance)
      (fun _ _ => α) n i s tr = α := by
  rw [PFunctor.FreeM.Path.stateChainFamily_const (spec := spec) (advance := advance)
    (α := α) (n := n) (i := i) (s := s) (tr := tr)]

example (α : Type u) (n i : Nat) (s : Stage i)
    (tr : Path (_root_.PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n i s)) :
    PFunctor.FreeM.Path.stateChainFamily (spec := spec) (advance := advance)
      (fun _ _ => α) n i s tr = α :=
  @PFunctor.FreeM.Path.stateChainFamily_const.{u} Stage spec advance α n i s tr

-- Old explicit unfolding retains the recursive facade spelling.
example (Family : (i : Nat) → Stage i → Type u) (i : Nat) (s : Stage i) (tr : PUnit) :
    PFunctor.FreeM.Path.stateChainFamily (spec := spec) (advance := advance) Family 0 i s tr =
      Family i s := by
  simp only [PFunctor.FreeM.Path.stateChainFamily]

example (Family : (i : Nat) → Stage i → Type u) (n i : Nat) (stage : Stage i)
    (tr : Path (_root_.PFunctor.FreeM.stateChain PUnit.unit Stage spec advance (n + 1) i stage)) :
    PFunctor.FreeM.Path.stateChainFamily Family (n + 1) i stage tr =
      _root_.PFunctor.FreeM.Path.liftAppend (spec i stage)
        (fun tr₁ =>
          _root_.PFunctor.FreeM.stateChain PUnit.unit Stage spec advance n (i + 1)
            (advance i stage tr₁))
        (fun tr₁ trRest =>
          PFunctor.FreeM.Path.stateChainFamily Family n (i + 1) (advance i stage tr₁) trRest)
        tr := by
  simp only [PFunctor.FreeM.Path.stateChainFamily]

end Interaction.TypeTree
