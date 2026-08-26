/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Free
public import PolyFun.PFunctor.PatternRunsOnMatter.Dynamical

/-!
# Pattern-runs-on-matter results as interaction trees

Pattern-runs-on-matter preserves the finite free-program structure. This file
exposes its synchronized output at the general ITree boundary without
changing the finite operational semantics or discarding the reached state at
leaves.
-/

@[expose] public section

universe pA pB qA qB uS uα

namespace PFunctor.DynSystem

attribute [local implicit_reducible] PFunctor.tensor

variable {P : PFunctor.{pA, pB}} {Q : PFunctor.{qA, qB}}
  {S : Type uS} {α : Type uα}

/-- Run a finite pattern on a dynamical system and expose the synchronized
finite result as a tau-free ITree. -/
def runPatternITree (system : DynSystem S Q) (pattern : FreeM P α)
    (state : S) : _root_.ITree (P ⊗ Q) (α × S) :=
  FreeM.toITree (system.runPattern pattern state)

@[simp] theorem runPatternITree_pure (system : DynSystem S Q)
    (value : α) (state : S) :
    system.runPatternITree (P := P) (pure value) state =
      ITree.pure (value, state) := by
  simp [runPatternITree]

/-- The ITree view preserves the synchronous Pattern-Runs-on-Matter node:
the pattern and matter positions are paired and both answers select the next
finite continuation. -/
theorem runPatternITree_liftBind (system : DynSystem S Q)
    (operation : P.A) (next : P.B operation → FreeM P α) (state : S) :
    system.runPatternITree (.liftBind operation next) state =
      ITree.query (operation, system.expose state) fun direction =>
        system.runPatternITree (next direction.1)
          (system.update state direction.2) := by
  unfold runPatternITree
  rw [runPattern_liftBind, FreeM.toITree_liftBind]

@[simp] theorem runPatternITree_tauFree (system : DynSystem S Q)
    (pattern : FreeM P α) (state : S) :
    ITree.TauFree (system.runPatternITree pattern state) :=
  FreeM.toITree_tauFree _

/-- The synchronized ITree lies in the exact well-founded tau-free fragment
identified by `FreeM.exists_toITree_iff`. -/
theorem runPatternITree_isFinite (system : DynSystem S Q)
    (pattern : FreeM P α) (state : S) :
    ∃ output : FreeM (P ⊗ Q) (α × S),
      FreeM.toITree output = system.runPatternITree pattern state :=
  ⟨system.runPattern pattern state, rfl⟩

end PFunctor.DynSystem
