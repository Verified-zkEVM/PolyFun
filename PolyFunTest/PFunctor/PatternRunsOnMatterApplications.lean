/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.PatternRunsOnMatter.Applications

/-!
# Executable application tests for patterns running on matter

The main example specializes the paper's Moore-machine Equation (2). It pins
both the visible outputs and the complete dependent backward trace.
-/

@[expose] public section

universe pA pB t

open PFunctor

/-- Equation (6) does not identify the pattern generator universes with the
target substitution monoid universe. -/
example (P : PFunctor.{pA, pB}) (T : PFunctor.SubstMonoid.{t, t}) :
    Lens (FreeP P ⊗ CofreeP (P ⊸ T.carrier)) T.carrier :=
  FreeP.runAgainstMonoid P T

namespace PFunctor.PatternRunsMooreTest

open FreeP

abbrev InputP : PFunctor := ⟨Bool, fun _ => PUnit⟩
abbrev MatterP : PFunctor := ⟨Nat, fun _ => Bool⟩
abbrev OutputP : PFunctor := ⟨Nat, fun _ => PUnit⟩

/-- Expose the Moore output and pull the unique result direction back to the
current Boolean input. -/
def mooreInteraction : Lens (InputP ⊗ MatterP) OutputP :=
  (fun input => input.2) ⇆
    (fun input _ => (PUnit.unit, input.1))

/-- A Moore system counting the `true` inputs consumed so far. -/
def trueCounter : DynSystem Nat MatterP :=
  DynSystem.mk' id fun count input => if input then count + 1 else count

def inputPattern : (FreeP InputP).A :=
  .liftBind true fun _ =>
    .liftBind false fun _ =>
      .liftBind true fun _ =>
        .pure PUnit.unit

def runCounter : Lens (FreeP InputP ⊗ CofreeP MatterP) (FreeP OutputP) :=
  runThrough mooreInteraction

def outputLabels : FreeM OutputP PUnit → List Nat
  | .pure _ => []
  | .liftBind output rest => output :: outputLabels (rest PUnit.unit)

/-- The Moore output is observed before consuming the current input. -/
example : outputLabels
    (runCounter.toFunA (inputPattern, trueCounter.behavior 0)) =
      [0, 1, 1] := by
  rfl

def outputPath : FreeM.Path
    (runCounter.toFunA (inputPattern, trueCounter.behavior 0)) :=
  ⟨PUnit.unit, ⟨PUnit.unit, ⟨PUnit.unit, ⟨⟩⟩⟩⟩

def matterInputs : {tree : M MatterP} → M.Vertex tree → List Bool
  | _, .root _ => []
  | _, .child input next => input :: matterInputs next

def patternPathLength : {tree : (FreeP InputP).A} →
    FreeM.Path tree → Nat
  | .pure _, _ => 0
  | .liftBind _ _, ⟨_, next⟩ => patternPathLength next + 1

/-- The backward map retains the source input order, detects swapped tensor
directions, and proves that matter advances at every synchronized node. -/
example :
    let pulled := runCounter.toFunB
      (inputPattern, trueCounter.behavior 0) outputPath
    matterInputs pulled.2 = [true, false, true] := by
  rfl

example :
    let pulled := runCounter.toFunB
      (inputPattern, trueCounter.behavior 0) outputPath
    patternPathLength pulled.1 = 3 ∧ M.Vertex.depth pulled.2 = 3 := by
  exact ⟨rfl, rfl⟩

end PFunctor.PatternRunsMooreTest

namespace PFunctor.PatternRunsGameTest

abbrev GameP : PFunctor := ⟨Bool, fun _ => Bool⟩

def idLens : Lens GameP GameP := Lens.id GameP

def flipLens : Lens GameP GameP :=
  (fun position => !position) ⇆ (fun _ direction => !direction)

/-- The challenger alternates between identity and bit-flipping interaction;
its next state records the outer response direction. -/
def challenger : DynSystem Bool (GameP ⊸ GameP) :=
  DynSystem.mk'
    (fun state => if state then flipLens else idLens)
    (fun _ direction => direction.2)

/-- The adversary exposes its state and replaces it with the pulled-back
query direction. -/
def adversary : DynSystem Bool GameP :=
  DynSystem.mk' id fun _ direction => direction

def gameTree : FreeM GameP (Bool × Bool) :=
  (DynSystem.game challenger adversary).patternN 2 (false, false)

def gamePath : FreeM.Path gameTree :=
  ⟨true, ⟨false, ⟨⟩⟩⟩

def leafValue : {tree : FreeM GameP (Bool × Bool)} →
    FreeM.Path tree → Bool × Bool
  | .pure value, _ => value
  | .liftBind _ _, ⟨_, next⟩ => leafValue next

/-- The two distinct response directions exercise both challenger updates and
the identity/flip pullbacks. A swapped update yields a different leaf. -/
example : leafValue gamePath = (false, true) := by
  rfl

/-- The object-level pattern executor and the existing game wiring agree for
the same nontrivial two-round run. -/
example :
    (adversary.runPattern (challenger.patternN 2 false) false).mapLens
        (Lens.eval GameP GameP) = gameTree :=
  DynSystem.runPattern_game challenger adversary 2 false false

/-- Pin the pattern-first symmetry in the Section 4 evaluation boundary. -/
example :
    (FreeP.evaluation GameP GameP).toFunB (true, flipLens) false =
      (true, ⟨true, false⟩) := by
  rfl

end PFunctor.PatternRunsGameTest
