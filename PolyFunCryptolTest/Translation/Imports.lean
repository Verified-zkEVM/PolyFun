/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptolTest.Translation.ImportedSource
public import PolyFunCryptol.Model.ResolvedLaws
public import PolyFunCryptol.Translation.SourceElaboration
import PolyFunCryptol.Translation.SourceElaboration
import PolyFunCryptol.Translation.SourceScope
import PolyFunCryptol.Model.Reference.Kinds
import PolyFunCryptol.Model.Reference.Types
import PolyFunCryptol.Model.Reference.Syntax
import PolyFunCryptol.Model.Types

/-!
# Official frontend import canaries

Kernel reduction checks exact imported terms. Semantic equations then check captured variables,
higher-order arguments, record projection, folds, and finite observations of infinite sequences.
These equations describe the current partial model; normal-evaluator demand equivalence is separate.
-/

public section

open Cryptol Translation SourceElaboration Tests.ImportedCanariesSource

namespace Cryptol.Tests.Imports

/-- The checked integer addition primitive. -/
@[expose] def add {Γ : List ClosedTy} : Resolved.Term Γ
    (.arrow .integer (.arrow .integer .integer)) :=
  .lam (.lam (.intOp .add (.var (.succ .zero)) (.var .zero)))

/-- A captured argument crosses both local declarations and a function binder. -/
@[expose] def capture : Resolved.Term [] (.arrow .integer (.arrow .integer .integer)) :=
  .lam (.letE (.var .zero)
    (.letE (.lam (.app (.app add (.var (.succ .zero))) (.var .zero))) (.var .zero)))

/-- A record's source labels determine the corresponding projection. -/
@[expose] def recordSelect : Resolved.Term []
    (.arrow (.prod .bit (.prod .integer .unit)) .integer) :=
  .lam (.fst (.snd (.var .zero)))

/-- Function arguments use the existing continuous function domain. -/
@[expose] def higherOrder : Resolved.Term []
    (.arrow (.arrow .integer .integer) (.arrow (.arrow .integer .integer)
      (.arrow .integer .integer))) :=
  .lam (.lam (.lam (.app (.var (.succ (.succ .zero)))
    (.app (.var (.succ .zero)) (.var .zero)))))

/-- Finite and infinite single-generator comprehensions have the same syntax interface. -/
@[expose] def mapped (length : Length) : Resolved.Term []
    (.arrow (.seq length .integer) (.seq length .integer)) :=
  .lam (.map (.lam (.app (.app add (.var .zero)) (.integer 1))) (.var .zero))

/-- A higher-order primitive keeps its function argument explicit. -/
@[expose] def folded : Resolved.Term [] (.arrow (.seq (.finite 3) .integer) .integer) :=
  .lam (.app (.app (.app (.primitive (.foldl 3 .integer .integer)) add) (.integer 0))
    (.var .zero))

/-! ## Kernel-checked acceptance

Each equation reduces the checker over the complete quoted bundle, whose nested
constructor data exceeds the default recursion depth of the reducer. -/

set_option maxRecDepth 10000 in
example : check bundle root0 = .ok ⟨_, capture⟩ := by with_unfolding_all rfl

set_option maxRecDepth 10000 in
example : check bundle root1 = .ok ⟨_, recordSelect⟩ := by with_unfolding_all rfl

set_option maxRecDepth 10000 in
example : check bundle root2 = .ok ⟨.arrow (.prod .integer (.prod .bit .unit)) .integer,
    .lam (.fst (.var .zero))⟩ := by with_unfolding_all rfl

set_option maxRecDepth 10000 in
example : check bundle root3 = .ok ⟨_, higherOrder⟩ := by with_unfolding_all rfl

set_option maxRecDepth 10000 in
example : check bundle root4 = .ok ⟨_, mapped (.finite 3)⟩ := by with_unfolding_all rfl

set_option maxRecDepth 10000 in
example : check bundle root5 = .ok ⟨_, mapped .infinite⟩ := by with_unfolding_all rfl

set_option maxRecDepth 10000 in
example : check bundle root6 = .ok ⟨_, folded⟩ := by with_unfolding_all rfl

set_option maxRecDepth 10000 in
example : check bundle root7 = .ok ⟨.arrow (.seq (.finite 0) .integer) .integer,
    .lam (.integer 0)⟩ := by with_unfolding_all rfl

set_option maxRecDepth 10000 in
example : check bundle root8 = .ok ⟨.arrow (.seq (.finite 3) .integer) .integer,
    .lam (.app (.app (.lam (.lam (.index (.var (.succ .zero)) (.var .zero)))) (.var .zero))
      (.integer 0))⟩ := by with_unfolding_all rfl

example (x y : Computation .integer) :
    DomainResult.applyContinuous
      (DomainResult.applyContinuous (Resolved.denote capture Environment.empty) x) y =
        Semantics.binary IntOp.add.eval x y := rfl

example (flag : Computation .bit) (value : Computation .integer) :
    DomainResult.applyContinuous (Resolved.denote recordSelect Environment.empty)
      (.value (flag, .value (value, .value ⟨()⟩))) = value := rfl

example (f g : Computation (.arrow .integer .integer)) (x : Computation .integer) :
    DomainResult.applyContinuous (DomainResult.applyContinuous
      (DomainResult.applyContinuous (Resolved.denote higherOrder Environment.empty) f) g) x =
        DomainResult.applyContinuous f (DomainResult.applyContinuous g x) := rfl

example (xs : Computation (.seq (.finite 3) .integer)) :
    DomainResult.applyContinuous (Resolved.denote folded Environment.empty) xs =
      Semantics.foldlPrefix 3 3 (Resolved.denote add Environment.empty) (.value ⟨0⟩) xs := rfl

example (xs : Nat → Int) (i : Nat) :
    Semantics.indexAt
      (DomainResult.applyContinuous (Resolved.denote (mapped .infinite) Environment.empty)
        (.value (fun n => .value ⟨xs n⟩))) i = .value ⟨xs i + 1⟩ := by
  simp only [mapped]
  rfl

end Cryptol.Tests.Imports
