/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.Import
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

`cryptol_import` checks the exported canaries, and the kernel re-checks each acceptance. The
imports equal hand-written terms. Semantic equations then check captured variables,
higher-order arguments, record projection, folds, and finite observations of infinite sequences.
These equations describe the current partial model; normal-evaluator demand equivalence is separate.
-/

public section

open Cryptol Translation SourceElaboration

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

`cryptol_import` proves `Imported.r.accepted` for each root `r` in the kernel; each
import is the hand-written term. -/

cryptol_import Imported from "PolyFunCryptol/artifacts/references/import-canaries.json"

example : Imported.capture = capture := rfl

example : Imported.recordSelect = recordSelect := rfl

example : Imported.tupleSelect = .lam (.fst (.var .zero)) := rfl

example : Imported.higherOrder = higherOrder := rfl

example : Imported.mapped = mapped (.finite 3) := rfl

example : Imported.streamMap = mapped .infinite := rfl

example : Imported.folded = folded := rfl

example : Imported.root7 = .lam (.integer 0) := rfl

example : Imported.root8 = .lam (.app (.app (.lam (.lam (.index (.var (.succ .zero))
    (.var .zero)))) (.var .zero)) (.integer 0)) := rfl

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
      Semantics.foldlPrefix 3 3 (Resolved.denote add Environment.empty) (.value ⟨0⟩) xs := by
  unfold folded
  rw [Resolved.denote_lam_apply, Resolved.denote_app, Resolved.denote_app, Resolved.denote_app]
  rfl

example (xs : Nat → Int) (i : Nat) :
    Semantics.indexAt
      (DomainResult.applyContinuous (Resolved.denote (mapped .infinite) Environment.empty)
        (.value (fun n => .value ⟨xs n⟩))) i = .value ⟨xs i + 1⟩ := by
  simp only [mapped]
  rfl

end Cryptol.Tests.Imports
