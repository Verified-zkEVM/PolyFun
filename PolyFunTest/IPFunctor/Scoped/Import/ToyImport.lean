/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunTest.IPFunctor.Scoped.Import.Toy
import Batteries.Tactic.Lint
meta import Examples.Tutorials.ScopedVectors
public meta import Lean.Elab.Command
public meta import Batteries.Tactic.Lint.Basic
public meta import Lean.Compiler.NoncomputableAttr

/-!
# Importing toy JSON fixtures

The frontend in `Toy.lean` is imported normally, so every kernel check below unfolds only exposed
bodies, as a downstream importer would.

* `accept.json` declares `twice`, the size-polymorphic identity `idv` (in a context holding
  `twice`, which entering the size binder weakens), and `inst`, which instantiates `idv` at `3`
  through an inserted coercion. Each comes with its source as an auxiliary definition, and the
  closed `twice` with its lazy meaning, both `noncomputable`. All three are typed and accepted by
  the kernel with `Eq.refl`, and again with `decide`; `twice` gets its equation lemma. The bundle
  declarations `declNames` and `declNames_length` come first. Only standard axioms are used.
* `meaning.json` declares `seven`, which is `(λ x. x) 7`. Its equation `seven.meaning_eq` states
  the auxiliary definition `seven.meaning` as a number. The import prepares the equation before it
  adds `seven.meaning`, so the equation takes the auxiliary definition's type.
* With `natives`, the closed `twice` also gets `twice.native`, its total evaluation, as a compiled
  auxiliary definition, which compiled code runs, and the theorem
  `twice.meaning_represents : Rep _ twice.meaning twice.native`. The frontend assembles that proof
  term before `twice.meaning` and `twice.native` exist, and only the kernel checks it, in commit
  mode and in check mode. With `misrepresent` the kernel rejects that theorem, in check mode and in
  commit mode, where nothing of the import remains.
* With `nolint`, `underscore.json`'s `twice_nat` and its auxiliary definitions are marked
  `@[nolint defsWithUnderscore]`, and its equation lemma `@[nolint checkType]`; its acceptance
  theorem and the bundle declarations are not marked. `#lint` skips the generated definitions and
  still reports a hand-written definition beside them.
* In check mode nothing is added. The kernel accepts `accept.json`; rejects the term of
  `reject-type.json`, whose declared scheme is wrong; rejects acceptance of
  `reject-erasure.json`, whose source differs in one literal; and accepts the 60 nested
  applications of `deep.json` at the ambient budget, but its equation lemma runs out of a
  budget of `100`; a budget of `1` does not cover the declaration's elaboration.
* `bundle-deep.json` holds three such declarations, of about 5M heartbeats each. Under a limit of
  6M heartbeats they import in one command, because each declaration has its own heartbeat
  scope; without the scopes the third one runs out, and the rollback removes the first two.
* In commit mode a rejection leaves nothing behind: in `reject-mid.json` the third of four
  declarations fails acceptance, and neither the bundle declarations, nor the two declarations
  before it, nor any fallback axiom remains. A compilation error rolls the import back as well:
  the kernel accepts `opaque` in `reject-compile.json`, written through `uncompiled`, and after
  the code generator's error nothing of it remains. The elaborator rejects an unbound variable,
  and the budget must be positive and at most the ambient `maxHeartbeats`.
-/

public section

namespace PolyFunTest.ToyImportFixtures

open Lean Elab Command Examples.ScopedVectors PolyFunTest.ToyImport

/-- The axioms declared in the current module. -/
meta def localAxioms (env : Environment) : Array Name :=
  env.constants.map₂.foldl (init := #[]) fun acc name info =>
    if info matches .axiomInfo _ then acc.push name else acc

/-- Report the axioms declared in the current module. -/
elab "#local_axioms" : command => do
  logInfo m!"local axioms: {localAxioms (← getEnv)}"

/-- Report whether a declaration of the given name exists, without resolving it. -/
elab "#declared " name:ident : command => do
  logInfo m!"{name.getId}: {(← getEnv).contains name.getId}"

/-- Report whether a declaration is marked `noncomputable`. -/
elab "#noncomputable " name:ident : command => do
  logInfo m!"{name.getId}: {isNoncomputable (← getEnv) name.getId}"

/-- Report the linters that a declaration's `@[nolint]` names, none without the attribute. -/
elab "#nolint " name:ident : command => do
  let linters := (Batteries.Tactic.Lint.nolintAttr.getParam? (← getEnv) name.getId).getD #[]
  logInfo m!"{name.getId}: {linters.toList}"

/-! ## Accepted declarations -/

namespace Accepted

toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json"

end Accepted

/-- info: 'PolyFunTest.ToyImportFixtures.Accepted.inst.accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Accepted.inst.accepted

/-- info: 'PolyFunTest.ToyImportFixtures.Accepted.twice.evaluate_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Accepted.twice.evaluate_eq

/-- The source is an auxiliary definition, and the acceptance theorem compares against it. -/
example : Accepted.twice.source =
    .lam (.arrow .nat .nat) (.lam .nat (.app (.var 1) (.app (.var 1) (.var 0)))) :=
  rfl

example : erase Accepted.twice = Accepted.twice.source :=
  Accepted.twice.accepted

/-- The closed declaration also gets its lazy meaning. -/
example : Accepted.twice.meaning = meaning Accepted.twice :=
  rfl

/-- info: PolyFunTest.ToyImportFixtures.Accepted.twice.meaning: true -/
#guard_msgs in
#noncomputable PolyFunTest.ToyImportFixtures.Accepted.twice.meaning

/-- info: PolyFunTest.ToyImportFixtures.Accepted.inst.source: true -/
#guard_msgs in
#noncomputable PolyFunTest.ToyImportFixtures.Accepted.inst.source

/-! ## An equation on an auxiliary definition -/

namespace Meaning

toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/meaning.json"

end Meaning

/-- The left side of `seven.meaning_eq` is the auxiliary definition `seven.meaning`, which the
import added only after preparing the equation. -/
example : Meaning.seven.meaning = (DomainResult.value ⟨7⟩ : DomainResult Empty (DiscreteOrder ℕ)) :=
  Meaning.seven.meaning_eq

/-- info: 'PolyFunTest.ToyImportFixtures.Meaning.seven.meaning_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meaning.seven.meaning_eq

/-- The bundle declarations: a definition and a theorem the kernel decides. -/
example : Accepted.declNames = ["twice", "idv", "inst"] :=
  rfl

example : Accepted.declNames.length = 3 :=
  Accepted.declNames_length

/-- The equation lemma's right side is free of syntax. -/
example (f : ℕ → ℕ) (x : ℕ) :
    (show (ℕ → ℕ) → ℕ → ℕ from evaluate Accepted.twice) f x = f (f x) :=
  congrFun (congrFun Accepted.twice.evaluate_eq f) x

/-- `inst` lives in the context of `idv`'s scheme. -/
example : Tm []
    [TyTerm.all (TyTerm.mono (TyTerm.arrow (TyTerm.vec (.var .zero) TyTerm.nat)
      (TyTerm.vec (.var .zero) TyTerm.nat)))]
    (TyTerm.mono (TyTerm.arrow (TyTerm.vec (TyTerm.lit 3) TyTerm.nat)
      (TyTerm.vec (TyTerm.lit 3) TyTerm.nat))) :=
  Accepted.inst

/-! ## Compiled auxiliary definitions and kernel-checked theorems -/

namespace Natives

toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json" natives

end Natives

-- `twice.native` is compiled, and compiled code runs it.
/-- info: PolyFunTest.ToyImportFixtures.Natives.twice.native: false -/
#guard_msgs in
#noncomputable PolyFunTest.ToyImportFixtures.Natives.twice.native

/-- info: 7 -/
#guard_msgs in
#eval (show (ℕ → ℕ) → ℕ → ℕ from Natives.twice.native) (· + 1) 5

/-- The theorem the frontend assembled, checked only by the kernel. -/
example : Rep _ Natives.twice.meaning Natives.twice.native :=
  Natives.twice.meaning_represents

/--
info: 'PolyFunTest.ToyImportFixtures.Natives.twice.meaning_represents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Natives.twice.meaning_represents

-- A declaration with dependencies gets neither.
/-- info: PolyFunTest.ToyImportFixtures.Natives.idv.native: false -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Natives.idv.native

namespace Misrepresented

-- The kernel rejects the theorem the frontend assembled, and the import leaves nothing.
/--
error: (kernel) declaration type mismatch, 'PolyFunTest.ToyImportFixtures.Misrepresented.twice.meaning_represents' has type
  True
but it is expected to have type
  Rep
    (IPFunctor.ScopedSignature.Term.denote (fun {a} ↦ tyAlg)
      ((TyTerm.nat.arrow TyTerm.nat).arrow (TyTerm.nat.arrow TyTerm.nat)).mono IPFunctor.ScopedSignature.Env.empty)
    twice.meaning twice.native
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json" natives misrepresent

end Misrepresented

/-- info: PolyFunTest.ToyImportFixtures.Misrepresented.twice: false -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Misrepresented.twice

/-! ## Linters that skip generated declarations -/

namespace Nolint

toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/underscore.json" nolint

/-- A hand-written definition beside the imported ones, which no import marks. -/
def hand_written : ℕ := 0

end Nolint

/-- info: PolyFunTest.ToyImportFixtures.Nolint.twice_nat: [defsWithUnderscore] -/
#guard_msgs in
#nolint PolyFunTest.ToyImportFixtures.Nolint.twice_nat

/-- info: PolyFunTest.ToyImportFixtures.Nolint.twice_nat.meaning: [defsWithUnderscore] -/
#guard_msgs in
#nolint PolyFunTest.ToyImportFixtures.Nolint.twice_nat.meaning

/-- info: PolyFunTest.ToyImportFixtures.Nolint.twice_nat.evaluate_eq: [checkType] -/
#guard_msgs in
#nolint PolyFunTest.ToyImportFixtures.Nolint.twice_nat.evaluate_eq

/-- info: PolyFunTest.ToyImportFixtures.Nolint.twice_nat.accepted: [] -/
#guard_msgs in
#nolint PolyFunTest.ToyImportFixtures.Nolint.twice_nat.accepted

/-- info: PolyFunTest.ToyImportFixtures.Nolint.declNames: [] -/
#guard_msgs in
#nolint PolyFunTest.ToyImportFixtures.Nolint.declNames

/-- info: PolyFunTest.ToyImportFixtures.Nolint.hand_written: [] -/
#guard_msgs in
#nolint PolyFunTest.ToyImportFixtures.Nolint.hand_written

-- `defsWithUnderscore` skips `twice_nat`, `twice_nat.source` and `twice_nat.meaning`, and reports
-- the hand-written definition.
/--
error: /- The `defsWithUnderscore` linter reports:
FOUND definitions with an underscore in their name.
This linter can be disabled with `@[nolint defsWithUnderscore]`. -/
#check Nolint.hand_written /- The definition `PolyFunTest.ToyImportFixtures.Nolint.hand_written` contains an underscore. This almost surely violates mathlib's naming convention; use lowerCamelCase or UpperCamelCase instead. -/
-/
#guard_msgs in
#lint- only defsWithUnderscore

namespace Decided

toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json" decide

end Decided

/-- info: 'PolyFunTest.ToyImportFixtures.Decided.inst.accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Decided.inst.accepted

/-! ## Check mode -/

namespace Checked

/--
info: declNames: the kernel accepts
---
info: declNames_length: the kernel accepts
---
info: twice: the kernel accepts
---
info: idv: the kernel accepts
---
info: inst: the kernel accepts
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json" check

/--
info: declNames: the kernel accepts
---
info: declNames_length: the kernel accepts
---
info: twice: the kernel accepts
---
info: idv: the kernel accepts
---
info: inst: the kernel accepts
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json" check natives

/--
info: declNames: the kernel accepts
---
info: declNames_length: the kernel accepts
---
info: twice: the kernel rejects `meaning_represents`: (kernel) declaration type mismatch, 'PolyFunTest.ToyImportFixtures.Checked.twice.meaning_represents' has type
  True
but it is expected to have type
  Rep
    (IPFunctor.ScopedSignature.Term.denote (fun {a} ↦ tyAlg)
      ((TyTerm.nat.arrow TyTerm.nat).arrow (TyTerm.nat.arrow TyTerm.nat)).mono IPFunctor.ScopedSignature.Env.empty)
    twice.meaning twice.native
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json" check natives misrepresent

/--
info: declNames: the kernel accepts
---
info: declNames_length: the kernel accepts
---
info: badType: the kernel rejects the term: (kernel) declaration type mismatch, 'PolyFunTest.ToyImportFixtures.Checked.badType' has type
  Tm [] [] (TyTerm.nat.arrow TyTerm.nat).mono
but it is expected to have type
  Tm [] [] (TyTerm.nat.arrow ((TyTerm.lit 3).vec TyTerm.nat)).mono
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/reject-type.json" check

/--
info: declNames: the kernel accepts
---
info: declNames_length: the kernel accepts
---
info: badSource: the kernel rejects acceptance: (kernel) declaration type mismatch, 'PolyFunTest.ToyImportFixtures.Checked.badSource.accepted' has type
  erase badSource = erase badSource
but it is expected to have type
  erase badSource = badSource.source
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/reject-erasure.json" check

/--
info: declNames: the kernel accepts
---
info: declNames_length: the kernel accepts
---
info: deep: the kernel accepts
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/deep.json" check

/--
info: declNames: the kernel accepts
---
info: declNames_length: the kernel accepts
---
info: deep: the kernel rejects `evaluate_eq`: (kernel) deterministic timeout
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/deep.json" budget 100 check

-- The budget also bounds elaboration, which does not fit in 1000 heartbeats.
/--
info: declNames: the kernel accepts
---
info: declNames_length: the kernel accepts
---
error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (1) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/deep.json" budget 1 check

/--
info: declNames: the kernel accepts
---
info: declNames_length: the kernel accepts
---
info: first: the kernel accepts
---
info: second: the kernel accepts
---
info: third: the kernel rejects acceptance: (kernel) declaration type mismatch, 'PolyFunTest.ToyImportFixtures.Checked.third.accepted' has type
  erase third = erase third
but it is expected to have type
  erase third = third.source
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/reject-mid.json" check

end Checked

/-- info: PolyFunTest.ToyImportFixtures.Checked.twice: false -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Checked.twice

/-! ## Heartbeat scopes -/

namespace Scoped

set_option maxHeartbeats 6000 in
-- Lowered below the bundle's 15M heartbeats, above each declaration's 5M.
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/bundle-deep.json"

end Scoped

/-- info: PolyFunTest.ToyImportFixtures.Scoped.deep3.accepted: true -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Scoped.deep3.accepted

namespace Unscoped

/--
error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (6000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option maxHeartbeats 6000 in
-- Lowered as for `Scoped`: without per-declaration scopes the bundle does not fit.
toy_import_unscoped "PolyFunTest/IPFunctor/Scoped/Import/fixtures/bundle-deep.json"

end Unscoped

/-- info: PolyFunTest.ToyImportFixtures.Unscoped.deep1: false -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Unscoped.deep1

/-! ## Failures in commit mode -/

namespace Committed

/--
error: (kernel) declaration type mismatch, 'PolyFunTest.ToyImportFixtures.Committed.badSource.accepted' has type
  erase badSource = erase badSource
but it is expected to have type
  erase badSource = badSource.source
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/reject-erasure.json"

/--
error: (kernel) declaration type mismatch, 'PolyFunTest.ToyImportFixtures.Committed.third.accepted' has type
  erase third = erase third
but it is expected to have type
  erase third = third.source
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/reject-mid.json"

-- The kernel accepts `opaque`; the code generator cannot compile it.
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'uncompiled', which is 'noncomputable'
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/reject-compile.json"

/-- error: toy: variable 1 is not in scope -/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/reject-scope.json"

/-- error: import budget 0 would leave the kernel unlimited; give a positive budget -/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json" budget 0

/-- error: import budget 100000000 exceeds the ambient maxHeartbeats 200000 -/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json" budget 100000000

end Committed

/-- info: PolyFunTest.ToyImportFixtures.Committed.badSource: false -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Committed.badSource

/-- info: PolyFunTest.ToyImportFixtures.Committed.first: false -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Committed.first

/-- info: PolyFunTest.ToyImportFixtures.Committed.declNames: false -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Committed.declNames

/-- info: PolyFunTest.ToyImportFixtures.Committed.opaque: false -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Committed.opaque

/-- info: local axioms: [] -/
#guard_msgs in
#local_axioms

end PolyFunTest.ToyImportFixtures
