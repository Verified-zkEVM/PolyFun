/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunTest.IPFunctor.Scoped.Import.Toy
public meta import Lean.Elab.Command

/-!
# Importing toy JSON fixtures

The frontend in `Toy.lean` is imported normally, so every kernel check below unfolds only exposed
bodies, as a downstream importer would.

* `accept.json` declares `twice`, the size-polymorphic identity `idv` (in a context holding
  `twice`, which entering the size binder weakens), and `inst`, which instantiates `idv` at `3`
  through an inserted coercion. All three are typed and accepted by the kernel with `Eq.refl`,
  and again with `decide`; `twice` gets its equation lemma. Only standard axioms are used.
* In check mode nothing is added. The kernel accepts `accept.json`; rejects the term of
  `reject-type.json`, whose declared scheme is wrong; rejects acceptance of
  `reject-erasure.json`, whose source differs in one literal; and accepts the 60 nested
  applications of `deep.json` at the ambient budget but runs out of a budget of `1`.
* In commit mode a rejected declaration leaves nothing behind: neither its definition nor the
  fallback axiom of its acceptance theorem. A compilation error leaves nothing either: the kernel
  accepts `opaque` in `reject-compile.json`, written through `uncompiled`, and after the code
  generator's error nothing of it remains. The elaborator rejects an unbound variable, and the
  budget must be positive and at most the ambient `maxHeartbeats`.
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

/-- The acceptance theorem states the source exactly. -/
example : erase Accepted.twice =
    .lam (.arrow .nat .nat) (.lam .nat (.app (.var 1) (.app (.var 1) (.var 0)))) :=
  Accepted.twice.accepted

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

namespace Decided

toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json" decide

end Decided

/-- info: 'PolyFunTest.ToyImportFixtures.Decided.inst.accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Decided.inst.accepted

/-! ## Check mode -/

namespace Checked

/--
info: twice: the kernel accepts
---
info: idv: the kernel accepts
---
info: inst: the kernel accepts
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/accept.json" check

/--
info: badType: the kernel rejects the term: (kernel) declaration type mismatch, 'PolyFunTest.ToyImportFixtures.Checked.badType' has type
  Tm [] [] (TyTerm.nat.arrow TyTerm.nat).mono
but it is expected to have type
  Tm [] [] (TyTerm.nat.arrow ((TyTerm.lit 3).vec TyTerm.nat)).mono
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/reject-type.json" check

/--
info: badSource: the kernel rejects acceptance: (kernel) declaration type mismatch, 'PolyFunTest.ToyImportFixtures.Checked.badSource.accepted' has type
  erase badSource = erase badSource
but it is expected to have type
  erase badSource = Src.Expr.lam Src.Ty.nat (Src.Expr.lit 4)
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/reject-erasure.json" check

/-- info: deep: the kernel accepts -/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/deep.json" check

/-- info: deep: the kernel rejects acceptance: (kernel) deterministic timeout -/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/deep.json" budget 1 check

end Checked

/-- info: PolyFunTest.ToyImportFixtures.Checked.twice: false -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Checked.twice

/-! ## Failures in commit mode -/

namespace Committed

/--
error: (kernel) declaration type mismatch, 'PolyFunTest.ToyImportFixtures.Committed.badSource.accepted' has type
  erase badSource = erase badSource
but it is expected to have type
  erase badSource = Src.Expr.lam Src.Ty.nat (Src.Expr.lit 4)
-/
#guard_msgs in
toy_import "PolyFunTest/IPFunctor/Scoped/Import/fixtures/reject-erasure.json"

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

/-- info: PolyFunTest.ToyImportFixtures.Committed.opaque: false -/
#guard_msgs in
#declared PolyFunTest.ToyImportFixtures.Committed.opaque

/-- info: local axioms: [] -/
#guard_msgs in
#local_axioms

end PolyFunTest.ToyImportFixtures
