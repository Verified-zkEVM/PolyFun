/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Support

/-!
# Free-program support through ordinary imports

The `MonadAttach` instances on free programs, the inductive return predicate and the support
equations are usable from a module that imports them without `import all`, at independent
universes. Membership in the support is the inductive predicate by `Iff.rfl`.
-/

public section

universe uA uB v

namespace PolyFunTest.ModuleAPI.FreeSupport

open PFunctor MonadAttach

variable {P : PFunctor.{uA, uB}} {α : Type v}

example : ExactMonadAttach (FreeM P) :=
  inferInstance

example (x : FreeM P α) (a : α) : a ∈ support x ↔ FreeM.CanReturn x a :=
  Iff.rfl

example (a b : α) : FreeM.CanReturn (FreeM.pure a : FreeM P α) b ↔ b = a :=
  FreeM.canReturn_pure_iff

example (op : P.A) (r : P.B op → FreeM P α) (a : α) :
    FreeM.CanReturn (FreeM.liftBind op r) a ↔ ∃ b, FreeM.CanReturn (r b) a :=
  FreeM.canReturn_liftBind_iff

example (a : α) : support (pure a : FreeM P α) = {a} :=
  FreeM.support_pure a

example (op : P.A) (r : P.B op → FreeM P α) :
    support (FreeM.liftBind op r) = ⋃ b, support (r b) :=
  FreeM.support_liftBind op r

example (op : P.A) (r : P.B op → FreeM P α) (c : α) :
    c ∈ support (FreeM.liftBind op r) ↔ ∃ b, c ∈ support (r b) :=
  FreeM.mem_support_liftBind

end PolyFunTest.ModuleAPI.FreeSupport
