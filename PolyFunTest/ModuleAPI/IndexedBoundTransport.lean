/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Free.Lens

/-!
# Bound transport and branch coverage

Generic consumers use independent indices and result universes. The concrete
counterexample prunes an expensive branch, showing why bound reflection requires
surjectivity of the response map.
-/

public section

universe uI uJ uA uB uC uD uX uY

namespace PolyFunTest.ModuleAPI.IndexedBoundTransport

open IPFunctor

example {I : Type uI} {J : Type uJ} {P : Endo.{uI, uA, uB} I} {Q : Endo.{uJ, uC, uD} J}
    {f : I → J} {X : I → Type uX} {Y : J → Type uY} (h : Reindexing P Q f)
    (leaf : ∀ s, X s → Y (f s)) (hargs : ∀ s a, Function.Surjective (h.arg s a))
    {s : I} (x : IFreeM P X s) (n : Nat) :
    (x.reindex h leaf).IsTotalRollBound n ↔ x.IsTotalRollBound n :=
  IFreeM.isRollBound_reindex_iff h leaf hargs x n

/-- A Boolean branch at the sole state. -/
abbrev Branch : Endo Unit := ⟨fun _ => Unit, fun _ _ => Bool, fun _ _ _ => ()⟩

/-- A unary branch at the sole state. -/
abbrev Unary : Endo Unit := ⟨fun _ => Unit, fun _ _ => Unit, fun _ _ _ => ()⟩

/-- Keep only the false branch of each operation. -/
@[expose] def prune : Reindexing Branch Unary id where
  op _ _ := ()
  arg _ _ _ := false
  source _ _ _ := rfl

/-- The true answer requests one more operation before returning. -/
@[expose] def program : IFreeM Branch (fun _ => Unit) () :=
  .liftBind () fun answer => if answer then .liftBind () (fun _ => .pure ()) else .pure ()

example : (program.reindex prune (fun _ value => value)).IsTotalRollBound 1 := by
  simp [program, prune, IFreeM.reindex_liftBind, IFreeM.IsTotalRollBound,
    IFreeM.isRollBound_liftBind_iff]

example : ¬ program.IsTotalRollBound 1 := by
  intro h
  have expensive := h.2 true
  exact Nat.not_lt_zero _ expensive.1

/-- A lens changes the interface through the shared reindexing operation. -/
example {I : Type uI} {P : Endo.{uI, uA, uB} I} {Q : Endo.{uI, uC, uD} I}
    {X : I → Type uX} {s : I} (l : Lens P Q) (x : IFreeM P X s) :
    x.mapLens l = x.reindex l.toReindexing (fun _ value => value) := rfl

end PolyFunTest.ModuleAPI.IndexedBoundTransport
