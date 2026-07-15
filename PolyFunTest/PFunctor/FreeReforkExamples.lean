/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Refork

/-! # Free-program reforking examples -/

@[expose] public section

open PFunctor

namespace PFunctor.FreeM.Path

/-- A query signature with two positions and a unique answer at each. -/
abbrev ReforkQuery : PFunctor := ⟨Bool, fun _ => Unit⟩

/-- A program whose `false` occurrences surround one `true` occurrence. -/
def reforkProgram : FreeM ReforkQuery Nat :=
  FreeM.liftBind false fun _ =>
    FreeM.liftBind true fun _ =>
      FreeM.liftBind false fun _ => pure 7

/-- The unique complete path through `reforkProgram`. -/
def reforkPath : Path reforkProgram :=
  ⟨(), ⟨(), ⟨(), ⟨⟩⟩⟩⟩

example : (locateAt? false reforkProgram reforkPath 1).isSome := by
  rw [locateAt?_isSome_iff_lt_occurrences]
  decide

example : locateAt? false reforkProgram reforkPath 2 = none := rfl

example : forkAt false reforkProgram 1 = reforkAt false reforkProgram 1 :=
  forkAt_eq_reforkAt false reforkProgram 1

example : FreeM ReforkQuery
    (Option (SelectedForkView false reforkProgram Unit fun _ => 1)) :=
  reforkSelected false reforkProgram (fun _ => some ()) (fun _ => 1)

example : FreeM ReforkQuery (Option (Nat × Nat)) :=
  filterMapReforkAt false reforkProgram 1 fun view =>
    some (output reforkProgram view.firstPath,
      output reforkProgram view.secondPath)

end PFunctor.FreeM.Path
