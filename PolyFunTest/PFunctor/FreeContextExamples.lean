/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Context

/-! # Typed free-program context examples -/

@[expose] public section

open PFunctor

namespace PFunctor.FreeM.Path

/-- A query signature with two positions and a unique answer at each. -/
abbrev ContextQuery : PFunctor := ⟨Bool, fun _ => Unit⟩

/-- A program whose `false` occurrences surround one `true` occurrence. -/
def contextProgram : FreeM ContextQuery Nat :=
  FreeM.liftBind false fun _ =>
    FreeM.liftBind true fun _ =>
      FreeM.liftBind false fun _ => pure 7

example : FreeM ContextQuery
    {result : Split false contextProgram 1 // result.Valid} :=
  splitAtValid false contextProgram 1

example :
    FreeM.bind (splitAtValid false contextProgram 1)
        (fun result => result.val.complete) =
      withPath contextProgram :=
  splitAtValid_bind_complete false contextProgram 1

example : forkAt false contextProgram 1 =
    FreeM.bind (splitAtValid false contextProgram 1)
      (fun result => result.val.completeFork) :=
  (splitAtValid_bind_completeFork false contextProgram 1).symm

end PFunctor.FreeM.Path
