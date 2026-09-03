/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Do

/-!
# Handler-relative weakest preconditions of free programs

Interpreting through a handler installs the target monad's core interpretation on `FreeM P`
along the fold: the resulting `wp` follows the handler, so it proves facts the demonic
all-responses reading cannot.
-/

@[expose] public section

set_option mvcgen.warning false

namespace PolyFunTest.DoTransport

open Std.Internal.Do PFunctor

abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

def flipTwo : FreeM coinP Bool := do
  let a ← FreeM.lift (P := coinP) PUnit.unit
  let b ← FreeM.lift (P := coinP) PUnit.unit
  pure (a && b)

/-- A nonidentity handler: interpret every free query as `true` in `Id`. -/
def chooseTrue : Handler Id coinP :=
  fun _ => true

local instance instHandlerWP : WPMonad (FreeM coinP) Prop EPost.Nil :=
  FreeM.wpMonadOfHandler chooseTrue

/-- The transported `wp` is the handler's, definitionally. -/
example (post : Bool → Prop) :
    wp flipTwo post Lean.Order.bot = wp (flipTwo.liftM chooseTrue) post Lean.Order.bot :=
  rfl

/-- A handler-specific fact that the demonic semantics cannot prove. -/
example : ⦃ True ⦄ flipTwo ⦃ fun result => result = true ⦄ := by
  refine ⟨fun _ => ?_⟩
  change (true && true) = true
  rfl

end PolyFunTest.DoTransport
