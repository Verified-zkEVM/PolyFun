/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Do

/-!
# Nonidentity `Std.Do` transport canary

This test installs handler-transported weakest-precondition semantics without
opening the demonic scope. It ensures that transport follows the handler rather
than silently selecting the free monad's all-responses interpretation.
-/

@[expose] public section

namespace PolyFunTest.DoTransport

open Std.Do
open PFunctor

abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

def flipTwo : FreeM coinP Bool := do
  let a ← FreeM.lift (P := coinP) PUnit.unit
  let b ← FreeM.lift (P := coinP) PUnit.unit
  pure (a && b)

/-- A nonidentity monad morphism: interpret every free query as `true` in `Id`. -/
def chooseTrue : Handler Id coinP :=
  fun _ => true

local instance instHandlerWP : WPMonad (FreeM coinP) .pure :=
  FreeM.wpMonadOfHandler chooseTrue

/-- The transported WP proves a handler-specific fact that the demonic
all-responses semantics cannot prove. -/
example : ⦃⌜True⌝⦄ flipTwo ⦃⇓ result => ⌜result = true⌝⦄ := by
  change True → true && true = true
  intro
  rfl

end PolyFunTest.DoTransport
