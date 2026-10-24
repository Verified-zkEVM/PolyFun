/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.Declarations
public import PolyFunCryptol.Model.PolyExamples

import all PolyFunCryptol.Model.Reference.Syntax
import all PolyFunCryptol.Model.Types
import all PolyFunCryptol.Model.Scheme

/-! # Ordered module contexts and lazy declaration groups -/

public section

namespace Cryptol.Tests.Declarations

open Polymorphic Translation

/-- First declaration identity. -/
@[expose] def x : Reference.Name := ⟨1, "x", "x"⟩
/-- Second declaration identity. -/
@[expose] def y : Reference.Name := ⟨2, "y", "y"⟩
/-- A closed bit-valued declaration. -/
@[expose] def schema : Reference.Schema := ⟨[], [], .constructor "TC TCBit" []⟩

-- A nonrecursive right-hand side cannot see its own binding.
example : (OpenElaboration.declarations 10 (w := Scope.empty) ⟨[], []⟩ []
    [.nonrecursive (.mk x schema (.expression (.var x)))]).toOption.isSome = false := rfl

-- Nor can it see a later declaration, even if both schemes are known.
example : (OpenElaboration.declarations 10 (w := Scope.empty) ⟨[], []⟩ []
    [.nonrecursive (.mk x schema (.expression (.var y))),
     .nonrecursive (.mk y schema (.expression (.var x)))]).toOption.isSome = false := rfl

-- A recursive group does provide simultaneous scope to all its members.
example : (OpenElaboration.declarations 10 (w := Scope.empty) ⟨[], []⟩ []
    [.recursive [.mk x schema (.expression (.var y)),
      .mk y schema (.expression (.var x))]]).toOption.isSome = true := by with_unfolding_all rfl

/-- A diverging group followed by an independent constant. -/
@[expose] def lazyGroup : Translation.Declarations Scope.empty []
    [(y, .mono .bit), (x, .mono .bit)] :=
  .recursive [(x, .mono .bit)] (Fin.cases (.var .zero) (fun i => nomatch i))
    (.nonrecursive y (.mono .bit) (.bit true) (.nil _))

-- An unproductive recursive binding does not prevent a later constant from being observed.
/-- Divergence in an unused binding does not force the next declaration. -/
theorem unused_recursion_is_lazy :
    lazyGroup.denote emptyAssignment (Env.empty _) (.mono .bit) .zero =
    DomainResult.value ⟨true⟩ := rfl

-- The finite exported syntax has exactly the environment interpreter's behavior.
example : (lazyGroup.close (Term.var .zero)).denote emptyAssignment (Env.empty _) =
    DomainResult.value ⟨true⟩ := by
  rw [Translation.Declarations.denote_close]
  rfl

end Cryptol.Tests.Declarations
