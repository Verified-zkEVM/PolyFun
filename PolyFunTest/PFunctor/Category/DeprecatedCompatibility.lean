/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Category

/-!
# Direct-import compatibility for the former `as` projections

The deprecated `LensCat.as` and `ChartCat.as` stay reducible, so instance search still sees the
underlying polynomial through them, as it did when `as` was an abbreviation.
-/

@[expose] public section

namespace PFunctor

set_option linter.deprecated false in
example : Unique ((LensCat.of (y : PFunctor.{0, 0})).as.A) := inferInstance

set_option linter.deprecated false in
example : Unique ((ChartCat.of (y : PFunctor.{0, 0})).as.A) := inferInstance

end PFunctor
