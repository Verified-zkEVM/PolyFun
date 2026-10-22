/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Direct-import compatibility for deprecated lens APIs

These canaries import only `PFunctor.Lens.Basic`. They ensure downstream files
using deprecated lens spellings keep elaborating without relying on the aggregate
`PFunctor.Deprecated` module or the `PolyFun` umbrella, and preserve the
independent universes of `Lens.enclose`.
-/

@[expose] public section

open scoped PFunctor

namespace PFunctor.Lens

set_option linter.deprecated false

universe uA uB uA₁ uB₁

-- Old universe arity and import surface: only Lens.Basic is imported.
example (P : PFunctor.{uA, uB}) (l : Lens P y.{uA₁, uB₁}) :
    enclose.{uA, uB, uA₁, uB₁} P := l

-- Old explicit unfolding at independent endpoint universes.
example (P : PFunctor.{uA, uB}) :
    enclose.{uA, uB, uA₁, uB₁} P = Lens P y.{uA₁, uB₁} := by
  unfold enclose
  rfl

end PFunctor.Lens
