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
using the former `X` spellings keep elaborating without relying on the aggregate
`PFunctor.Deprecated` module or the `PolyFun` umbrella.
The section canaries preserve the independent universes of `Lens.enclose`.
-/

@[expose] public section

open scoped PFunctor

namespace PFunctor.Lens

/--
warning: `PFunctor.X` has been deprecated: Use `PFunctor.y` instead

Hint: Replace the deprecated name:
  X̵y̲
---
warning: `PFunctor.Lens.fromX` has been deprecated: Use `PFunctor.Lens.fromY` instead

Hint: Replace the deprecated name:
  fromX̵Y̲
-/
#guard_msgs in
example {P : PFunctor.{0, 0}} (a : P.A) : Lens X P := fromX a

/--
warning: `PFunctor.X` has been deprecated: Use `PFunctor.y` instead

Hint: Replace the deprecated name:
  X̵y̲
---
warning: `PFunctor.Lens.Equiv.compX` has been deprecated: Use `PFunctor.Lens.Equiv.compY` instead

Hint: Replace the deprecated name:
  L̵e̵n̵s̵.̵E̵q̵u̵i̵v̵.̵c̵o̵m̵p̵X̵E̲q̲u̲i̲v̲.̲c̲o̲m̲p̲Y̲
-/
#guard_msgs in
example {P : PFunctor.{0, 0}} : Lens.Equiv (P ◃ X) P := Lens.Equiv.compX

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
