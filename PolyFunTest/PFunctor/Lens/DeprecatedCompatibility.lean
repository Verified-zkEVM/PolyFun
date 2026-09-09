/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# Direct-import compatibility for the former `X` lens API

These canaries import only `PFunctor.Lens.Basic`. They ensure downstream files
using the former `X` spellings keep elaborating without relying on the aggregate
`PFunctor.Deprecated` module or the `PolyFun` umbrella.
-/

@[expose] public section

open scoped PFunctor

namespace PFunctor.Lens

/--
warning: `PFunctor.X` has been deprecated: Use `PFunctor.y` instead
---
warning: `PFunctor.Lens.fromX` has been deprecated: Use `PFunctor.Lens.fromY` instead
-/
#guard_msgs in
example {P : PFunctor.{0, 0}} (a : P.A) : Lens X P := fromX a

/--
warning: `PFunctor.X` has been deprecated: Use `PFunctor.y` instead
---
warning: `PFunctor.Lens.Equiv.compX` has been deprecated: Use `PFunctor.Lens.Equiv.compY` instead
-/
#guard_msgs in
example {P : PFunctor.{0, 0}} : Lens.Equiv (P ◃ X) P := Lens.Equiv.compX

end PFunctor.Lens
