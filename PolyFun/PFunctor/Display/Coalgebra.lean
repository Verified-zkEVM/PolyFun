/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module


public import PolyFun.PFunctor.Display.Basic

/-!
# Coalgebras over polynomial displays

A display `S : PFunctor.Display P` refines one layer of the polynomial
extension `P.Obj`. Given a base coalgebra map `step : C → P.Obj C` and a
proof-relevant family `F : C → Type`, a `Display.Coalgebra S step F` preserves
one current witness `F c` through the displayed refinement of `step c`.

The definition is the raw dependent function type

```text
(c : C) → F c → S.Obj F (step c).
```

It is intentionally an `abbrev`, rather than a structure duplicating the
underlying coalgebra or dynamical system. In particular, for
`R : DynSystem C P`, the displayed coalgebra is written directly as
`Display.Coalgebra S R.out F`.
-/

@[expose] public section

universe uA uB uC uD uE uF

namespace PFunctor
namespace Display

variable {P : PFunctor.{uA, uB}}

/-- A proof-relevant coalgebra over a displayed polynomial layer.

For each base state `c` and current witness `F c`, the result chooses displayed
position data for `step c` and recursively supplies witnesses over all
displayed directions. -/
abbrev Coalgebra (S : Display.{uA, uB, uC, uD} P)
    {C : Type uE} (step : C → P.Obj C) (F : C → Type uF) :
    Type (max uE uF uC uD uB) :=
  (c : C) → F c → S.Obj F (step c)

end Display
end PFunctor
