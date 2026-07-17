/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Free

/-!
# Displayed handlers between polynomial interfaces

This file supplies the display-level counterpart of a free-monad handler. If

```text
f : (a : P.A) → FreeM Q (P.B a)
```

implements every operation of `P` as a `Q`-program, then
`Display.Handler S T f` implements every displayed position of `S` as
displayed data over that program, using the target display `T`.

This is the intrinsic PolyFun form of the paper's dependent-polynomial
morphism. It is named after the existing `FreeM.liftM` handler API rather than
introducing a paper-specific arrow alias. `mapHandler` is its free extension,
and `Handler.comp` is displayed Kleisli composition.
-/

@[expose] public section

universe uA uA' uA'' uB uC uD uC' uD' uC'' uD'' uF

namespace PFunctor
namespace Display

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA', uB}}
  {R : PFunctor.{uA'', uB}}

/-- A displayed implementation of a free-monad handler. -/
abbrev Handler
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Q)
    (f : (a : P.A) → FreeM Q (P.B a)) :=
  (a : P.A) → (c : S.position a) →
    FreeM.Displayed (T.toDisplayedShape (S.direction a c)) (f a)

/-- Extend a displayed handler recursively over a free source program. This
maps the base tree with `FreeM.liftM` and its displayed data in lockstep. -/
def mapHandler
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Q)
    {E : Type uB} {F : E → Type uF}
    (t : FreeM P E)
    (d : FreeM.Displayed (S.toDisplayedShape F) t)
    (f : (a : P.A) → FreeM Q (P.B a))
    (df : Handler S T f) :
    FreeM.Displayed (T.toDisplayedShape F) (t.liftM f) :=
  match t, d with
  | .pure x, d => T.leaf F x d.down
  | .liftBind a rest, ⟨c, children⟩ =>
      T.bind (f a) (df a c) (fun b => (rest b).liftM f)
        (fun b e => S.mapHandler T (rest b) (children b e) f df)

@[simp]
theorem mapHandler_pure
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Q)
    {E : Type uB} {F : E → Type uF}
    (x : E) (d : ULift.{max uC uB uD} (F x))
    (f : (a : P.A) → FreeM Q (P.B a)) (df : Handler S T f) :
    S.mapHandler T (pure x) d f df = T.leaf F x d.down :=
  rfl

@[simp]
theorem mapHandler_liftBind
    (S : Display.{uA, uB, uC, uD} P)
    (T : Display.{uA', uB, uC', uD'} Q)
    {E : Type uB} {F : E → Type uF}
    (a : P.A) (rest : P.B a → FreeM P E) (c : S.position a)
    (children : (b : P.B a) → S.direction a c b →
      FreeM.Displayed (S.toDisplayedShape F) (rest b))
    (f : (a : P.A) → FreeM Q (P.B a)) (df : Handler S T f) :
    S.mapHandler T (FreeM.lift a >>= rest) ⟨c, children⟩ f df =
      T.bind (f a) (df a c) (fun b => (rest b).liftM f)
        (fun b e => S.mapHandler T (rest b) (children b e) f df) :=
  rfl

namespace Handler

/-- Displayed Kleisli composition of handlers. -/
def comp
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB, uC', uD'} Q}
    {U : Display.{uA'', uB, uC'', uD''} R}
    {f : (a : P.A) → FreeM Q (P.B a)}
    {g : (a : Q.A) → FreeM R (Q.B a)}
    (df : Handler S T f) (dg : Handler T U g) :
    Handler S U (fun a => (f a).liftM g) :=
  fun a c => T.mapHandler U (f a) (df a c) g dg

@[simp]
theorem comp_apply
    {S : Display.{uA, uB, uC, uD} P}
    {T : Display.{uA', uB, uC', uD'} Q}
    {U : Display.{uA'', uB, uC'', uD''} R}
    {f : (a : P.A) → FreeM Q (P.B a)}
    {g : (a : Q.A) → FreeM R (Q.B a)}
    (df : Handler S T f) (dg : Handler T U g)
    (a : P.A) (c : S.position a) :
    comp df dg a c = T.mapHandler U (f a) (df a c) g dg :=
  rfl

end Handler
end Display
end PFunctor
