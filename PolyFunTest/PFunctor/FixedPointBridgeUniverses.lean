/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Cofree
public import PolyFun.PFunctor.Handler
public import PolyFun.PFunctor.M.WellFounded

/-! # Universe canaries for fixed-point bridge infrastructure -/

@[expose] public section

universe uA uB uA₂ uB₂ uα uM uN

namespace PFunctor.FixedPointBridgeUniverseCanaries

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}
  {α : Type uα}

/-- W-tree lens transport keeps source and target polynomial universes
independent. -/
example (lens : Lens P Q) (tree : P.W) : Q.W :=
  W.mapLens lens tree

/-- Cofree lens transport keeps labels independent from both source and target
polynomial universes. -/
example (lens : Lens P Q) (tree : CofreeC P α) : CofreeC Q α :=
  CofreeC.mapLens lens tree

/-- Handler target changes may alter the output universe without coupling it
to the handled polynomial's position universe. -/
example {m : Type uB → Type uM} {n : Type uB → Type uN}
    (transform : ∀ {β : Type uB}, m β → n β)
    (handler : Handler m P) (position : P.A) :
    Handler.mapTarget transform handler position =
      transform (handler position) :=
  rfl

end PFunctor.FixedPointBridgeUniverseCanaries
