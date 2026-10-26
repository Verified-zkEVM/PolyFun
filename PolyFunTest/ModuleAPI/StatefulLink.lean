/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Stateful.Link

/-!
# Ordinary-import canaries for stateful package composition

VCVio's state-separating `QueryImpl.Stateful.link` and `parSum` are `Handler.Stateful.link` and
`sumMap` on oracle interfaces. These examples check through ordinary imports that the one-step
equations hold by `rfl`, and that associativity, the unit laws and interchange hold when every
interface has its own position universe.
-/

@[expose] public section

universe u v uE uE₁ uE₂ uM uM₁ uM₂ uI uI₁ uI₂

namespace PolyFunTest.ModuleAPI.StatefulLink

open _root_.PFunctor Handler.Stateful

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {S T U S₁ S₂ T₁ T₂ : Type u}
variable {E : PFunctor.{uE, u}} {M : PFunctor.{uM, u}} {I : PFunctor.{uI, u}}
variable {E₁ : PFunctor.{uE₁, u}} {E₂ : PFunctor.{uE₂, u}}
variable {M₁ : PFunctor.{uM₁, u}} {M₂ : PFunctor.{uM₂, u}}
variable {I₁ : PFunctor.{uI₁, u}} {I₂ : PFunctor.{uI₂, u}}

example (outer : Handler.Stateful (FreeM M) S E) (inner : Handler.Stateful m T M) (a : E.A)
    (s : S) (t : T) :
    (outer.link inner a).run (s, t) =
      (fun r : (E.B a × S) × T => (r.1.1, (r.1.2, r.2))) <$> inner.run ((outer a).run s) t :=
  rfl

example (a : Handler.Stateful (FreeM M) S E) (b : Handler.Stateful (FreeM I) T M)
    (c : Handler.Stateful m U I) :
    (a.link b).link c = stateCongr (Equiv.prodAssoc S T U).symm (a.link (b.link c)) :=
  link_assoc a b c

example (a : Handler.Stateful (FreeM M) S E) :
    a.link (lift (S := PUnit.{u + 1}) (Handler.id M)) = stateCongr (Equiv.prodPUnit S).symm a :=
  link_lift_id a

example (a : Handler.Stateful m S E) :
    (lift (S := PUnit.{u + 1}) (Handler.id E)).link a = stateCongr (Equiv.punitProd S).symm a :=
  lift_id_link a

example (o₁ : Handler.Stateful (FreeM M₁) S₁ E₁) (o₂ : Handler.Stateful (FreeM M₂) S₂ E₂)
    (i₁ : Handler.Stateful m T₁ M₁) (i₂ : Handler.Stateful m T₂ M₂) :
    (sumMap o₁ o₂).link (sum i₁ i₂) =
      stateCongr (Equiv.prodProdProdComm S₁ T₁ S₂ T₂) (sum (o₁.link i₁) (o₂.link i₂)) :=
  sumMap_link_sum o₁ o₂ i₁ i₂

example (o₁ : Handler.Stateful (FreeM M₁) S₁ E₁) (o₂ : Handler.Stateful (FreeM M₂) S₂ E₂)
    (i₁ : Handler.Stateful (FreeM I₁) T₁ M₁) (i₂ : Handler.Stateful (FreeM I₂) T₂ M₂) :
    (sumMap o₁ o₂).link (sumMap i₁ i₂) =
      stateCongr (Equiv.prodProdProdComm S₁ T₁ S₂ T₂) (sumMap (o₁.link i₁) (o₂.link i₂)) :=
  sumMap_link_sumMap o₁ o₂ i₁ i₂

example (impl : Handler (FreeM M) E) (h : Handler.Stateful m S M) :
    h.reindex impl = stateCongr (Equiv.punitProd S) ((lift (S := PUnit.{u + 1}) impl).link h) :=
  reindex_eq_link impl h

example (l : Lens E M) {α : Type u} (x : FreeM E α) :
    x.liftM (Handler.ofLens l) = x.mapLens l :=
  Handler.liftM_ofLens l x

end PolyFunTest.ModuleAPI.StatefulLink
