/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import PolyFun.PFunctor.Handler.CertifiedVec

/-!
# Certified handlers over allowed answers

`PolyFun.PFunctor.Handler.Certified` certifies a handler on every branch of its implementations.
This file certifies a handler on the branches selected by answer relations `allowsP` on the
source interface and `allowsQ` on the target interface.

* A restricted budget pushes forward along a monotone additive map
  (`FreeM.IsChargeBoundUnder.map`).
* A `Handler.CertifiedUnder` has an exchange, a bound of each implementation over `allowsQ` by the
  exchanged price, and the side condition that each implementation returns, along `allowsQ`,
  only answers that `allowsP` allows.
* A budget over `allowsP` transfers to a budget over `allowsQ` (`CertifiedUnder.transfer`), and
  these handlers compose (`CertifiedUnder.comp`). The side condition of a composite follows from
  the fold of a demonic postcondition over a substituted program
  (`FreeM.wpFold_demonicUnder_liftM`).
* With the demand map of `PolyFun.PFunctor.Handler.CertifiedVec` as exchange, a use vector `u`
  over `allowsP` gives the use vector `∑ i, u i • d i` over `allowsQ`
  (`Handler.isChargeBoundUnder_liftM_demand`). With every answer allowed this is
  `Handler.isChargeBound_liftM_demand`.
-/

@[expose] public section

universe uA uA₂ uA₃ uB uB₂ uB₃ v w w' w''

open scoped BigOperators

namespace PFunctor

namespace FreeM

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {α : Type v}

/-- A postcondition that holds at every result holds under the demonic fold, whatever answers are
allowed. -/
theorem wpFold_demonicUnder_of_forall (allows : (a : P.A) → P.B a → Prop) {post : α → Prop}
    (h : ∀ r, post r) (x : FreeM P α) : wpFold (OpSpec.demonicUnder allows) x post := by
  induction x with
  | pure r => exact h r
  | lift_bind a r ih => exact fun b _ => ih b

/-- **A demonic postcondition through a handler.** If every result each implementation can return
along `allowsQ` is allowed by `allows`, a postcondition of `x` along `allows` is a postcondition of
the simulated program along `allowsQ`. -/
theorem wpFold_demonicUnder_liftM {γ : Type uB} {allows : (a : P.A) → P.B a → Prop}
    {allowsQ : (q : Q.A) → Q.B q → Prop} (handler : (a : P.A) → FreeM Q (P.B a))
    (hout : ∀ a, wpFold (OpSpec.demonicUnder allowsQ) (handler a) (allows a))
    {x : FreeM P γ} {post : γ → Prop} (hx : wpFold (OpSpec.demonicUnder allows) x post) :
    wpFold (OpSpec.demonicUnder allowsQ) (x.liftM handler) post := by
  rw [wpFold_liftM]
  induction x with
  | pure r => exact hx
  | lift_bind a r ih =>
    exact wpFold_mono (OpSpec.demonicUnder_mono allowsQ) (handler a)
      (fun b hb => ih b (hx b hb)) (hout a)

section Transport

variable {ω : Type w} {ω' : Type w'} [AddZeroClass ω] [Preorder ω] [AddZeroClass ω'] [Preorder ω']

/-- Restricted charge bounds push forward along monotone additive maps. -/
theorem IsChargeBoundUnder.map {c : P.A → ω} {allows : (a : P.A) → P.B a → Prop} {B s : ω}
    {x : FreeM P α} (φ : ω →+o ω') (h : IsChargeBoundUnder x c allows B s) :
    IsChargeBoundUnder x (φ ∘ c) allows (φ B) (φ s) :=
  (isChargeBoundUnder_iff_restrict x).2 (((isChargeBoundUnder_iff_restrict x).1 h).map φ)

end Transport

end FreeM

namespace Handler

variable {ω : Type w} {ω' : Type w'} {ω'' : Type w''}

section CertifiedUnder

variable [AddMonoid ω] [Preorder ω] [AddMonoid ω'] [Preorder ω'] [AddMonoid ω''] [Preorder ω'']

/-- A handler implementing `P` by programs over `Q`, certified over allowed answers: with an
exchange of prices, each call at `a` stays within its exchanged price along the answers `allowsQ`
allows, and every result it can return along them is allowed by `allowsP`. -/
structure CertifiedUnder (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB₂}) (c : P.A → ω)
    (allowsP : (a : P.A) → P.B a → Prop) (d : Q.A → ω')
    (allowsQ : (q : Q.A) → Q.B q → Prop) where
  /-- The implementation of each call. -/
  handler : Handler (FreeM Q) P
  /-- The conversion of prices from `P`'s layer to `Q`'s. -/
  exchange : ω →+o ω'
  /-- Each call stays within its exchanged price along the allowed answers of `Q`. -/
  certificate : ∀ a, (handler a).IsChargeBoundUnder d allowsQ (exchange (c a))
  /-- Each call returns, along the allowed answers of `Q`, only allowed answers of `P`. -/
  allowed : ∀ a, FreeM.wpFold (OpSpec.demonicUnder allowsQ) (handler a) (allowsP a)

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- A certified handler is certified over any allowed answers of its target, with every answer of
its source allowed. -/
def Certified.toUnder {c : P.A → ω} {d : Q.A → ω'} (f : Certified P Q c d)
    (allowsQ : (q : Q.A) → Q.B q → Prop) : CertifiedUnder P Q c (fun _ _ => True) d allowsQ where
  handler := f.handler
  exchange := f.exchange
  certificate a := (f.certificate a).under allowsQ
  allowed a := FreeM.wpFold_demonicUnder_of_forall allowsQ (fun _ => trivial) (f.handler a)

namespace CertifiedUnder

/-- The identity handler, certified over any allowed answers by the identity exchange. -/
def id (P : PFunctor.{uA, uB}) (c : P.A → ω) (allows : (a : P.A) → P.B a → Prop) :
    CertifiedUnder P P c allows c allows where
  handler := Handler.id P
  exchange := OrderAddMonoidHom.id ω
  certificate a := (FreeM.isChargeBoundUnder_lift_iff a).2 (by rw [zero_add]; exact le_rfl)
  allowed _ := fun _ hb => hb

/-- Certified handlers over allowed answers compose: implement by `f`, then implement `f`'s target
by `g`, exchanging prices through both. -/
def comp [AddLeftMono ω''] [AddRightMono ω''] {Q : PFunctor.{uA₂, uB}} {c : P.A → ω}
    {allowsP : (a : P.A) → P.B a → Prop} {d : Q.A → ω'} {allowsQ : (q : Q.A) → Q.B q → Prop}
    {e : R.A → ω''} {allowsR : (r : R.A) → R.B r → Prop}
    (g : CertifiedUnder Q R d allowsQ e allowsR) (f : CertifiedUnder P Q c allowsP d allowsQ) :
    CertifiedUnder P R c allowsP e allowsR where
  handler := g.handler.comp f.handler
  exchange := g.exchange.comp f.exchange
  certificate a := by
    have h := (f.certificate a).map g.exchange
    rw [map_zero] at h
    exact h.liftM g.handler g.certificate g.allowed
  allowed a := FreeM.wpFold_demonicUnder_liftM g.handler g.allowed (f.allowed a)

/-- **Transfer over allowed answers.** A program within budget `B` along `allowsP`, simulated
through a handler certified over `allowsP` and `allowsQ`, is within the exchanged budget along
`allowsQ`. -/
theorem transfer [AddLeftMono ω'] [AddRightMono ω'] {c : P.A → ω}
    {allowsP : (a : P.A) → P.B a → Prop} {d : Q.A → ω'} {allowsQ : (q : Q.A) → Q.B q → Prop}
    (f : CertifiedUnder P Q c allowsP d allowsQ) {α : Type uB} {x : FreeM P α} {B s : ω}
    (hx : x.IsChargeBoundUnder c allowsP B s) :
    (x.liftM f.handler).IsChargeBoundUnder d allowsQ (f.exchange B) (f.exchange s) :=
  (hx.map f.exchange).liftM f.handler f.certificate f.allowed

end CertifiedUnder

end CertifiedUnder

/-! ## Handlers certified by demands over allowed answers -/

section Demand

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}} {ι ι' : Type*} [Fintype ι]
  [CommSemiring ω] [PartialOrder ω] [IsOrderedRing ω] {α : Type uB}

/-- A handler whose implementation of each call at `a` has use vector at most
`∑ i, c a i • d i` along `allowsQ`, and which returns only answers allowed by `allowsP`, certified
over allowed answers with the demand map of `d` as its exchange. -/
def CertifiedUnder.ofDemand {c : P.A → ι → ω} {allowsP : (a : P.A) → P.B a → Prop}
    {e : Q.A → ι' → ω} {allowsQ : (q : Q.A) → Q.B q → Prop} (h : Handler (FreeM Q) P)
    (d : ι → ι' → ω) (hd : 0 ≤ d)
    (hh : ∀ a, (h a).IsChargeBoundUnder e allowsQ (∑ i, c a i • d i))
    (hout : ∀ a, FreeM.wpFold (OpSpec.demonicUnder allowsQ) (h a) (allowsP a)) :
    CertifiedUnder P Q c allowsP e allowsQ :=
  ⟨h, demandHom d hd, hh, hout⟩

/-- **Use bounds through a handler, over allowed answers.** If `x` has use vector `u` along
`allowsP`, each call at `a` is implemented with use vector `∑ i, c a i • d i` along `allowsQ`, and
every result it can return along `allowsQ` is allowed by `allowsP`, then `x.liftM h` has use vector
`∑ i, u i • d i` along `allowsQ`. -/
theorem isChargeBoundUnder_liftM_demand {c : P.A → ι → ω} {allowsP : (a : P.A) → P.B a → Prop}
    {e : Q.A → ι' → ω} {allowsQ : (q : Q.A) → Q.B q → Prop} {h : Handler (FreeM Q) P}
    {d : ι → ι' → ω} (hd : 0 ≤ d)
    (hh : ∀ a, (h a).IsChargeBoundUnder e allowsQ (∑ i, c a i • d i))
    (hout : ∀ a, FreeM.wpFold (OpSpec.demonicUnder allowsQ) (h a) (allowsP a))
    {x : FreeM P α} {u : ι → ω} (hx : x.IsChargeBoundUnder c allowsP u) :
    (x.liftM h).IsChargeBoundUnder e allowsQ (∑ i, u i • d i) := by
  have := (CertifiedUnder.ofDemand h d hd hh hout).transfer hx
  rwa [map_zero] at this

end Demand

end Handler

end PFunctor
