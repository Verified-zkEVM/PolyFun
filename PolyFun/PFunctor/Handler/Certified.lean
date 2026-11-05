/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Charge

/-!
# Certified handlers

A layer of cost accounting is an interface with a charge: `P` priced by `c : P.A → ω`. An
implementation of `P` one layer down, by programs over `Q` priced by `d : Q.A → ω'`, is
*certified* when it comes with an **exchange** `E : ω →+o ω'` that converts prices between the
layers, and every call at `a` is implemented within `E (c a)` (`Handler.Certified`).

* A bound transfers along a certified handler: a program within `B` is simulated within `E B`
  (`Certified.transfer`), and in value form a simulated program costs at most `E` of the
  original's cost (`Certified.cost_liftM_le`).
* Certified handlers compose, composing their exchanges (`Certified.comp`), and the identity
  handler is certified by the identity exchange (`Certified.id`). Certificates therefore chain
  along the cross-layer links of a cost argument: a specification implemented by an algorithm,
  the algorithm compiled to instructions, and so on.
* A reduction runs a setup program, then the source program through a certified handler, then a
  finishing program; the handler and the finishing program may use the setup's result, such as
  keys or tables. Its bound is affine in the source budget, `setupCost + E B + finishCost`
  (`CostedReduction.run_isChargeBound`).

The exchange is monotone and additive, so it handles changes of unit (one hash is `k`
compressions), changes of cost type (per-kind counts to weighted totals) and the identity. Costs
that are not additive across a layer, such as a cache answering repeated calls, are handled by the
amortized transfer of `PolyFun.PFunctor.Handler.Charge`.
-/

@[expose] public section

universe uA uA₂ uA₃ uB w w' w''

namespace PFunctor

namespace Handler

variable {ω : Type w} {ω' : Type w'} {ω'' : Type w''}

section Certified

variable [AddCommMonoid ω] [PartialOrder ω] [AddCommMonoid ω'] [PartialOrder ω']
  [AddCommMonoid ω''] [PartialOrder ω'']

/-- A handler implementing `P` by programs over `Q`, with an exchange from `P`'s prices to `Q`'s
under which each call at `a` is implemented within `exchange (c a)`. -/
structure Certified (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB}) (c : P.A → ω)
    (d : Q.A → ω') where
  /-- The implementation of each call. -/
  handler : Handler (FreeM Q) P
  /-- The conversion of prices from `P`'s layer to `Q`'s. -/
  exchange : ω →+o ω'
  /-- Each call is implemented within its exchanged price. -/
  certificate : handler.WithinCharge d (exchange ∘ c)

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}

namespace Certified

/-- The identity handler, certified by the identity exchange. -/
def id (P : PFunctor.{uA, uB}) (c : P.A → ω) : Certified P P c c where
  handler := Handler.id P
  exchange := OrderAddMonoidHom.id ω
  certificate := withinCharge_id c

/-- Certified handlers compose: implement by `f`, then implement `f`'s target by `g`, exchanging
prices through both. -/
def comp [IsOrderedAddMonoid ω''] {c : P.A → ω} {d : Q.A → ω'} {e : R.A → ω''}
    (g : Certified Q R d e) (f : Certified P Q c d) : Certified P R c e where
  handler := g.handler.comp f.handler
  exchange := g.exchange.comp f.exchange
  certificate a := by
    have h := (f.certificate a).map g.exchange
    rw [map_zero] at h
    exact h.liftM g.handler g.certificate

@[simp]
theorem comp_exchange [IsOrderedAddMonoid ω''] {c : P.A → ω} {d : Q.A → ω'} {e : R.A → ω''}
    (g : Certified Q R d e) (f : Certified P Q c d) :
    (g.comp f).exchange = g.exchange.comp f.exchange :=
  rfl

/-- **Transfer.** A program within budget `B`, simulated through a certified handler, is within the
exchanged budget. -/
theorem transfer [IsOrderedAddMonoid ω'] {c : P.A → ω} {d : Q.A → ω'} (f : Certified P Q c d)
    {α : Type uB} {x : FreeM P α} {B s : ω} (hx : x.IsChargeBound c B s) :
    (x.liftM f.handler).IsChargeBound d (f.exchange B) (f.exchange s) :=
  (hx.map f.exchange).liftM f.handler f.certificate

end Certified

end Certified

section Value

variable [AddCommMonoid ω] [CompleteLattice ω] [AddCommMonoid ω'] [CompleteLattice ω']
  [IsOrderedAddMonoid ω'] [CanonicallyOrderedAdd ω'] [AddSupDistrib ω']
  {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB}}

/-- **Transfer, value form.** A program simulated through a certified handler costs at most the
exchange of the original's worst-case cost. -/
theorem Certified.cost_liftM_le {c : P.A → ω} {d : Q.A → ω'} (f : Certified P Q c d)
    {α : Type uB} (x : FreeM P α) :
    FreeM.cost d (x.liftM f.handler) ≤ f.exchange (FreeM.cost c x) := by
  refine (FreeM.cost_liftM_le d f.handler x).trans
    ((FreeM.cost_mono_charge (fun a => ?_) x).trans (FreeM.cost_comp_le f.exchange c x))
  have h := FreeM.cost_le_of_isChargeBound (f.certificate a)
  rw [zero_add] at h
  exact h

end Value

section Reduction

variable [AddCommMonoid ω] [PartialOrder ω] [AddCommMonoid ω'] [PartialOrder ω']
  [IsOrderedAddMonoid ω'] [CanonicallyOrderedAdd ω']
  {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB}}

/-- A reduction from a `P`-program to a `Q`-program: run `setup`, then the source program through
an implementation certified with one exchange, then `finish` on its result. The implementation and
`finish` may use the result of `setup`. Each of the two extra stages has a budget. -/
structure CostedReduction (P : PFunctor.{uA, uB}) (Q : PFunctor.{uA₂, uB}) (c : P.A → ω)
    (d : Q.A → ω') (σ α β : Type uB) where
  /-- Work before running the source program, producing data for the later stages. -/
  setup : FreeM Q σ
  /-- The implementation of the source calls, given the result of `setup`. -/
  handler : σ → Handler (FreeM Q) P
  /-- The conversion of prices from `P`'s layer to `Q`'s, the same for every setup result. -/
  exchange : ω →+o ω'
  /-- Each call is implemented within its exchanged price, whatever `setup` returned. -/
  certificate : ∀ k, (handler k).WithinCharge d (exchange ∘ c)
  /-- Work after the source program returns, given the result of `setup`. -/
  finish : σ → α → FreeM Q β
  /-- The budget of `setup`. -/
  setupCost : ω'
  /-- The budget of `finish`, uniform in the setup and source results. -/
  finishCost : ω'
  setup_le : setup.IsChargeBound d setupCost
  finish_le : ∀ k a, (finish k a).IsChargeBound d finishCost

namespace CostedReduction

variable {c : P.A → ω} {d : Q.A → ω'} {σ α β : Type uB}

/-- The certified handler for one result of `setup`. -/
def certified (r : CostedReduction P Q c d σ α β) (k : σ) : Certified P Q c d :=
  ⟨r.handler k, r.exchange, r.certificate k⟩

/-- The reduced program. -/
def run (r : CostedReduction P Q c d σ α β) (x : FreeM P α) : FreeM Q β :=
  FreeM.bind r.setup fun k => FreeM.bind (x.liftM (r.handler k)) (r.finish k)

/-- The reduction's cost transformer: affine in the source budget. -/
def bound (r : CostedReduction P Q c d σ α β) (B : ω) : ω' :=
  r.setupCost + r.exchange B + r.finishCost

omit [CanonicallyOrderedAdd ω'] in
theorem bound_mono (r : CostedReduction P Q c d σ α β) : Monotone r.bound :=
  fun _ _ h => add_le_add (add_le_add le_rfl (r.exchange.monotone' h)) le_rfl

/-- **The reduction's bound.** A source program within `B` reduces to a target program within
`setupCost + E B + finishCost`. -/
theorem run_isChargeBound (r : CostedReduction P Q c d σ α β) {x : FreeM P α} {B : ω}
    (hx : x.IsChargeBound c B) : (r.run x).IsChargeBound d (r.bound B) := by
  have hmid : ∀ k, (x.liftM (r.handler k)).IsChargeBound d (r.exchange B) := fun k => by
    have h := (r.certified k).transfer hx
    rw [map_zero] at h
    exact h
  have := r.setup_le.bind fun k => (hmid k).bind (r.finish_le k)
  rwa [← add_assoc] at this

end CostedReduction

end Reduction

end Handler

end PFunctor
