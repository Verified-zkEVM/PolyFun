/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Charge
public import PolyFun.PFunctor.Handler.Stateful.Link

/-!
# Charge certificates for stateful packages

A stateful package `Stateful (FreeM Q) σ P` answers each call of `P` with a `Q`-program that also
updates a private state. It is within a charge when, from every state, the program answering a
call at `a` stays within `c a` under the target charge `d` (`Stateful.WithinCharge`).

* A stateless certificate lifts to any state (`Handler.WithinCharge.lift`).
* A certificate pushes forward along a change of cost type (`Stateful.WithinCharge.map`), which
  plays the role of the exchange of a certified handler.
* Certificates compose along `Stateful.link`, which runs the outer package's programs through the
  inner package (`Stateful.WithinCharge.link`). Linked packages are the stateful cross-layer links:
  a protocol implemented by a stateful algorithm, implemented in turn by a stateful machine model.
* A program within budget, run through a certified package from any state, is within the same
  budget (`Stateful.WithinCharge.run`), by `FreeM.IsChargeBound.run_liftM`.
-/

@[expose] public section

universe u uE uM uMB uI uIB w

namespace PFunctor

namespace Handler

namespace Stateful

variable {S T : Type u} {E : PFunctor.{uE, u}} {M : PFunctor.{uM, uMB}} {I : PFunctor.{uI, uIB}}
  {ω : Type w}

/-- From every state, the program answering each call at `a` stays within `c a` under `d`. -/
def WithinCharge [Add ω] [LE ω] [Zero ω] (h : Stateful (FreeM M) S E) (d : M.A → ω)
    (c : E.A → ω) : Prop :=
  ∀ a s, ((h a).run s).IsChargeBound d (c a)

variable [AddMonoid ω] [Preorder ω]

/-- A certificate pushes forward along a monotone additive map of cost types. -/
theorem WithinCharge.map {ω' : Type*} [AddZeroClass ω'] [Preorder ω']
    {h : Stateful (FreeM M) S E} {d : M.A → ω} {c : E.A → ω} (hh : h.WithinCharge d c)
    (φ : ω →+o ω') : h.WithinCharge (φ ∘ d) (φ ∘ c) := fun a s => by
  simpa using (hh a s).map φ

variable [AddLeftMono ω] [AddRightMono ω]

/-- **Certificates compose along `link`.** If the outer package answers each call within `c a`
under `d`, and the inner package answers each of those calls within `d` under `e`, the linked
package answers each call within `c a` under `e`. The middle interface answers in `Type u`, since
the inner package implements it. -/
theorem WithinCharge.link {M : PFunctor.{uM, u}} {outer : Stateful (FreeM M) S E}
    {inner : Stateful (FreeM I) T M}
    {c : E.A → ω} {d : M.A → ω} {e : I.A → ω} (ho : outer.WithinCharge d c)
    (hi : inner.WithinCharge e d) : (outer.link inner).WithinCharge e c := by
  rintro a ⟨s, t⟩
  rw [link_apply_run, FreeM.isChargeBound_map_iff']
  exact (ho a s).run_liftM inner hi t

/-- A program within budget, run through a certified package from any state, stays within the
budget. -/
theorem WithinCharge.run {h : Stateful (FreeM M) S E} {d : M.A → ω} {c : E.A → ω}
    (hh : h.WithinCharge d c) {α : Type u} {x : FreeM E α} {B s : ω}
    (hx : x.IsChargeBound c B s) (σ₀ : S) : (h.run x σ₀).IsChargeBound d B s :=
  hx.run_liftM h hh σ₀

end Stateful

variable {S : Type u} {E : PFunctor.{uE, u}} {M : PFunctor.{uM, uMB}} {ω : Type w}

/-- A stateless certificate holds from every state of the lifted package. -/
theorem WithinCharge.lift [AddZeroClass ω] [Preorder ω] {h : Handler (FreeM M) E}
    {d : M.A → ω} {c : E.A → ω} (hh : h.WithinCharge d c) :
    (Stateful.lift (S := S) h).WithinCharge d c := by
  intro a s
  simpa [Stateful.lift] using hh a

end Handler

end PFunctor
