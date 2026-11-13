/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import PolyFun.Control.Monad.Hom.Writer
public import PolyFun.PFunctor.Handler.Charge
public import PolyFun.PFunctor.Handler.Stateful.Combinators

/-!
# Moving charges between meters

A charge on calls can be kept in three ways: logged in a writer (`Handler.withChargeW`), kept as a
running total in state (`Handler.withCharge`), or kept as a passive counter beside the state of a
stateful handler (`Handler.Stateful.extend`). This module relates the three, and moves each along
monad morphisms of the underlying handler.

## Naturality

Charging a handler commutes with post-composing it by a monad morphism `φ`:
`WriterT.mapHom φ` applied to `h.withChargeW c` is `(mapTarget φ h).withChargeW c`
(`Handler.mapHom_withChargeW`), and the same holds for `withCharge` under `StateT.mapHom φ`
(`Handler.mapHom_withCharge`). By the fold's naturality `FreeM.liftM_natural`, the run of a charged
program commutes with `φ` as well (`Handler.mapHom_liftM_withChargeW`,
`Handler.run_liftM_mapTarget_withCharge`). Mapping the log along an additive hom `f` is charging by
`f ∘ c` (`Handler.mapOutputHom_liftM_withChargeW`).

## Meters

The writer and state meters agree: from a running total `t`, the state meter ends at `t` plus the
writer's log (`Handler.run_liftM_withCharge`). For a stateful handler, a passive counter added on
the right of its state with `Stateful.extend` ends at its starting value plus the writer's log,
beside the same output and handler state (`Handler.Stateful.run_extend_eq_withChargeW`). Every
charge is added on the right, so none of these laws needs commutativity.
-/

public section

universe uA uB v w

namespace PFunctor

namespace Handler

variable {P : PFunctor.{uA, uB}} {m : Type uB → Type v} {n : Type uB → Type w} {ω : Type uB}

/-! ## Naturality -/

section Naturality

variable [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]

/-- Charging in a writer commutes with post-composing the handler by a monad morphism. -/
theorem mapHom_withChargeW [AddMonoid ω] (φ : m →ᵐ n) (h : Handler m P) (c : P.A → ω)
    (a : P.A) :
    WriterT.mapHom φ (h.withChargeW c a) = (mapTarget (fun x => φ x) h).withChargeW c a := by
  apply WriterT.ext
  simp

/-- **Interpreting a writer-charged program commutes with a monad morphism.** -/
theorem mapHom_liftM_withChargeW [AddMonoid ω] (φ : m →ᵐ n) (h : Handler m P) (c : P.A → ω)
    {α : Type uB} (x : FreeM P α) :
    WriterT.mapHom φ (x.liftM (h.withChargeW c)) =
      x.liftM ((mapTarget (fun x => φ x) h).withChargeW c) := by
  rw [FreeM.liftM_natural]
  congr 1
  funext a
  exact mapHom_withChargeW φ h c a

/-- Charging with a running total commutes with post-composing the handler by a monad morphism. -/
theorem mapHom_withCharge [Add ω] (φ : m →ᵐ n) (h : Handler m P) (c : P.A → ω) (a : P.A) :
    StateT.mapHom φ (h.withCharge c a) = (mapTarget (fun x => φ x) h).withCharge c a := by
  ext s
  simp

/-- **Running a program charged with a running total commutes with a monad morphism.** -/
theorem run_liftM_mapTarget_withCharge [Add ω] (φ : m →ᵐ n) (h : Handler m P) (c : P.A → ω)
    {α : Type uB} (x : FreeM P α) (s : ω) :
    (x.liftM ((mapTarget (fun x => φ x) h).withCharge c)).run s =
      φ ((x.liftM (h.withCharge c)).run s) := by
  rw [← FreeM.run_liftM_mapHom]
  congr 2
  funext a
  exact (mapHom_withCharge φ h c a).symm

end Naturality

/-! ## Changing the charge -/

section MapOutput

variable [Monad m] [LawfulMonad m] {τ : Type uB} [AddMonoid ω] [AddMonoid τ]

/-- Mapping a charge log along an additive hom `f` is charging by `f ∘ c`. -/
theorem mapOutputHom_withChargeW (f : ω →+ τ) (h : Handler m P) (c : P.A → ω) (a : P.A) :
    WriterT.mapOutputHom (AddMonoidHom.toMultiplicative f) (h.withChargeW c a) =
      h.withChargeW (f ∘ c) a := by
  apply WriterT.ext
  simp [Functor.map_map]

/-- **Every charge of a run is its log pushed along an additive hom.** Mapping the log of a
writer-charged run along `f` is the run charged by `f ∘ c`. -/
theorem mapOutputHom_liftM_withChargeW (f : ω →+ τ) (h : Handler m P) (c : P.A → ω)
    {α : Type uB} (x : FreeM P α) :
    WriterT.mapOutputHom (AddMonoidHom.toMultiplicative f) (x.liftM (h.withChargeW c)) =
      x.liftM (h.withChargeW (f ∘ c)) := by
  rw [FreeM.liftM_natural]
  congr 1
  funext a
  exact mapOutputHom_withChargeW f h c a

end MapOutput

/-! ## Meters -/

section Meters

variable [Monad m] [LawfulMonad m] [AddMonoid ω]

/-- Reading a writer charge as a running total gives the state meter. -/
theorem toStateTHom_withChargeW (h : Handler m P) (c : P.A → ω) (a : P.A) :
    WriterT.toStateTHom (h.withChargeW c a) = h.withCharge c a := by
  ext t
  simp [Functor.map_map]

/-- **The writer and state meters agree.** From a running total `t`, the state meter of a run ends
at `t` plus the writer meter's log of the same run. -/
theorem run_liftM_withCharge (h : Handler m P) (c : P.A → ω) {α : Type uB} (x : FreeM P α)
    (t : ω) :
    (x.liftM (h.withCharge c)).run t =
      (fun p => (p.1, t + Multiplicative.toAdd p.2)) <$> (x.liftM (h.withChargeW c)).run := by
  rw [← WriterT.run_toStateTHom, FreeM.liftM_natural]
  congr 2
  funext a
  exact (toStateTHom_withChargeW h c a).symm

namespace Stateful

variable {S : Type uB}

/-- **A passive counter is the writer meter.** Extending a stateful handler with a counter on the
right of its state that adds `c a` at each call gives, from the counter value `t`, the output and
handler state of the writer-charged run, with the counter at `t` plus that run's log. -/
theorem run_extend_eq_withChargeW (h : Stateful m S P) (c : P.A → ω) {α : Type uB}
    (x : FreeM P α) (s : S) (t : ω) :
    (Stateful.extend h (fun a _ _ _ total => total + c a)).run x (s, t) =
      (fun r => (r.1.1, (r.2, t + Multiplicative.toAdd r.1.2))) <$>
        (x.liftM (h.withChargeW c)).run.run s := by
  induction x using FreeM.rec generalizing s t with
  | pure a => simp
  | liftBind a r ih =>
    rw [run_liftBind, extend_apply_run]
    simp [FreeM.liftM, ih, add_assoc, map_bind, bind_map_left]

end Stateful

end Meters

end Handler

end PFunctor
