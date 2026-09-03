/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.OpenTheory.Quotient

/-!
# Emulation across a quotient

Observations and emulation judgments move between a theory `T` and its
quotient `T.quotient E` by a congruence `E`.

* `Observation.comap` pulls an observation on the quotient back to `T`;
  `Observation.descend` pushes an `E`-invariant observation on `T` forward.
* `Emulates.quotient_iff`: emulation between classes in the quotient is
  emulation between representatives under the pulled-back observation, since
  every closing context of the quotient is the class of a context of `T`.
* An observation on the quotient that respects plug commutation or
  factorization pulls back to one that does. In particular, when the quotient
  satisfies `HasPlugFactorization` — for instance because the laws of `T` hold
  modulo `E` — every observation on `T` that factors through the quotient
  respects factorization, and the whole `Emulates` composition suite applies
  to `T` at that observation.

The congruence at the empty boundary is itself the pull-back of equality on
the quotient (`Observation.comap_eq`): this is how a process model's structural
equivalence becomes the canonical observation of its quotient theory.
-/

public section

universe u

namespace Interaction
namespace UC

variable {T : OpenTheory.{u}} (E : OpenTheory.Congruence T)

/-! ## Observations across the quotient -/

namespace Observation

/-- Pull an observation on the quotient back to the theory. -/
@[expose]
def comap (Obs : Observation (T.quotient E)) : Observation T where
  rel c₁ c₂ := Obs.rel (E.cls c₁) (E.cls c₂)
  equiv := ⟨fun _ => Obs.equiv.refl _, Obs.equiv.symm, Obs.equiv.trans⟩

@[simp]
theorem comap_rel (Obs : Observation (T.quotient E)) {c₁ c₂ : T.Closed} :
    (Obs.comap E).rel c₁ c₂ ↔ Obs.rel (E.cls c₁) (E.cls c₂) :=
  Iff.rfl

/-- The congruence at the empty boundary, as an observation on the theory. -/
@[expose]
def ofCongruence : Observation T where
  rel := E.rel
  equiv := E.equivalence PortBoundary.empty

@[simp]
theorem ofCongruence_rel {c₁ c₂ : T.Closed} : (ofCongruence E).rel c₁ c₂ ↔ E.rel c₁ c₂ :=
  Iff.rfl

/-- Equality on the quotient pulls back to the congruence. -/
theorem comap_eq_rel {c₁ c₂ : T.Closed} :
    ((Observation.eq (T.quotient E)).comap E).rel c₁ c₂ ↔ E.rel c₁ c₂ := by
  rw [comap_rel, Observation.eq_rel]
  exact E.cls_eq_cls

/-- Push an `E`-invariant observation forward to the quotient. -/
@[expose]
def descend (Obs : Observation T) (hInv : ∀ {c₁ c₂ : T.Closed}, E.rel c₁ c₂ → Obs.rel c₁ c₂) :
    Observation (T.quotient E) where
  rel q₁ q₂ := Quotient.liftOn₂' q₁ q₂ Obs.rel fun _ _ _ _ ha hb =>
    propext ⟨fun h => Obs.equiv.trans (Obs.equiv.symm (hInv ha)) (Obs.equiv.trans h (hInv hb)),
      fun h => Obs.equiv.trans (hInv ha) (Obs.equiv.trans h (Obs.equiv.symm (hInv hb)))⟩
  equiv :=
    ⟨fun q => Quotient.inductionOn' q fun c => Obs.equiv.refl c,
      fun {q₁ q₂} => Quotient.inductionOn₂' q₁ q₂ fun _ _ h => Obs.equiv.symm h,
      fun {q₁ q₂ q₃} => Quotient.inductionOn₃' q₁ q₂ q₃ fun _ _ _ h h' => Obs.equiv.trans h h'⟩

@[simp]
theorem descend_rel_cls (Obs : Observation T)
    (hInv : ∀ {c₁ c₂ : T.Closed}, E.rel c₁ c₂ → Obs.rel c₁ c₂) {c₁ c₂ : T.Closed} :
    (Obs.descend E hInv).rel (E.cls c₁) (E.cls c₂) ↔ Obs.rel c₁ c₂ :=
  Iff.rfl

/-- Pulling a descended observation back recovers the observation. -/
theorem comap_descend_rel (Obs : Observation T)
    (hInv : ∀ {c₁ c₂ : T.Closed}, E.rel c₁ c₂ → Obs.rel c₁ c₂) {c₁ c₂ : T.Closed} :
    ((Obs.descend E hInv).comap E).rel c₁ c₂ ↔ Obs.rel c₁ c₂ :=
  Iff.rfl

/-! ## Factorization pulls back -/

instance comap_respectsPlugComm (Obs : Observation (T.quotient E)) [Obs.RespectsPlugComm] :
    (Obs.comap E).RespectsPlugComm where
  plug_comm W K := Observation.RespectsPlugComm.plug_comm (Obs := Obs) (E.cls W) (E.cls K)

instance comap_respectsFactorization (Obs : Observation (T.quotient E))
    [Obs.RespectsFactorization] : (Obs.comap E).RespectsFactorization where
  close_par_left W₁ W₂ K :=
    Observation.RespectsFactorization.close_par_left (Obs := Obs) (E.cls W₁) (E.cls W₂) (E.cls K)
  close_par_right W₁ W₂ K :=
    Observation.RespectsFactorization.close_par_right (Obs := Obs) (E.cls W₁) (E.cls W₂)
      (E.cls K)
  close_wire_left W₁ W₂ K :=
    Observation.RespectsFactorization.close_wire_left (Obs := Obs) (E.cls W₁) (E.cls W₂)
      (E.cls K)
  close_wire_right W₁ W₂ K :=
    Observation.RespectsFactorization.close_wire_right (Obs := Obs) (E.cls W₁) (E.cls W₂)
      (E.cls K)

end Observation

/-! ## Emulation across the quotient -/

/-- Emulation of classes in the quotient is emulation of representatives under
the pulled-back observation. -/
theorem Emulates.quotient_iff {Δ : PortBoundary} {real ideal : T.Obj Δ}
    {Obs : Observation (T.quotient E)} :
    Emulates (E.cls real) (E.cls ideal) Obs ↔ Emulates real ideal (Obs.comap E) := by
  constructor
  · intro h
    exact ⟨fun K => h.compare (E.cls K)⟩
  · intro h
    exact ⟨fun K => Quotient.inductionOn' K fun K => h.compare K⟩

/-- Emulation at the congruence itself: no closing context separates `real`
from `ideal` up to `E`. -/
theorem Emulates.ofCongruence_iff {Δ : PortBoundary} {real ideal : T.Obj Δ} :
    Emulates real ideal (Observation.ofCongruence E) ↔
      Emulates (E.cls real) (E.cls ideal) (Observation.eq (T.quotient E)) := by
  rw [Emulates.quotient_iff]
  constructor
  · intro h
    exact ⟨fun K => (Observation.comap_eq_rel E).mpr (h.compare K)⟩
  · intro h
    exact ⟨fun K => (Observation.comap_eq_rel E).mp (h.compare K)⟩

end UC
end Interaction
