/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.OpenTheory.Congruence
public import PolyFun.Interaction.UC.OpenTheory.PlugFactorization

/-!
# Quotient open theories

`OpenTheory.quotient T E` is the open theory whose objects at each boundary are
the classes of `T`'s objects under the congruence `E`, with the operations
descended along `Quotient.map'` and `Quotient.map₂'`.

The point of the construction is to prove coherence once. A theory whose laws
hold only up to `E` satisfies the **laws modulo `E`** — the classes
`IsLawfulMod`, `IsMonoidalMod`, `IsTracedMod`, `IsCompactClosedMod`,
`HasPlugWireFactorMod`, and `HasPlugFactorizationMod`, whose fields are the
strict laws with equality replaced by `E.rel` — and each of them lifts to the
corresponding strict class on the quotient. A strict theory satisfies every
law modulo any congruence, so nothing is lost for theories that already
satisfy the strict ladder.

Downstream, the composition theorems of `Emulates` therefore apply to the
quotient of a process model unchanged, and observations on the quotient pull
back to observations on the model that respect factorization; see
`EmulatesQuotient`.
-/

public section

universe u

namespace Interaction
namespace UC
namespace OpenTheory

variable {T : UC.OpenTheory.{u}}

/-! ## The quotient theory -/

/-- The quotient of `T` by the congruence `E`. -/
@[expose]
def quotient (T : UC.OpenTheory.{u}) (E : Congruence T) : UC.OpenTheory.{u} where
  Obj Δ := Quotient (E.setoid Δ)
  map φ := Quotient.map' (T.map φ) fun _ _ h => E.map_congr φ h
  par := Quotient.map₂' T.par fun _ _ h₁ _ _ h₂ => E.par_congr h₁ h₂
  wire := Quotient.map₂' T.wire fun _ _ h₁ _ _ h₂ => E.wire_congr h₁ h₂
  plug := Quotient.map₂' T.plug fun _ _ h₁ _ _ h₂ => E.plug_congr h₁ h₂

namespace Congruence

variable (E : Congruence T)

/-- The class of an object in the quotient theory. -/
@[expose]
def cls {Δ : PortBoundary} (W : T.Obj Δ) : (T.quotient E).Obj Δ :=
  Quotient.mk'' W

theorem cls_eq_cls {Δ : PortBoundary} {W W' : T.Obj Δ} : E.cls W = E.cls W' ↔ E.rel W W' :=
  Quotient.eq''

theorem cls_surjective {Δ : PortBoundary} : Function.Surjective (E.cls (Δ := Δ)) :=
  Quotient.mk''_surjective

@[simp]
theorem quotient_map_cls {Δ₁ Δ₂ : PortBoundary} (φ : PortBoundary.Hom Δ₁ Δ₂) (W : T.Obj Δ₁) :
    (T.quotient E).map φ (E.cls W) = E.cls (T.map φ W) :=
  rfl

@[simp]
theorem quotient_par_cls {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂) :
    (T.quotient E).par (E.cls W₁) (E.cls W₂) = E.cls (T.par W₁ W₂) :=
  rfl

@[simp]
theorem quotient_wire_cls {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)) :
    (T.quotient E).wire (E.cls W₁) (E.cls W₂) = E.cls (T.wire W₁ W₂) :=
  rfl

@[simp]
theorem quotient_plug_cls {Δ : PortBoundary} (W : T.Obj Δ) (K : T.Obj (PortBoundary.swap Δ)) :
    (T.quotient E).plug (E.cls W) (E.cls K) = E.cls (T.plug W K) :=
  rfl

/-- Induction on the quotient: it suffices to consider classes. -/
@[elab_as_elim]
theorem quotient_ind {Δ : PortBoundary} {p : (T.quotient E).Obj Δ → Prop}
    (h : ∀ W, p (E.cls W)) (q : (T.quotient E).Obj Δ) : p q :=
  Quotient.ind' h q

end Congruence

/-! ## Laws modulo a congruence -/

/-- Naturality of the operations up to `E`: the fields of `IsLawful` with
equality replaced by `E.rel`. -/
class IsLawfulMod (E : Congruence T) : Prop where
  map_id : ∀ {Δ : PortBoundary} (W : T.Obj Δ), E.rel (T.map (PortBoundary.Hom.id Δ) W) W
  map_comp : ∀ {Δ₁ Δ₂ Δ₃ : PortBoundary} (g : PortBoundary.Hom Δ₂ Δ₃)
      (f : PortBoundary.Hom Δ₁ Δ₂) (W : T.Obj Δ₁),
    E.rel (T.map (PortBoundary.Hom.comp g f) W) (T.map g (T.map f W))
  map_par : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' : PortBoundary} (f₁ : PortBoundary.Hom Δ₁ Δ₁')
      (f₂ : PortBoundary.Hom Δ₂ Δ₂') (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂),
    E.rel (T.map (PortBoundary.Hom.tensor f₁ f₂) (T.par W₁ W₂))
      (T.par (T.map f₁ W₁) (T.map f₂ W₂))
  map_wire : ∀ {Δ₁ Δ₁' Γ Δ₂ Δ₂' : PortBoundary} (f₁ : PortBoundary.Hom Δ₁ Δ₁')
      (f₂ : PortBoundary.Hom Δ₂ Δ₂') (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)),
    E.rel (T.map (PortBoundary.Hom.tensor f₁ f₂) (T.wire W₁ W₂))
      (T.wire (T.map (PortBoundary.Hom.tensor f₁ (PortBoundary.Hom.id Γ)) W₁)
        (T.map (PortBoundary.Hom.tensor (PortBoundary.Hom.id (PortBoundary.swap Γ)) f₂) W₂))
  map_plug : ∀ {Δ₁ Δ₂ : PortBoundary} (f : PortBoundary.Hom Δ₁ Δ₂) (W : T.Obj Δ₁)
      (K : T.Obj (PortBoundary.swap Δ₂)),
    E.rel (T.plug (T.map f W) K) (T.plug W (T.map (PortBoundary.Hom.swap f) K))

/-- The symmetric monoidal laws up to `E`. -/
class IsMonoidalMod (E : Congruence T) [HasUnit T] : Prop extends IsLawfulMod E where
  par_assoc : ∀ {Δ₁ Δ₂ Δ₃ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂) (W₃ : T.Obj Δ₃),
    E.rel (T.map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).toHom (T.par (T.par W₁ W₂) W₃))
      (T.par W₁ (T.par W₂ W₃))
  par_comm : ∀ {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂),
    E.rel (T.map (PortBoundary.Equiv.tensorComm Δ₁ Δ₂).toHom (T.par W₁ W₂)) (T.par W₂ W₁)
  par_leftUnit : ∀ {Δ : PortBoundary} (W : T.Obj Δ),
    E.rel (T.map (PortBoundary.Equiv.tensorEmptyLeft Δ).toHom (T.par (HasUnit.unit (T := T)) W))
      W
  par_rightUnit : ∀ {Δ : PortBoundary} (W : T.Obj Δ),
    E.rel (T.map (PortBoundary.Equiv.tensorEmptyRight Δ).toHom
      (T.par W (HasUnit.unit (T := T)))) W

/-- The trace laws up to `E`. -/
class IsTracedMod (E : Congruence T) [HasUnit T] : Prop extends IsMonoidalMod E where
  wire_assoc : ∀ {Δ₁ Γ₁ Γ₂ Δ₃ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ₁))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ₁) Γ₂))
      (W₃ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ₂) Δ₃)),
    E.rel (T.wire (T.wire W₁ W₂) W₃) (T.wire W₁ (T.wire W₂ W₃))
  wire_par_superpose : ∀ {Δ₁ Δ₂ Γ Δ₃ : PortBoundary} (W₁ : T.Obj Δ₁)
      (W₂ : T.Obj (PortBoundary.tensor Δ₂ Γ))
      (W₃ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₃)),
    E.rel
      (T.wire (T.map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Γ).symm.toHom (T.par W₁ W₂)) W₃)
      (T.map (PortBoundary.Equiv.tensorAssoc Δ₁ Δ₂ Δ₃).symm.toHom (T.par W₁ (T.wire W₂ W₃)))
  wire_comm : ∀ {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)),
    E.rel (T.wire W₁ W₂)
      (T.map (PortBoundary.Equiv.tensorComm Δ₂ Δ₁).toHom
        (T.wire (T.map (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom W₂)
          (T.map (PortBoundary.Equiv.tensorComm Δ₁ Γ).toHom W₁)))

/-- The compact-closure laws up to `E`. -/
class IsCompactClosedMod (E : Congruence T) [HasUnit T] [HasIdWire T] : Prop
    extends IsTracedMod E where
  wire_idWire : ∀ (Γ : PortBoundary) {Δ₂ : PortBoundary}
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)),
    E.rel (T.wire (HasIdWire.idWire (T := T) Γ) W₂) W₂
  wire_idWire_right : ∀ (Γ : PortBoundary) {Δ₁ : PortBoundary}
      (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)),
    E.rel (T.wire W₁ (HasIdWire.idWire (T := T) Γ)) W₁
  unit_eq : E.rel (HasUnit.unit (T := T))
    (T.map (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
      (HasIdWire.idWire (T := T) PortBoundary.empty))

/-- The plug-wire factorization laws up to `E`. -/
class HasPlugWireFactorMod (E : Congruence T) [HasUnit T] [HasIdWire T] : Prop
    extends IsCompactClosedMod E where
  plug_eq_wire : ∀ {Δ : PortBoundary} (W : T.Obj Δ) (K : T.Obj (PortBoundary.swap Δ)),
    E.rel (T.plug W K)
      (T.map (PortBoundary.Equiv.tensorEmptyLeft PortBoundary.empty).toHom
        (T.wire (T.map (PortBoundary.Equiv.tensorEmptyLeft Δ).symm.toHom W)
          (T.map (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ)).symm.toHom K)))
  plug_par_left : ∀ {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
      (K : T.Obj (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))),
    E.rel (T.plug (T.par W₁ W₂) K)
      (T.plug W₁
        (T.map (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁)).toHom
          (T.wire (Γ := PortBoundary.swap Δ₂) (Δ₂ := PortBoundary.empty) K
            (T.map (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm.toHom W₂))))
  plug_wire_left : ∀ {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
      (K : T.Obj (PortBoundary.swap (PortBoundary.tensor Δ₁ Δ₂))),
    E.rel (T.plug (T.wire W₁ W₂) K)
      (T.plug W₁
        (T.wire (Δ₁ := PortBoundary.swap Δ₁) (Γ := PortBoundary.swap Δ₂)
          (Δ₂ := PortBoundary.swap Γ) K
          (T.map (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂).toHom W₂)))

/-- The five plug-factorization laws up to `E`. -/
class HasPlugFactorizationMod (E : Congruence T) : Prop extends IsLawfulMod E where
  plug_comm : ∀ {Δ : PortBoundary} (W : T.Obj Δ) (K : T.Obj (PortBoundary.swap Δ)),
    E.rel (T.plug W K) (T.plug K W)
  close_par_left : ∀ {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
      (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)),
    E.rel (T.close (T.par W₁ W₂) K) (T.close W₁ (T.parContextLeft W₂ K))
  close_par_right : ∀ {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
      (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)),
    E.rel (T.close (T.par W₁ W₂) K) (T.close W₂ (T.parContextRight W₁ K))
  close_wire_left : ∀ {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
      (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)),
    E.rel (T.close (T.wire W₁ W₂) K) (T.close W₁ (T.wireContextLeft W₂ K))
  close_wire_right : ∀ {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
      (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)),
    E.rel (T.close (T.wire W₁ W₂) K) (T.close W₂ (T.wireContextRight W₁ K))

/-! ## Strict laws hold modulo any congruence -/

section Strict

variable (E : Congruence T)

instance (priority := 100) isLawfulMod_of_isLawful [IsLawful T] : IsLawfulMod E where
  map_id W := E.rel_of_eq (OpenTheory.map_id W)
  map_comp g f W := E.rel_of_eq (OpenTheory.map_comp g f W)
  map_par f₁ f₂ W₁ W₂ := E.rel_of_eq (OpenTheory.map_par f₁ f₂ W₁ W₂)
  map_wire f₁ f₂ W₁ W₂ := E.rel_of_eq (OpenTheory.map_wire f₁ f₂ W₁ W₂)
  map_plug f W K := E.rel_of_eq (OpenTheory.map_plug f W K)

instance (priority := 100) isMonoidalMod_of_isMonoidal [IsMonoidal T] : IsMonoidalMod E where
  par_assoc W₁ W₂ W₃ := E.rel_of_eq (OpenTheory.par_assoc W₁ W₂ W₃)
  par_comm W₁ W₂ := E.rel_of_eq (OpenTheory.par_comm W₁ W₂)
  par_leftUnit W := E.rel_of_eq (OpenTheory.par_leftUnit W)
  par_rightUnit W := E.rel_of_eq (OpenTheory.par_rightUnit W)

instance (priority := 100) isTracedMod_of_isTraced [IsTraced T] : IsTracedMod E where
  wire_assoc W₁ W₂ W₃ := E.rel_of_eq (OpenTheory.wire_assoc W₁ W₂ W₃)
  wire_par_superpose W₁ W₂ W₃ := E.rel_of_eq (OpenTheory.wire_par_superpose W₁ W₂ W₃)
  wire_comm W₁ W₂ := E.rel_of_eq (OpenTheory.wire_comm W₁ W₂)

instance (priority := 100) isCompactClosedMod_of_isCompactClosed [IsCompactClosed T] :
    IsCompactClosedMod E where
  wire_idWire _ _ W₂ := E.rel_of_eq (OpenTheory.wire_idWire W₂)
  wire_idWire_right _ _ W₁ := E.rel_of_eq (OpenTheory.wire_idWire_right W₁)
  unit_eq := E.rel_of_eq (OpenTheory.unit_eq (T := T))

instance (priority := 100) hasPlugWireFactorMod_of_hasPlugWireFactor [HasPlugWireFactor T] :
    HasPlugWireFactorMod E where
  plug_eq_wire W K := E.rel_of_eq (OpenTheory.plug_eq_wire W K)
  plug_par_left W₁ W₂ K := E.rel_of_eq (OpenTheory.plug_par_left W₁ W₂ K)
  plug_wire_left W₁ W₂ K := E.rel_of_eq (OpenTheory.plug_wire_left W₁ W₂ K)

instance (priority := 100) hasPlugFactorizationMod_of_hasPlugFactorization
    [HasPlugFactorization T] : HasPlugFactorizationMod E where
  plug_comm W K := E.rel_of_eq (OpenTheory.plug_comm W K)
  close_par_left W₁ W₂ K := E.rel_of_eq (OpenTheory.close_par_left W₁ W₂ K)
  close_par_right W₁ W₂ K := E.rel_of_eq (OpenTheory.close_par_right W₁ W₂ K)
  close_wire_left W₁ W₂ K := E.rel_of_eq (OpenTheory.close_wire_left W₁ W₂ K)
  close_wire_right W₁ W₂ K := E.rel_of_eq (OpenTheory.close_wire_right W₁ W₂ K)

end Strict

/-! ## Laws modulo the congruence lift to the quotient -/

section Lift

variable (E : Congruence T)

instance [HasUnit T] : HasUnit (T.quotient E) where
  unit := E.cls (HasUnit.unit (T := T))

instance [HasIdWire T] : HasIdWire (T.quotient E) where
  idWire Γ := E.cls (HasIdWire.idWire (T := T) Γ)

theorem quotient_unit [HasUnit T] :
    HasUnit.unit (T := T.quotient E) = E.cls (HasUnit.unit (T := T)) :=
  rfl

theorem quotient_idWire [HasIdWire T] (Γ : PortBoundary) :
    HasIdWire.idWire (T := T.quotient E) Γ = E.cls (HasIdWire.idWire (T := T) Γ) :=
  rfl

instance [IsLawfulMod E] : IsLawful (T.quotient E) where
  map_id W := Quotient.inductionOn' W fun W => Quotient.sound' (IsLawfulMod.map_id (E := E) W)
  map_comp g f W :=
    Quotient.inductionOn' W fun W => Quotient.sound' (IsLawfulMod.map_comp (E := E) g f W)
  map_par f₁ f₂ W₁ W₂ :=
    Quotient.inductionOn₂' W₁ W₂ fun W₁ W₂ =>
      Quotient.sound' (IsLawfulMod.map_par (E := E) f₁ f₂ W₁ W₂)
  map_wire f₁ f₂ W₁ W₂ :=
    Quotient.inductionOn₂' W₁ W₂ fun W₁ W₂ =>
      Quotient.sound' (IsLawfulMod.map_wire (E := E) f₁ f₂ W₁ W₂)
  map_plug f W K :=
    Quotient.inductionOn₂' W K fun W K => Quotient.sound' (IsLawfulMod.map_plug (E := E) f W K)

instance [HasUnit T] [IsMonoidalMod E] : IsMonoidal (T.quotient E) where
  toIsLawful := inferInstance
  toHasUnit := inferInstance
  par_assoc W₁ W₂ W₃ :=
    Quotient.inductionOn₃' W₁ W₂ W₃ fun W₁ W₂ W₃ =>
      Quotient.sound' (IsMonoidalMod.par_assoc (E := E) W₁ W₂ W₃)
  par_comm W₁ W₂ :=
    Quotient.inductionOn₂' W₁ W₂ fun W₁ W₂ =>
      Quotient.sound' (IsMonoidalMod.par_comm (E := E) W₁ W₂)
  par_leftUnit W :=
    Quotient.inductionOn' W fun W => Quotient.sound' (IsMonoidalMod.par_leftUnit (E := E) W)
  par_rightUnit W :=
    Quotient.inductionOn' W fun W => Quotient.sound' (IsMonoidalMod.par_rightUnit (E := E) W)

instance [HasUnit T] [IsTracedMod E] : IsTraced (T.quotient E) where
  toIsMonoidal := inferInstance
  wire_assoc W₁ W₂ W₃ :=
    Quotient.inductionOn₃' W₁ W₂ W₃ fun W₁ W₂ W₃ =>
      Quotient.sound' (IsTracedMod.wire_assoc (E := E) W₁ W₂ W₃)
  wire_par_superpose W₁ W₂ W₃ :=
    Quotient.inductionOn₃' W₁ W₂ W₃ fun W₁ W₂ W₃ =>
      Quotient.sound' (IsTracedMod.wire_par_superpose (E := E) W₁ W₂ W₃)
  wire_comm W₁ W₂ :=
    Quotient.inductionOn₂' W₁ W₂ fun W₁ W₂ =>
      Quotient.sound' (IsTracedMod.wire_comm (E := E) W₁ W₂)

instance [HasUnit T] [HasIdWire T] [IsCompactClosedMod E] : IsCompactClosed (T.quotient E) where
  toIsTraced := inferInstance
  toHasIdWire := inferInstance
  wire_idWire Γ _ W₂ :=
    Quotient.inductionOn' W₂ fun W₂ =>
      Quotient.sound' (IsCompactClosedMod.wire_idWire (E := E) Γ W₂)
  wire_idWire_right Γ _ W₁ :=
    Quotient.inductionOn' W₁ fun W₁ =>
      Quotient.sound' (IsCompactClosedMod.wire_idWire_right (E := E) Γ W₁)
  unit_eq := Quotient.sound' (IsCompactClosedMod.unit_eq (E := E))

instance [HasUnit T] [HasIdWire T] [HasPlugWireFactorMod E] :
    HasPlugWireFactor (T.quotient E) where
  toIsCompactClosed := inferInstance
  plug_eq_wire W K :=
    Quotient.inductionOn₂' W K fun W K =>
      Quotient.sound' (HasPlugWireFactorMod.plug_eq_wire (E := E) W K)
  plug_par_left W₁ W₂ K :=
    Quotient.inductionOn₃' W₁ W₂ K fun W₁ W₂ K =>
      Quotient.sound' (HasPlugWireFactorMod.plug_par_left (E := E) W₁ W₂ K)
  plug_wire_left W₁ W₂ K :=
    Quotient.inductionOn₃' W₁ W₂ K fun W₁ W₂ K =>
      Quotient.sound' (HasPlugWireFactorMod.plug_wire_left (E := E) W₁ W₂ K)

instance [HasPlugFactorizationMod E] : HasPlugFactorization (T.quotient E) where
  toIsLawful := inferInstance
  plug_comm W K :=
    Quotient.inductionOn₂' W K fun W K =>
      Quotient.sound' (HasPlugFactorizationMod.plug_comm (E := E) W K)
  close_par_left W₁ W₂ K :=
    Quotient.inductionOn₃' W₁ W₂ K fun W₁ W₂ K =>
      Quotient.sound' (HasPlugFactorizationMod.close_par_left (E := E) W₁ W₂ K)
  close_par_right W₁ W₂ K :=
    Quotient.inductionOn₃' W₁ W₂ K fun W₁ W₂ K =>
      Quotient.sound' (HasPlugFactorizationMod.close_par_right (E := E) W₁ W₂ K)
  close_wire_left W₁ W₂ K :=
    Quotient.inductionOn₃' W₁ W₂ K fun W₁ W₂ K =>
      Quotient.sound' (HasPlugFactorizationMod.close_wire_left (E := E) W₁ W₂ K)
  close_wire_right W₁ W₂ K :=
    Quotient.inductionOn₃' W₁ W₂ K fun W₁ W₂ K =>
      Quotient.sound' (HasPlugFactorizationMod.close_wire_right (E := E) W₁ W₂ K)

end Lift

end OpenTheory
end UC
end Interaction
