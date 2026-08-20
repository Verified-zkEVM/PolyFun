/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.SubTheory

/-!
# Pointwise families of open theories

This module packages an indexed family `T : ι → OpenTheory` as one open
theory whose systems are indexed families of systems. All structural
operations act pointwise, so every tier of the `OpenTheory` lawfulness
hierarchy lifts componentwise.

The construction is structural and does not assign any computational
meaning to the index. A downstream development may instantiate `ι` with a
security parameter and put an asymptotic observation on the resulting
closed-system families without introducing probability or complexity into
PolyFun.

`SubTheory.pi` similarly packages a family of allowed-system predicates as
one sub-theory. Its membership condition is uniform at the family level:
callers may instead define a custom sub-theory when admissibility relates
different indices, as polynomial-time realizability normally does.
-/

public section

universe u v

namespace Interaction
namespace UC

namespace OpenTheory

/-- The pointwise open theory associated to a family `T : ι → OpenTheory`.

An object at boundary `Δ` selects an object of `T i` at the same boundary for
every index `i`. Boundary adaptation, parallel composition, wiring, and
plugging are all performed pointwise. -/
@[expose]
def pi {ι : Type v} (T : ι → UC.OpenTheory.{u}) : UC.OpenTheory.{max u v} where
  Obj Δ := ∀ i, (T i).Obj Δ
  map f W i := (T i).map f (W i)
  par W₁ W₂ i := (T i).par (W₁ i) (W₂ i)
  wire W₁ W₂ i := (T i).wire (W₁ i) (W₂ i)
  plug W K i := (T i).plug (W i) (K i)

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, HasUnit (T i)] : HasUnit (pi T) where
  unit i := HasUnit.unit (T := T i)

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, HasIdWire (T i)] : HasIdWire (pi T) where
  idWire Γ i := HasIdWire.idWire (T := T i) Γ

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, IsLawfulMap (T i)] : IsLawfulMap (pi T) where
  map_id W := funext fun i => OpenTheory.map_id (T := T i) (W i)
  map_comp g f W := funext fun i => OpenTheory.map_comp (T := T i) g f (W i)

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, IsLawfulPar (T i)] : IsLawfulPar (pi T) where
  map_id W := funext fun i => OpenTheory.map_id (T := T i) (W i)
  map_comp g f W := funext fun i => OpenTheory.map_comp (T := T i) g f (W i)
  map_par f₁ f₂ W₁ W₂ :=
    funext fun i => OpenTheory.map_par (T := T i) f₁ f₂ (W₁ i) (W₂ i)

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, IsLawfulWire (T i)] : IsLawfulWire (pi T) where
  map_id W := funext fun i => OpenTheory.map_id (T := T i) (W i)
  map_comp g f W := funext fun i => OpenTheory.map_comp (T := T i) g f (W i)
  map_wire f₁ f₂ W₁ W₂ :=
    funext fun i => OpenTheory.map_wire (T := T i) f₁ f₂ (W₁ i) (W₂ i)

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, IsLawfulPlug (T i)] : IsLawfulPlug (pi T) where
  map_id W := funext fun i => OpenTheory.map_id (T := T i) (W i)
  map_comp g f W := funext fun i => OpenTheory.map_comp (T := T i) g f (W i)
  map_plug f W K := funext fun i => OpenTheory.map_plug (T := T i) f (W i) (K i)

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, IsLawful (T i)] : IsLawful (pi T) where
  map_id W := funext fun i => OpenTheory.map_id (T := T i) (W i)
  map_comp g f W := funext fun i => OpenTheory.map_comp (T := T i) g f (W i)
  map_par f₁ f₂ W₁ W₂ :=
    funext fun i => OpenTheory.map_par (T := T i) f₁ f₂ (W₁ i) (W₂ i)
  map_wire f₁ f₂ W₁ W₂ :=
    funext fun i => OpenTheory.map_wire (T := T i) f₁ f₂ (W₁ i) (W₂ i)
  map_plug f W K := funext fun i => OpenTheory.map_plug (T := T i) f (W i) (K i)

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, IsMonoidal (T i)] : IsMonoidal (pi T) where
  toIsLawful := inferInstance
  toHasUnit := inferInstance
  par_assoc W₁ W₂ W₃ :=
    funext fun i => OpenTheory.par_assoc (T := T i) (W₁ i) (W₂ i) (W₃ i)
  par_comm W₁ W₂ :=
    funext fun i => OpenTheory.par_comm (T := T i) (W₁ i) (W₂ i)
  par_leftUnit W :=
    funext fun i => OpenTheory.par_leftUnit (T := T i) (W i)
  par_rightUnit W :=
    funext fun i => OpenTheory.par_rightUnit (T := T i) (W i)

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, IsTraced (T i)] : IsTraced (pi T) where
  toIsMonoidal := inferInstance
  wire_assoc W₁ W₂ W₃ :=
    funext fun i => OpenTheory.wire_assoc (T := T i) (W₁ i) (W₂ i) (W₃ i)
  wire_par_superpose W₁ W₂ W₃ :=
    funext fun i => OpenTheory.wire_par_superpose (T := T i) (W₁ i) (W₂ i) (W₃ i)
  wire_comm W₁ W₂ :=
    funext fun i => OpenTheory.wire_comm (T := T i) (W₁ i) (W₂ i)

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, IsCompactClosed (T i)] : IsCompactClosed (pi T) where
  toIsTraced := inferInstance
  toHasIdWire := inferInstance
  wire_idWire _Γ _ W₂ :=
    funext fun i => OpenTheory.wire_idWire (T := T i) (W₂ i)
  wire_idWire_right _Γ _ W₁ :=
    funext fun i => OpenTheory.wire_idWire_right (T := T i) (W₁ i)
  unit_eq := funext fun i => OpenTheory.unit_eq (T := T i)

instance {ι : Type v} {T : ι → UC.OpenTheory.{u}}
    [∀ i, HasPlugWireFactor (T i)] : HasPlugWireFactor (pi T) where
  toIsCompactClosed := inferInstance
  plug_eq_wire W K :=
    funext fun i => OpenTheory.plug_eq_wire (T := T i) (W i) (K i)
  plug_par_left W₁ W₂ K :=
    funext fun i => OpenTheory.plug_par_left (T := T i) (W₁ i) (W₂ i) (K i)
  plug_wire_left W₁ W₂ K :=
    funext fun i => OpenTheory.plug_wire_left (T := T i) (W₁ i) (W₂ i) (K i)

end OpenTheory

namespace SubTheory

/-- The pointwise sub-theory of an indexed family of sub-theories. -/
@[expose]
def pi {ι : Type v} {T : ι → OpenTheory.{u}} (D : ∀ i, SubTheory (T i)) :
    SubTheory (OpenTheory.pi T) where
  mem W := ∀ i, (D i).mem (W i)
  mem_map f hW i := (D i).mem_map f (hW i)
  mem_par hW₁ hW₂ i := (D i).mem_par (hW₁ i) (hW₂ i)
  mem_wire hW₁ hW₂ i := (D i).mem_wire (hW₁ i) (hW₂ i)

instance {ι : Type v} {T : ι → OpenTheory.{u}}
    {D : ∀ i, SubTheory (T i)} [∀ i, (D i).IsPlugClosed] :
    (pi D).IsPlugClosed where
  mem_plug hW hK i := SubTheory.IsPlugClosed.mem_plug (D := D i) (hW i) (hK i)

instance {ι : Type v} {T : ι → OpenTheory.{u}}
    {D : ∀ i, SubTheory (T i)} [∀ i, OpenTheory.HasUnit (T i)]
    [∀ i, OpenTheory.HasIdWire (T i)] [∀ i, (D i).IsStructural] :
    (pi D).IsStructural where
  mem_unit i := SubTheory.IsStructural.mem_unit (D := D i)
  mem_idWire Γ i := SubTheory.IsStructural.mem_idWire (D := D i) Γ

end SubTheory

end UC
end Interaction
