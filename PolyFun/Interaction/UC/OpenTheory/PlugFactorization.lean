/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

import all PolyFun.Interaction.UC.Interface
public import PolyFun.Interaction.UC.OpenTheory

/-!
# Plug factorization

The UC composition theorems move one component of a composite across the
divide between the system under test and its closing context. In a theory
with strict compact-closed structure that motion is an equality derived from
`HasPlugWireFactor`. Concrete process models cannot honestly reach the unit
and snake laws of that class: at strong sampler equivalence `interleave unit p`
has one more path per step than `p`, so no path bijection exists. They can,
however, validate the five equalities the composition theorems consume.

`HasPlugFactorization` names exactly those five laws on top of `IsLawful`:
`plug_comm` and the four residual-context factorizations `close_par_left`,
`close_par_right`, `close_wire_left`, `close_wire_right`. Every
`HasPlugWireFactor` theory is an instance
(`hasPlugFactorization_of_hasPlugWireFactor`), so the free syntax models are
unaffected, and downstream results that only need the composition suite
should assume this class.

The residual-context formers `parContextLeft`, `parContextRight`,
`wireContextLeft`, and `wireContextRight` are plain `map`/`wire` composites
and need no lawfulness at all.
-/

public section

universe u

namespace Interaction
namespace UC
namespace OpenTheory

variable {T : UC.OpenTheory.{u}}

/-! ## Residual contexts -/

/-- The effective plug for the left component of a parallel composition.

Given `W₂ : T.Obj Δ₂` and `K : T.Plug (tensor Δ₁ Δ₂)`, wire them
together through the `Δ₂` boundary to obtain a plug for `Δ₁` alone. -/
@[expose]
def parContextLeft {Δ₁ Δ₂ : PortBoundary} (W₂ : T.Obj Δ₂)
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) : T.Plug Δ₁ :=
  T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₁))
    (T.wire
      (Γ := PortBoundary.swap Δ₂)
      (Δ₂ := PortBoundary.empty)
      K
      (T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight Δ₂).symm W₂))

/-- The effective plug for the right component of a parallel composition.

Given `W₁ : T.Obj Δ₁` and `K : T.Plug (tensor Δ₁ Δ₂)`, wire them
together through the `Δ₁` boundary to obtain a plug for `Δ₂` alone. -/
@[expose]
def parContextRight {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁)
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) : T.Plug Δ₂ :=
  T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight (PortBoundary.swap Δ₂))
    (T.wire
      (Γ := PortBoundary.swap Δ₁)
      (Δ₂ := PortBoundary.empty)
      (T.mapEquiv
        (PortBoundary.Equiv.tensorComm
          (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂))
        K)
      (T.mapEquiv (PortBoundary.Equiv.tensorEmptyRight Δ₁).symm W₁))

/-- The effective plug for the left factor of a wiring.

Given `W₂ : T.Obj (tensor (swap Γ) Δ₂)` and
`K : T.Plug (tensor Δ₁ Δ₂)`, wire them together through the `Δ₂`
boundary to obtain a plug for `tensor Δ₁ Γ`. -/
@[expose]
def wireContextLeft {Δ₁ Γ Δ₂ : PortBoundary}
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) : T.Plug (PortBoundary.tensor Δ₁ Γ) :=
  T.wire
    (Δ₁ := PortBoundary.swap Δ₁)
    (Γ := PortBoundary.swap Δ₂)
    (Δ₂ := PortBoundary.swap Γ)
    K
    (T.mapEquiv
      (PortBoundary.Equiv.tensorComm (PortBoundary.swap Γ) Δ₂)
      W₂)

/-- The effective plug for the right factor of a wiring.

Given `W₁ : T.Obj (tensor Δ₁ Γ)` and `K : T.Plug (tensor Δ₁ Δ₂)`,
wire them together through the `Δ₁` boundary to obtain a plug for
`tensor (swap Γ) Δ₂`. -/
@[expose]
def wireContextRight {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.Plug (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂) :=
  T.mapEquiv
    (PortBoundary.Equiv.tensorComm (PortBoundary.swap Δ₂) Γ)
    (T.wire
      (Δ₁ := PortBoundary.swap Δ₂)
      (Γ := PortBoundary.swap Δ₁)
      (Δ₂ := Γ)
      (T.mapEquiv
        (PortBoundary.Equiv.tensorComm
          (PortBoundary.swap Δ₁) (PortBoundary.swap Δ₂))
        K)
      W₁)

/-! ## The class -/

/--
`HasPlugFactorization T` records the five equalities the UC composition
theorems consume: `plug` is symmetric, and closing a parallel or wired
composite against a context factors through closing one component against
the residual context formed by wiring the other component into the context.

This is strictly weaker than `HasPlugWireFactor`: it asks for no unit, no
identity wire, and no snake equation, which is what lets a process model whose
coherences hold only up to a quotient declare exactly the strength it has.
-/
class HasPlugFactorization (T : UC.OpenTheory.{u}) : Prop extends IsLawful T where
  /-- The protocol and context roles of `plug` are interchangeable. -/
  plug_comm : ∀ {Δ : PortBoundary} (W : T.Obj Δ) (K : T.Obj (PortBoundary.swap Δ)),
    T.plug W K = T.plug K W
  /-- Closing a parallel composition factors through the left component. -/
  close_par_left : ∀ {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
      (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)),
    T.close (T.par W₁ W₂) K = T.close W₁ (T.parContextLeft W₂ K)
  /-- Closing a parallel composition factors through the right component. -/
  close_par_right : ∀ {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
      (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)),
    T.close (T.par W₁ W₂) K = T.close W₂ (T.parContextRight W₁ K)
  /-- Closing a wired composition factors through the left component. -/
  close_wire_left : ∀ {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
      (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)),
    T.close (T.wire W₁ W₂) K = T.close W₁ (T.wireContextLeft W₂ K)
  /-- Closing a wired composition factors through the right component. -/
  close_wire_right : ∀ {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
      (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
      (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)),
    T.close (T.wire W₁ W₂) K = T.close W₂ (T.wireContextRight W₁ K)

/-! ## Strict compact-closed theories factor -/

/-- Every theory with strict plug/wire factorization has plug factorization:
the left laws are fields of `HasPlugWireFactor`, the right laws follow by
commuting the composite, and plug symmetry follows from `plug_eq_wire` and
`wire_comm`. -/
instance (priority := 100) hasPlugFactorization_of_hasPlugWireFactor
    [HasPlugWireFactor T] : HasPlugFactorization T where
  toIsLawful := inferInstance
  plug_comm W K := by
    rw [OpenTheory.plug_eq_wire W K, OpenTheory.plug_eq_wire K W,
      OpenTheory.wire_comm]
    congr 1
    simp only [OpenTheory.mapEquiv]
    rw [← OpenTheory.map_comp, ← OpenTheory.map_comp]
    have hcomm : (PortBoundary.Equiv.tensorComm
        PortBoundary.empty PortBoundary.empty).toHom =
        PortBoundary.Hom.id _ := by
      apply PortBoundary.Hom.ext <;>
        exact PFunctor.Chart.ext _ _
          (fun a => PEmpty.elim (Sum.elim id id a))
          (fun a => PEmpty.elim (Sum.elim id id a))
    rw [hcomm, OpenTheory.map_id]
    congr 1 <;> congr 1 <;> apply PortBoundary.Hom.ext
    all_goals
      exact PFunctor.Chart.ext _ _
        (fun a => by
          first
          | cases a with
            | inl x => first | exact PEmpty.elim x | rfl
            | inr x => first | exact PEmpty.elim x | rfl
          | rfl)
        (fun a => by
          first
          | cases a with
            | inl x => first | exact PEmpty.elim x | rfl
            | inr x => first | exact PEmpty.elim x | rfl
          | rfl)
  close_par_left W₁ W₂ K := OpenTheory.plug_par_left W₁ W₂ K
  close_par_right W₁ W₂ K := by
    simp only [OpenTheory.close]
    rw [← OpenTheory.par_comm W₂ W₁, OpenTheory.map_plug, OpenTheory.plug_par_left]
    unfold parContextRight
    simp only [OpenTheory.mapEquiv]
    congr 3
  close_wire_left W₁ W₂ K := OpenTheory.plug_wire_left W₁ W₂ K
  close_wire_right {Δ₁} {Γ} {Δ₂} W₁ W₂ K := by
    simp only [OpenTheory.close]
    rw [OpenTheory.wire_comm, OpenTheory.map_plug, OpenTheory.plug_wire_left,
      OpenTheory.map_plug]
    unfold wireContextRight
    simp only [OpenTheory.mapEquiv]
    congr 1
    congr 1
    rw [← OpenTheory.map_comp]
    erw [PortBoundary.Equiv.tensorComm_comp_tensorComm Δ₁ Γ, OpenTheory.map_id]
    rfl

/-! ## The laws as theorems -/

section Laws

variable [HasPlugFactorization T]

/-- `plug` is symmetric: the protocol and context roles are interchangeable. -/
theorem plug_comm {Δ : PortBoundary} (W : T.Obj Δ) (K : T.Obj (PortBoundary.swap Δ)) :
    T.plug W K = T.plug K W :=
  HasPlugFactorization.plug_comm W K

/-- Closing a parallel composition factors through the left component.

This captures the string-diagram identity: plugging `par W₁ W₂` against
`K` is the same as plugging `W₁` against the residual context formed by
wiring `W₂` into `K`. -/
theorem close_par_left {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.close (T.par W₁ W₂) K = T.close W₁ (T.parContextLeft W₂ K) :=
  HasPlugFactorization.close_par_left W₁ W₂ K

/-- Closing a parallel composition factors through the right component. -/
theorem close_par_right {Δ₁ Δ₂ : PortBoundary} (W₁ : T.Obj Δ₁) (W₂ : T.Obj Δ₂)
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.close (T.par W₁ W₂) K = T.close W₂ (T.parContextRight W₁ K) :=
  HasPlugFactorization.close_par_right W₁ W₂ K

/-- Closing a wired composition factors through the left component. -/
theorem close_wire_left {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.close (T.wire W₁ W₂) K = T.close W₁ (T.wireContextLeft W₂ K) :=
  HasPlugFactorization.close_wire_left W₁ W₂ K

/-- Closing a wired composition factors through the right component. -/
theorem close_wire_right {Δ₁ Γ Δ₂ : PortBoundary} (W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ))
    (W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂))
    (K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)) :
    T.close (T.wire W₁ W₂) K = T.close W₂ (T.wireContextRight W₁ K) :=
  HasPlugFactorization.close_wire_right W₁ W₂ K

end Laws

end OpenTheory
end UC
end Interaction
