/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.EmulatesWithin

/-!
# Emulation in the presence of a global subroutine

A *global* resource is one that both a protocol and the surrounding world may
use: a shared clock, a common reference string, a global PKI.  Following
Farshim–Karvonen–Knispel–Kohlweiss–Tyagi, *UC, Categorically* (ePrint
2026/1605, Definition III.13), emulation with a global resource `G` is ordinary
emulation of the wired composites: `real` emulates `ideal` with global `G`
when `wire real G` emulates `wire ideal G`.

`OpenTheory.withGlobal` forms that composite: the protocol exposes an honest
face `Δ` and a subroutine face `Γ`; the global resource consumes `Γ` and
exposes its remaining world-facing boundary `E`.  The paper's
`(id ⊗ r) ∘ γ` composite is stated here in the wire-composed form native to
`OpenTheory`; the strict compact-closed reassociation between the two
presentations is not asserted.

The universal-composition theorem with global subroutines (Theorem III.14, the
static-system UCGS theorem) then follows from the existing wire composition
suite: an outer protocol wired onto the composite's honest face preserves
emulation, with the global resource left in place.  This is exactly the
paper's proof, which derives Theorem III.14 by applying the composition
theorem to the `γ`-hybrid resources.

Relativized variants restrict the closing contexts to a `SubTheory` and
additionally require the wired-in systems to be allowed, mirroring
`EmulatesWithin`.
-/

public section

universe u

namespace Interaction
namespace UC

variable {T : OpenTheory.{u}}

/-! ## The global-resource composite -/

/-- Wire a global resource `G` onto the subroutine face `Γ` of an open system.
The result exposes the system's honest face `Δ` together with the global
resource's world-facing boundary `E`. -/
def OpenTheory.withGlobal {Δ Γ E : PortBoundary}
    (W : T.Obj (PortBoundary.tensor Δ Γ))
    (G : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E)) :
    T.Obj (PortBoundary.tensor Δ E) :=
  T.wire W G

/-- `EmulatesWithGlobal G real ideal Obs` says `real` emulates `ideal` in the
presence of the shared global resource `G`: the two `G`-composites are
contextually indistinguishable under `Obs`.

This is Definition III.13 of *UC, Categorically*: emulation with a global
resource is ordinary emulation of the wired composites. -/
def EmulatesWithGlobal {Δ Γ E : PortBoundary}
    (G : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E))
    (real ideal : T.Obj (PortBoundary.tensor Δ Γ)) (Obs : Observation T) : Prop :=
  Emulates (T.withGlobal real G) (T.withGlobal ideal G) Obs

namespace EmulatesWithGlobal

variable {Δ Γ E : PortBoundary} {Obs : Observation T}
  {G : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E)}

/-- Every open system emulates itself in the presence of any global resource. -/
theorem refl (G : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E))
    (Obs : Observation T) (W : T.Obj (PortBoundary.tensor Δ Γ)) :
    EmulatesWithGlobal G W W Obs :=
  Emulates.refl Obs (T.withGlobal W G)

/-- Emulation with a global resource is symmetric. -/
theorem symm {real ideal : T.Obj (PortBoundary.tensor Δ Γ)}
    (h : EmulatesWithGlobal G real ideal Obs) : EmulatesWithGlobal G ideal real Obs :=
  Emulates.symm h

/-- Emulation with a global resource composes transitively. -/
theorem trans {W₁ W₂ W₃ : T.Obj (PortBoundary.tensor Δ Γ)}
    (h₁₂ : EmulatesWithGlobal G W₁ W₂ Obs) (h₂₃ : EmulatesWithGlobal G W₂ W₃ Obs) :
    EmulatesWithGlobal G W₁ W₃ Obs :=
  Emulates.trans h₁₂ h₂₃

end EmulatesWithGlobal

/-- Unconditional emulation survives sharing any global resource: wiring the
same `G` onto both sides preserves emulation. -/
theorem Emulates.toEmulatesWithGlobal {Δ Γ E : PortBoundary} {Obs : Observation T}
    [Obs.RespectsFactorization] {real ideal : T.Obj (PortBoundary.tensor Δ Γ)}
    (h : Emulates real ideal Obs)
    (G : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E)) :
    EmulatesWithGlobal G real ideal Obs :=
  h.wire_left G

namespace EmulatesWithGlobal

variable {Δ Γ E : PortBoundary} {Obs : Observation T}
  {G : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E)}

/-- Replacing the global resource by one that emulates it preserves emulation
with a global resource. -/
theorem congr_global [Obs.RespectsFactorization]
    {G' : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E)}
    {real ideal : T.Obj (PortBoundary.tensor Δ Γ)}
    (hG : Emulates G G' Obs) (h : EmulatesWithGlobal G real ideal Obs) :
    EmulatesWithGlobal G' real ideal Obs :=
  Emulates.trans (Emulates.wire_right real hG.symm)
    (Emulates.trans h (Emulates.wire_right ideal hG))

/-- **Universal composition with global subroutines** (Theorem III.14 of
*UC, Categorically*, the static-system UCGS theorem): an outer protocol `ρ`
wired onto the honest face of the `G`-composite preserves emulation with the
global resource left in place. -/
theorem wire_outer [Obs.RespectsFactorization] {Δ' : PortBoundary}
    {real ideal : T.Obj (PortBoundary.tensor Δ Γ)}
    (ρ : T.Obj (PortBoundary.tensor Δ' (PortBoundary.swap Δ)))
    (h : EmulatesWithGlobal G real ideal Obs) :
    Emulates
      (T.wire (Γ := PortBoundary.swap Δ) ρ (T.withGlobal real G))
      (T.wire (Γ := PortBoundary.swap Δ) ρ (T.withGlobal ideal G)) Obs :=
  Emulates.wire_right (Γ := PortBoundary.swap Δ) ρ h

/-- Simultaneously replace the outer protocol and the `G`-hybrid: the combined
form of `wire_outer` and outer-protocol emulation. -/
theorem wire_compose_outer [Obs.RespectsFactorization] {Δ' : PortBoundary}
    {real ideal : T.Obj (PortBoundary.tensor Δ Γ)}
    {ρ ρ' : T.Obj (PortBoundary.tensor Δ' (PortBoundary.swap Δ))}
    (houter : Emulates ρ ρ' Obs) (h : EmulatesWithGlobal G real ideal Obs) :
    Emulates
      (T.wire (Γ := PortBoundary.swap Δ) ρ (T.withGlobal real G))
      (T.wire (Γ := PortBoundary.swap Δ) ρ' (T.withGlobal ideal G)) Obs :=
  Emulates.wire_compose (Γ := PortBoundary.swap Δ) houter h

end EmulatesWithGlobal

/-! ## Relativized variants -/

/-- Emulation with a global resource against the contexts allowed by a
sub-theory `D`: the relativization of `EmulatesWithGlobal`, mirroring
`EmulatesWithin`. -/
def EmulatesWithGlobalWithin (D : SubTheory T) {Δ Γ E : PortBoundary}
    (G : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E))
    (real ideal : T.Obj (PortBoundary.tensor Δ Γ)) (Obs : Observation T) : Prop :=
  EmulatesWithin D (T.withGlobal real G) (T.withGlobal ideal G) Obs

/-- Relativized emulation survives sharing an *allowed* global resource. -/
theorem EmulatesWithin.toEmulatesWithGlobalWithin {D : SubTheory T}
    {Δ Γ E : PortBoundary} {Obs : Observation T} [Obs.RespectsFactorization]
    {real ideal : T.Obj (PortBoundary.tensor Δ Γ)}
    (h : EmulatesWithin D real ideal Obs)
    {G : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E)} (hG : D.mem G) :
    EmulatesWithGlobalWithin D G real ideal Obs :=
  h.wire_left hG

/-- Relativized universal composition with global subroutines: an *allowed*
outer protocol wired onto the honest face of the `G`-composite preserves
relativized emulation. -/
theorem EmulatesWithGlobalWithin.wire_outer {D : SubTheory T}
    {Δ Γ E Δ' : PortBoundary} {Obs : Observation T} [Obs.RespectsFactorization]
    {G : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) E)}
    {real ideal : T.Obj (PortBoundary.tensor Δ Γ)}
    {ρ : T.Obj (PortBoundary.tensor Δ' (PortBoundary.swap Δ))} (hρ : D.mem ρ)
    (h : EmulatesWithGlobalWithin D G real ideal Obs) :
    EmulatesWithin D
      (T.wire (Γ := PortBoundary.swap Δ) ρ (T.withGlobal real G))
      (T.wire (Γ := PortBoundary.swap Δ) ρ (T.withGlobal ideal G)) Obs :=
  EmulatesWithin.wire_right (Γ := PortBoundary.swap Δ) hρ h

end UC
end Interaction
