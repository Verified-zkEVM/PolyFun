/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.Emulates

/-!
# Dummy-adversary and split-mono reductions

In Farshim–Karvonen–Knispel–Kohlweiss–Tyagi, *UC, Categorically* (ePrint
2026/1605), completeness of the dummy adversary (Theorem III.7) says that
checking the security equation against the trivial adversary suffices, and its
split-mono strengthening (Corollary III.9, instantiated by the multiplexing
adversary in Lemma IV.3) says that security may always be checked against any
adversary that admits a retraction.

In PolyFun's context-quantified formulation the adversary face of a system is
wired against an explicit component, so the two results become statements
about wiring in a compact-closed theory:

* `emulates_wire_dummy_iff` — attaching the identity wire (the dummy
  adversary) to the adversarial face changes nothing, so emulation of the
  dummy-attached systems is emulation outright.
* `Emulates.of_wire_splitMono` — if an adversary component `A` admits a
  retraction (`wire A Rt = idWire`), then emulation of the `A`-attached
  systems already implies emulation.  Lemma IV.3's multiplexing adversary is
  one concrete such split mono.

Both need the strict zig-zag laws, so they hold for `IsCompactClosed`
theories — the free syntax models — and are *not* available for the concrete
process model `openTheory`, whose corresponding laws hold only up to
activation equivalence.  A process-model analogue would require
observation-level zig-zag laws, in the same way `Observation.RespectsPlugComm`
replaces strict plug commutation.
-/

public section

universe u

namespace Interaction
namespace UC

variable {T : OpenTheory.{u}}

/-- **Completeness of the dummy adversary, structurally** (Theorem III.7 of
*UC, Categorically*): wiring the identity wire onto the adversarial face of
both systems is invisible, so emulation of the dummy-attached systems is
exactly emulation.  The substantive direction is `mp`: checking the dummy
attachment suffices. -/
theorem emulates_wire_dummy_iff [OpenTheory.IsCompactClosed T]
    {Δm Δa : PortBoundary} {Obs : Observation T}
    {π idl : T.Obj (PortBoundary.tensor Δm Δa)} :
    Emulates (T.wire π (OpenTheory.HasIdWire.idWire (T := T) Δa))
      (T.wire idl (OpenTheory.HasIdWire.idWire (T := T) Δa)) Obs ↔
      Emulates π idl Obs := by
  rw [OpenTheory.wire_idWire_right, OpenTheory.wire_idWire_right]

/-- **Split-mono reduction** (Corollary III.9 / Lemma IV.3 of
*UC, Categorically*): if the adversary component `A` admits a retraction
`Rt`, then emulation of the `A`-attached systems implies emulation outright.
The proof re-expresses each system as its `A`-attachment wired against `Rt`
and applies `Emulates.wire_left`. -/
theorem Emulates.of_wire_splitMono [OpenTheory.IsCompactClosed T]
    {Δm Δa β : PortBoundary} {Obs : Observation T} [Obs.RespectsFactorization]
    {π idl : T.Obj (PortBoundary.tensor Δm Δa)}
    {A : T.Obj (PortBoundary.tensor (PortBoundary.swap Δa) β)}
    {Rt : T.Obj (PortBoundary.tensor (PortBoundary.swap β) Δa)}
    (hRetract : T.wire A Rt = OpenTheory.HasIdWire.idWire (T := T) Δa)
    (h : Emulates (T.wire π A) (T.wire idl A) Obs) :
    Emulates π idl Obs := by
  have hπ : π = T.wire (T.wire π A) Rt := by
    rw [OpenTheory.wire_assoc, hRetract, OpenTheory.wire_idWire_right]
  have hidl : idl = T.wire (T.wire idl A) Rt := by
    rw [OpenTheory.wire_assoc, hRetract, OpenTheory.wire_idWire_right]
  rw [hπ, hidl]
  exact h.wire_left Rt

/-- The dummy adversary is the degenerate split mono: the identity wire
retracts along itself once the zig-zag laws hold.  Stated as the `mp`
direction of `emulates_wire_dummy_iff` in split-mono form for uniformity. -/
theorem Emulates.of_wire_dummy [OpenTheory.IsCompactClosed T]
    {Δm Δa : PortBoundary} {Obs : Observation T}
    {π idl : T.Obj (PortBoundary.tensor Δm Δa)}
    (h : Emulates (T.wire π (OpenTheory.HasIdWire.idWire (T := T) Δa))
      (T.wire idl (OpenTheory.HasIdWire.idWire (T := T) Δa)) Obs) :
    Emulates π idl Obs :=
  emulates_wire_dummy_iff.mp h

end UC
end Interaction
