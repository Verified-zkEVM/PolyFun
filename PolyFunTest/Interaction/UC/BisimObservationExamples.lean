/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import PolyFun.Interaction.UC.BisimObservation

/-!
# Examples: UC emulation up to weak bisimulation

Type-level regression tests that the `Observation.bisim` bridge and the
`plug`-composition-up-to-bisimulation result are usable as UC judgments. These
exercise the API that connects the generic `Control.WeakBisim` theory (through
`OpenProcessIso`) to `Emulates` for the concrete process model `openTheory`.
-/

namespace Interaction
namespace UC
namespace BisimObservationExamples

universe u v w w'

variable {Party : Type u} {m : Type w → Type w'} {schedulerSampler : m (ULift.{w, 0} Bool)}
variable {Δ : PortBoundary}

/-- Every open system UC-emulates itself up to weak bisimulation. -/
example (W : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ) :
    Emulates W W (Observation.bisim Party m schedulerSampler) :=
  Emulates.refl _ W

/-- `Observation.bisim` relates a closed system to itself (reflexivity of the
underlying `OpenProcessIso`, obtained from the generic theory). -/
example (c : (openTheory.{u, v, w, w'} Party m schedulerSampler).Closed) :
    (Observation.bisim Party m schedulerSampler).rel c c :=
  (Observation.bisim Party m schedulerSampler).equiv.refl c

/-- **UC `plug`-composition up to weak bisimulation** is available for the
concrete process model: given protocol and environment emulations under
`Observation.bisim`, the closed executions are weakly bisimilar. This is the
judgment that the abstract `Emulates.plug_compose` cannot deliver for
`openTheory` (which is not `HasPlugWireFactor`). -/
example
    {real ideal : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ}
    {K_real K_ideal :
      (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj (PortBoundary.swap Δ)}
    (hProt : Emulates real ideal (Observation.bisim Party m schedulerSampler))
    (hEnv : Emulates K_real K_ideal (Observation.bisim Party m schedulerSampler)) :
    OpenProcessIso
      ((openTheory Party m schedulerSampler).close real K_real)
      ((openTheory Party m schedulerSampler).close ideal K_ideal) :=
  Emulates.plug_compose_bisim hProt hEnv

end BisimObservationExamples
end UC
end Interaction
