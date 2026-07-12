/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import PolyFun.Interaction.UC.Emulates
import PolyFun.Interaction.UC.OpenProcessModel
import PolyFun.Interaction.UC.OpenProcessBisim

/-!
# Weak bisimulation as a UC observation

`Emulates` (in `Emulates.lean`) judges UC security through an abstract
`Observation` — a bundled `Equivalence` on the closed systems of an open
theory — and its canonical instance `Observation.eq` uses perfect *syntactic*
equality. This file supplies the intended-but-previously-missing behavioural
instance for the concrete process model `openTheory`: the silent-step-absorbing
weak bisimulation `OpenProcessIso`, restricted to closed systems
(`Δ = PortBoundary.empty`), packaged as `Observation.bisim`.

With this bridge, `Emulates real ideal (Observation.bisim …)` is UC emulation
*up to weak bisimulation*: `real` and `ideal` need not be syntactically equal
once closed against any context — only observationally indistinguishable modulo
internal silent (unactivated / scheduler) steps. This is the seam through which
the dynamical/interaction-tree bisimulation theory reaches the UC judgment.

## Main definitions

* `Observation.bisim` — `OpenProcessIso` on closed open-processes as an
  `Observation (openTheory …)`. Its `Equivalence` proof is
  `OpenProcessIso.{refl, symm, trans}` (classical: `trans` uses `Classical.em`
  to case-split on whether an intermediate step is silent).

The `plug`-composition consequence — that `Emulates … Observation.bisim`
composes for the concrete model, which is *not* `HasPlugWireFactor` on the nose —
is developed alongside `openTheory_plug_comm_iso` (`OpenProcessModel.lean`) and
the `Obs.rel`-generalized `Emulates.plug_compose` (`Emulates.lean`).
-/

universe u v w w'

namespace Interaction
namespace UC

variable {Party : Type u} {m : Type w → Type w'} {schedulerSampler : m (ULift.{w, 0} Bool)}

/--
Weak bisimulation of closed open-processes, as an observation relation for the
concrete process theory `openTheory`.

The underlying relation is `OpenProcessIso` at the empty boundary,
i.e. on `T.Closed = OpenProcess m Party PortBoundary.empty`. Reflexivity,
symmetry, and transitivity are the already-proven `OpenProcessIso` laws.
-/
def Observation.bisim (Party : Type u) (m : Type w → Type w')
    (schedulerSampler : m (ULift.{w, 0} Bool)) :
    Observation (openTheory.{u, v, w, w'} Party m schedulerSampler) where
  rel := OpenProcessIso
  -- The equivalence proof is inherited from the generic `Control.WeakBisim`
  -- theory (`OpenProcessBisim.lean`), grounding the UC observation in the
  -- reusable bisimulation framework rather than the hand-rolled process proofs.
  equiv :=
    { refl := OpenProcessIso.refl'
      symm := OpenProcessIso.symm'
      trans := OpenProcessIso.trans' }

@[simp]
theorem Observation.bisim_rel
    {c₁ c₂ : (openTheory.{u, v, w, w'} Party m schedulerSampler).Closed} :
    (Observation.bisim.{u, v, w, w'} Party m schedulerSampler).rel c₁ c₂ ↔
      OpenProcessIso c₁ c₂ :=
  Iff.rfl

/-! ## UC `plug`-composition for real processes, up to bisimulation

The concrete `openTheory` is not `HasPlugWireFactor` on the nose, so the
`[HasPlugWireFactor]` UC composition theorems in `Emulates.lean` do not apply to
it. The `Obs.rel`-generalized `Emulates.plug_compose_of_commObs` does — once its
commutation hypothesis is discharged by `openTheory_plug_comm_iso`. -/

variable {Δ : PortBoundary}

/-- `plug` commutes up to `Observation.bisim`: the discharge of the commutation
hypothesis of `Emulates.plug_compose_of_commObs` for the concrete process model.
This is exactly `openTheory_plug_comm_iso` read through the `Observation.bisim`
relation. -/
theorem bisim_plug_comm
    (W : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ)
    (K : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj (PortBoundary.swap Δ)) :
    (Observation.bisim.{u, v, w, w'} Party m schedulerSampler).rel
      ((openTheory Party m schedulerSampler).plug W K)
      ((openTheory Party m schedulerSampler).plug K W) :=
  openTheory_plug_comm_iso Party m schedulerSampler W K

/-- **UC `plug`-composition for real processes, judged up to weak bisimulation.**
If a protocol emulates its ideal and an environment emulates its ideal — both
under `Observation.bisim` — then the closed real-world and ideal-world executions
are weakly bisimilar. This is the concrete instantiation of
`Emulates.plug_compose_of_commObs` that the abstract `Emulates.plug_compose`
cannot deliver for `openTheory` (which lacks strict compact-closed structure). -/
theorem Emulates.plug_compose_bisim
    {real ideal : (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj Δ}
    {K_real K_ideal :
      (openTheory.{u, v, w, w'} Party m schedulerSampler).Obj (PortBoundary.swap Δ)}
    (hProt : Emulates real ideal (Observation.bisim Party m schedulerSampler))
    (hEnv : Emulates K_real K_ideal (Observation.bisim Party m schedulerSampler)) :
    (Observation.bisim Party m schedulerSampler).rel
      ((openTheory Party m schedulerSampler).close real K_real)
      ((openTheory Party m schedulerSampler).close ideal K_ideal) :=
  Emulates.plug_compose_of_commObs bisim_plug_comm hProt hEnv

end UC
end Interaction
