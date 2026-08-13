/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.Emulates
public import PolyFun.Interaction.UC.SubTheory

/-!
# Emulation relative to an allowed class of contexts

`Emulates real ideal Obs` quantifies over *every* plug.

`EmulatesWithin D real ideal Obs` restricts that quantifier to the plugs
allowed by a `SubTheory D`. It does not assert that `real` or `ideal` belongs
to `D`; those are separate protocol-membership obligations when a development
needs them.

## Main definitions

* `SubTheory.mem_parContextLeft` and its three siblings: the residual context
  formed by absorbing one component of a composite into the plug stays inside
  `D`. These are the only new facts the whole file needs, and they hold
  because the four context-formers of `Emulates` are `map`/`wire` composites.
* `EmulatesWithin D real ideal Obs`, and the composition suite relativized to
  it.
* `SubTheory.PreservesAllowedness`, the exact closure obligation on a context
  transformer.
* `UCSecureWithin`, whose simulator must preserve allowedness.

## What relativizing costs, and why that is the point

Each composition theorem gains one hypothesis: the component being held fixed
must itself be allowed. `par_left` needs `D.mem W₂` because the plug it hands
to `h₁` is built from `W₂`. So the side condition that a categorical account
of UC imposes by fiat — that the map exhibiting an emulation lies in the
allowed sub-category — is here *derived* from the shape of the factorization
argument. There is nowhere else it could come from and nowhere else it could
go.

Instantiating `D` at `SubTheory.top` discards every such hypothesis and
recovers `Emulates` exactly (`emulatesWithin_top_iff`), so nothing in this
file weakens what the unrelativized suite already proves.

## What simulator preservation says

The first conjunct of `UCSecureWithin` says only that the selected simulator
sends `D`-allowed contexts to `D`-allowed contexts. It does not supply an
algorithm, a resource bound, a realizability witness, or an efficiency proof.
Such a reading requires a separate bridge from `D.mem` to the relevant
operational or cost model.
-/

public section

universe u

namespace Interaction
namespace UC

variable {T : OpenTheory.{u}}

/-! ## Residual contexts stay allowed -/

namespace SubTheory

/-- A context transformer preserves membership in the allowed class `D`. -/
@[expose]
def PreservesAllowedness (D : SubTheory T) {Δ : PortBoundary}
    (transform : T.Plug Δ → T.Plug Δ) : Prop :=
  ∀ K : T.Plug Δ, D.mem K → D.mem (transform K)

/-- Absorbing the right component of a `par` into an allowed plug yields an
allowed plug, since `parContextLeft` is a `wire` followed by a `map`. -/
theorem mem_parContextLeft {D : SubTheory T} {Δ₁ Δ₂ : PortBoundary} {W₂ : T.Obj Δ₂}
    {K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)} (hK : D.mem K) (hW₂ : D.mem W₂) :
    D.mem (T.parContextLeft W₂ K) :=
  D.mem_map _ (D.mem_wire hK (D.mem_map _ hW₂))

/-- Absorbing the left component of a `par` into an allowed plug yields an
allowed plug. -/
theorem mem_parContextRight {D : SubTheory T} {Δ₁ Δ₂ : PortBoundary} {W₁ : T.Obj Δ₁}
    {K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)} (hK : D.mem K) (hW₁ : D.mem W₁) :
    D.mem (T.parContextRight W₁ K) :=
  D.mem_map _ (D.mem_wire (D.mem_map _ hK) (D.mem_map _ hW₁))

/-- Absorbing the right factor of a `wire` into an allowed plug yields an
allowed plug. -/
theorem mem_wireContextLeft {D : SubTheory T} {Δ₁ Γ Δ₂ : PortBoundary}
    {W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    {K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)} (hK : D.mem K) (hW₂ : D.mem W₂) :
    D.mem (T.wireContextLeft W₂ K) :=
  D.mem_wire hK (D.mem_map _ hW₂)

/-- Absorbing the left factor of a `wire` into an allowed plug yields an
allowed plug. -/
theorem mem_wireContextRight {D : SubTheory T} {Δ₁ Γ Δ₂ : PortBoundary}
    {W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    {K : T.Plug (PortBoundary.tensor Δ₁ Δ₂)} (hK : D.mem K) (hW₁ : D.mem W₁) :
    D.mem (T.wireContextRight W₁ K) :=
  D.mem_map _ (D.mem_wire (D.mem_map _ hK) hW₁)

end SubTheory

/-! ## The relativized emulation judgment -/

/--
`EmulatesWithin D real ideal Obs` says `real` emulates `ideal` against every
context that the sub-theory `D` allows.

This is `Emulates` with its plug quantifier cut down to `D`. Since `D` shrinks
the set of distinguishers, the judgment is *antitone* in `D`
(`EmulatesWithin.mono`): a smaller allowed class is a weaker security claim.
-/
structure EmulatesWithin (D : SubTheory T) {Δ : PortBoundary} (real ideal : T.Obj Δ)
    (Obs : Observation T) : Prop where
  /-- Every allowed context sees `real` and `ideal` as `Obs`-related. -/
  compare : ∀ K : T.Plug Δ, D.mem K → Obs.rel (T.close real K) (T.close ideal K)

namespace EmulatesWithin

/-- Every open system emulates itself relative to any allowed class. -/
theorem refl (D : SubTheory T) {Δ : PortBoundary} (Obs : Observation T) (W : T.Obj Δ) :
    EmulatesWithin D W W Obs :=
  ⟨fun _ _ => Obs.equiv.refl _⟩

/-- Relativized emulation is symmetric. -/
theorem symm {D : SubTheory T} {Δ : PortBoundary} {Obs : Observation T} {W₁ W₂ : T.Obj Δ}
    (h : EmulatesWithin D W₁ W₂ Obs) : EmulatesWithin D W₂ W₁ Obs :=
  ⟨fun K hK => Obs.equiv.symm (h.compare K hK)⟩

/-- Relativized emulation composes transitively. -/
theorem trans {D : SubTheory T} {Δ : PortBoundary} {Obs : Observation T} {W₁ W₂ W₃ : T.Obj Δ}
    (h₁₂ : EmulatesWithin D W₁ W₂ Obs) (h₂₃ : EmulatesWithin D W₂ W₃ Obs) :
    EmulatesWithin D W₁ W₃ Obs :=
  ⟨fun K hK => Obs.equiv.trans (h₁₂.compare K hK) (h₂₃.compare K hK)⟩

/--
Shrinking the allowed class weakens the judgment.

Read the other way: a claim proved against a large class of contexts holds
against every smaller one.
-/
theorem mono {D₁ D₂ : SubTheory T} (hD : D₁ ≤ D₂) {Δ : PortBoundary} {Obs : Observation T}
    {real ideal : T.Obj Δ} (h : EmulatesWithin D₂ real ideal Obs) :
    EmulatesWithin D₁ real ideal Obs :=
  ⟨fun K hK => h.compare K (hD K hK)⟩

/-- Adapting both sides along the same boundary morphism preserves relativized
emulation. The adapted context is allowed because `D` is closed under `map`. -/
theorem map_invariance [OpenTheory.IsLawfulPlug T] {D : SubTheory T} {Δ₁ Δ₂ : PortBoundary}
    {Obs : Observation T} (f : PortBoundary.Hom Δ₁ Δ₂) {real ideal : T.Obj Δ₁}
    (h : EmulatesWithin D real ideal Obs) :
    EmulatesWithin D (T.map f real) (T.map f ideal) Obs :=
  ⟨fun K hK => by
    simp only [OpenTheory.close,
      OpenTheory.map_plug f real K, OpenTheory.map_plug f ideal K]
    exact h.compare _ (D.mem_map _ hK)⟩

end EmulatesWithin

/-! ## Reconciliation with the unrelativized judgment -/

/-- An unrestricted emulation is an emulation relative to any allowed class:
restricting the contexts can only discard obligations. -/
theorem Emulates.toEmulatesWithin (D : SubTheory T) {Δ : PortBoundary} {Obs : Observation T}
    {real ideal : T.Obj Δ} (h : Emulates real ideal Obs) : EmulatesWithin D real ideal Obs :=
  ⟨fun K _ => h.compare K⟩

/--
Relativizing to the class that allows everything is a no-op.

This is the machine-checked form of the claim that this file is a
conservative extension: every theorem below specializes at
`SubTheory.top` to the corresponding theorem about `Emulates`.
-/
theorem emulatesWithin_top_iff {Δ : PortBoundary} {Obs : Observation T}
    {real ideal : T.Obj Δ} :
    EmulatesWithin (SubTheory.top T) real ideal Obs ↔ Emulates real ideal Obs :=
  ⟨fun h => ⟨fun K => h.compare K trivial⟩, fun h => ⟨fun K _ => h.compare K⟩⟩

/-! ## Relativized UC composition theorems -/

namespace EmulatesWithin

/--
Replacing the left component of a parallel composition preserves relativized
emulation.

The new hypothesis `hW₂` is the one the abstract theory imposes as a
convention: the untouched component must itself be an allowed system. It is
needed here because the plug handed to `h₁` is built by absorbing `W₂` into
the ambient context.
-/
theorem par_left {D : SubTheory T} {Δ₁ Δ₂ : PortBoundary} {Obs : Observation T}
    [Obs.RespectsFactorization] {real₁ ideal₁ : T.Obj Δ₁}
    (h₁ : EmulatesWithin D real₁ ideal₁ Obs) {W₂ : T.Obj Δ₂} (hW₂ : D.mem W₂) :
    EmulatesWithin D (T.par real₁ W₂) (T.par ideal₁ W₂) Obs :=
  ⟨fun K hK => Obs.equiv.trans
    (Observation.RespectsFactorization.close_par_left real₁ W₂ K)
    (Obs.equiv.trans (h₁.compare _ (SubTheory.mem_parContextLeft hK hW₂))
      (Obs.equiv.symm (Observation.RespectsFactorization.close_par_left ideal₁ W₂ K)))⟩

/-- Replacing the right component of a parallel composition preserves
relativized emulation. -/
theorem par_right {D : SubTheory T} {Δ₁ Δ₂ : PortBoundary} {Obs : Observation T}
    [Obs.RespectsFactorization] {W₁ : T.Obj Δ₁} (hW₁ : D.mem W₁)
    {real₂ ideal₂ : T.Obj Δ₂} (h₂ : EmulatesWithin D real₂ ideal₂ Obs) :
    EmulatesWithin D (T.par W₁ real₂) (T.par W₁ ideal₂) Obs :=
  ⟨fun K hK => Obs.equiv.trans
    (Observation.RespectsFactorization.close_par_right W₁ real₂ K)
    (Obs.equiv.trans (h₂.compare _ (SubTheory.mem_parContextRight hK hW₁))
      (Obs.equiv.symm (Observation.RespectsFactorization.close_par_right W₁ ideal₂ K)))⟩

/--
**Relativized UC composition theorem for `par`.**

The real right component and ideal left component must be allowed: the hybrid
argument passes through `T.par ideal₁ real₂`, and each leg absorbs the other
component into the context.
-/
theorem par_compose {D : SubTheory T} {Δ₁ Δ₂ : PortBoundary} {Obs : Observation T}
    [Obs.RespectsFactorization] {real₁ ideal₁ : T.Obj Δ₁} {real₂ ideal₂ : T.Obj Δ₂}
    (h₁ : EmulatesWithin D real₁ ideal₁ Obs) (h₂ : EmulatesWithin D real₂ ideal₂ Obs)
    (hReal₂ : D.mem real₂) (hIdeal₁ : D.mem ideal₁) :
    EmulatesWithin D (T.par real₁ real₂) (T.par ideal₁ ideal₂) Obs :=
  EmulatesWithin.trans (par_left h₁ hReal₂) (par_right hIdeal₁ h₂)

/-- Replacing the left factor of a wiring preserves relativized emulation. -/
theorem wire_left {D : SubTheory T} {Δ₁ Γ Δ₂ : PortBoundary} {Obs : Observation T}
    [Obs.RespectsFactorization] {real₁ ideal₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    (h₁ : EmulatesWithin D real₁ ideal₁ Obs)
    {W₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)} (hW₂ : D.mem W₂) :
    EmulatesWithin D (T.wire real₁ W₂) (T.wire ideal₁ W₂) Obs :=
  ⟨fun K hK => Obs.equiv.trans
    (Observation.RespectsFactorization.close_wire_left real₁ W₂ K)
    (Obs.equiv.trans (h₁.compare _ (SubTheory.mem_wireContextLeft hK hW₂))
      (Obs.equiv.symm (Observation.RespectsFactorization.close_wire_left ideal₁ W₂ K)))⟩

/-- Replacing the right factor of a wiring preserves relativized emulation. -/
theorem wire_right {D : SubTheory T} {Δ₁ Γ Δ₂ : PortBoundary} {Obs : Observation T}
    [Obs.RespectsFactorization] {W₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)} (hW₁ : D.mem W₁)
    {real₂ ideal₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₂ : EmulatesWithin D real₂ ideal₂ Obs) :
    EmulatesWithin D (T.wire W₁ real₂) (T.wire W₁ ideal₂) Obs :=
  ⟨fun K hK => Obs.equiv.trans
    (Observation.RespectsFactorization.close_wire_right W₁ real₂ K)
    (Obs.equiv.trans (h₂.compare _ (SubTheory.mem_wireContextRight hK hW₁))
      (Obs.equiv.symm (Observation.RespectsFactorization.close_wire_right W₁ ideal₂ K)))⟩

/-- **Relativized UC composition theorem for `wire`.** -/
theorem wire_compose {D : SubTheory T} {Δ₁ Γ Δ₂ : PortBoundary} {Obs : Observation T}
    [Obs.RespectsFactorization] {real₁ ideal₁ : T.Obj (PortBoundary.tensor Δ₁ Γ)}
    {real₂ ideal₂ : T.Obj (PortBoundary.tensor (PortBoundary.swap Γ) Δ₂)}
    (h₁ : EmulatesWithin D real₁ ideal₁ Obs) (h₂ : EmulatesWithin D real₂ ideal₂ Obs)
    (hReal₂ : D.mem real₂) (hIdeal₁ : D.mem ideal₁) :
    EmulatesWithin D (T.wire real₁ real₂) (T.wire ideal₁ ideal₂) Obs :=
  EmulatesWithin.trans (wire_left h₁ hReal₂) (wire_right hIdeal₁ h₂)

/--
Replacing the plug while keeping the system fixed preserves observational
equivalence, provided the fixed system is itself allowed — it becomes the
context after `plug_comm` exchanges the two roles.
-/
theorem plug_right {D : SubTheory T} {Δ : PortBoundary} {Obs : Observation T}
    [Obs.RespectsPlugComm] {W : T.Obj Δ} (hW : D.mem W) {K₁ K₂ : T.Plug Δ}
    (hK : EmulatesWithin D K₁ K₂ Obs) : Obs.rel (T.close W K₁) (T.close W K₂) :=
  Obs.equiv.trans (Observation.RespectsPlugComm.plug_comm W K₁)
    (Obs.equiv.trans (hK.compare W hW)
      (Obs.equiv.symm (Observation.RespectsPlugComm.plug_comm W K₂)))

/--
**Relativized UC composition theorem for `plug`.**

The hybrid runs through `T.close ideal K_real`, so the real context must be
allowed for the first leg and the ideal system must be allowed for the second,
where it plays the role of the context.
-/
theorem plug_compose {D : SubTheory T} {Δ : PortBoundary} {Obs : Observation T}
    [Obs.RespectsPlugComm] {real ideal : T.Obj Δ} {K_real K_ideal : T.Plug Δ}
    (hProt : EmulatesWithin D real ideal Obs) (hEnv : EmulatesWithin D K_real K_ideal Obs)
    (hKreal : D.mem K_real) (hIdeal : D.mem ideal) :
    Obs.rel (T.close real K_real) (T.close ideal K_ideal) :=
  Obs.equiv.trans (hProt.compare K_real hKreal) (plug_right hIdeal hEnv)

end EmulatesWithin

/-! ## Relativized UC security -/

/--
`UCSecureWithin D protocol ideal Obs SimSpace simulate` is UC security with an
existential simulator, relative to the allowed class `D`.

Two things change relative to `UCSecure`. The context quantifier is cut down
to `D`, and the selected simulator must satisfy
`SubTheory.PreservesAllowedness D`. Neither protocol membership nor simulator
realizability or efficiency follows from this definition.
-/
def UCSecureWithin (D : SubTheory T) {Δ : PortBoundary} (protocol ideal : T.Obj Δ)
    (Obs : Observation T) (SimSpace : Type*) (simulate : SimSpace → T.Plug Δ → T.Plug Δ) : Prop :=
  ∃ s : SimSpace,
    D.PreservesAllowedness (simulate s) ∧
    (∀ K : T.Plug Δ, D.mem K → Obs.rel (T.close protocol K) (T.close ideal (simulate s K)))

/-- Relativized emulation implies relativized UC security with the identity
simulator, which trivially preserves the allowed class. -/
theorem EmulatesWithin.toUCSecureWithin {D : SubTheory T} {Δ : PortBoundary}
    {protocol ideal : T.Obj Δ} {Obs : Observation T}
    (h : EmulatesWithin D protocol ideal Obs) :
    UCSecureWithin D protocol ideal Obs PUnit (fun _ K => K) :=
  ⟨⟨⟩, fun _ hK => hK, h.compare⟩

/-- Relativized UC security with identity simulation recovers relativized
emulation. -/
theorem UCSecureWithin.toEmulatesWithin_id {D : SubTheory T} {Δ : PortBoundary}
    {protocol ideal : T.Obj Δ} {Obs : Observation T}
    (hSec : UCSecureWithin D protocol ideal Obs PUnit (fun _ K => K)) :
    EmulatesWithin D protocol ideal Obs :=
  let ⟨_, _, h⟩ := hSec; ⟨h⟩

/-- Relativizing UC security to the class that allows everything recovers
`UCSecure`. -/
theorem ucSecureWithin_top_iff {Δ : PortBoundary} {protocol ideal : T.Obj Δ}
    {Obs : Observation T} {SimSpace : Type*} {simulate : SimSpace → T.Plug Δ → T.Plug Δ} :
    UCSecureWithin (SubTheory.top T) protocol ideal Obs SimSpace simulate ↔
      UCSecure protocol ideal Obs SimSpace simulate :=
  ⟨fun ⟨s, _, h⟩ => ⟨s, fun K => h K trivial⟩,
    fun ⟨s, h⟩ => ⟨s, fun _ _ => trivial, fun K _ => h K⟩⟩

end UC
end Interaction
