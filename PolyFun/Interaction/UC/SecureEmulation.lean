/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import all PolyFun.Interaction.UC.Emulates
import all PolyFun.Interaction.UC.EmulatesWithin
public import PolyFun.Interaction.UC.EmulatesWithin

/-!
# Secure emulation as a preorder

`Emulates` is symmetric: it demands that every context sees the two systems as
equivalent, with no simulator.  The simulation paradigm of UC is asymmetric —
`real` securely emulates `ideal` when some context transformer (the simulator)
makes the ideal world explain every real-world observation.  `UCSecure`
carries that simulator over an explicitly pinned parameter space;
`SecurelyEmulates` is its fully existential form, quantifying over arbitrary
context transformers.

This existential form is what orders open systems.  Appendix A of
Farshim–Karvonen–Knispel–Kohlweiss–Tyagi, *UC, Categorically* (ePrint
2026/1605) observes that "`real` is securely emulated by `ideal`" is a
preorder on resources — reflexive by the identity simulator, transitive by
composing simulators — and assembles the category of resources and secure
emulations from it by a Grothendieck construction.  `securelyEmulatesPreorder`
packages the preorder; the Grothendieck packaging is deliberately not built
until a consumer exists (see `docs/wiki/uc.md`).

Monotonicity of `SecurelyEmulates` under `par` and `wire` is *not* provable in
this context-transformer form: moving a simulator across a parallel
composition requires representing it as an open system and bending its wires
through compact-closed structure, which the concrete process model does not
strictly possess.  A structural-simulator variant (the simulator as a
`T.Obj` applied by `wire`) is the faithful rendering of the paper's
morphism-level simulators and remains future work.

Naming: `SecurelyEmulates` follows the paper's "secure emulation".  The word
"realizes" is deliberately avoided: in PolyFun, realizability refers to the
machine-realizability layer in `PolyFun.Realizability`.
-/

public section

universe u

namespace Interaction
namespace UC

variable {T : OpenTheory.{u}}

/-! ## The existential-simulator judgment -/

/-- `SecurelyEmulates real ideal Obs` says some context transformer (the
simulator) makes the ideal world explain every closed real-world execution:
the fully existential form of `UCSecure`.

Unlike `Emulates` this judgment is directional; it is reflexive and
transitive but not symmetric. -/
def SecurelyEmulates {Δ : PortBoundary} (real ideal : T.Obj Δ)
    (Obs : Observation T) : Prop :=
  ∃ simulate : T.Plug Δ → T.Plug Δ,
    ∀ K : T.Plug Δ, Obs.rel (T.close real K) (T.close ideal (simulate K))

namespace SecurelyEmulates

variable {Δ : PortBoundary} {Obs : Observation T}

/-- Every open system securely emulates itself via the identity simulator. -/
theorem refl (Obs : Observation T) (W : T.Obj Δ) : SecurelyEmulates W W Obs :=
  ⟨id, fun _ => Obs.equiv.refl _⟩

/-- Secure emulations compose: the composite simulator applies the first
simulator and then the second. -/
theorem trans {W₁ W₂ W₃ : T.Obj Δ} (h₁₂ : SecurelyEmulates W₁ W₂ Obs)
    (h₂₃ : SecurelyEmulates W₂ W₃ Obs) : SecurelyEmulates W₁ W₃ Obs := by
  obtain ⟨f₁, hf₁⟩ := h₁₂
  obtain ⟨f₂, hf₂⟩ := h₂₃
  exact ⟨f₂ ∘ f₁, fun K => Obs.equiv.trans (hf₁ K) (hf₂ (f₁ K))⟩

/-- Replacing the real system by one that unconditionally emulates it
preserves secure emulation. -/
theorem congr_left {real' real ideal : T.Obj Δ} (h : Emulates real' real Obs)
    (hsec : SecurelyEmulates real ideal Obs) :
    SecurelyEmulates real' ideal Obs := by
  obtain ⟨f, hf⟩ := hsec
  exact ⟨f, fun K => Obs.equiv.trans (h.compare K) (hf K)⟩

/-- Replacing the ideal system by one that unconditionally emulates it
preserves secure emulation. -/
theorem congr_right {real ideal ideal' : T.Obj Δ} (h : Emulates ideal ideal' Obs)
    (hsec : SecurelyEmulates real ideal Obs) :
    SecurelyEmulates real ideal' Obs := by
  obtain ⟨f, hf⟩ := hsec
  exact ⟨f, fun K => Obs.equiv.trans (hf K) (h.compare (f K))⟩

end SecurelyEmulates

/-- Unconditional emulation is secure emulation via the identity simulator. -/
theorem Emulates.toSecurelyEmulates {Δ : PortBoundary} {Obs : Observation T}
    {real ideal : T.Obj Δ} (h : Emulates real ideal Obs) :
    SecurelyEmulates real ideal Obs :=
  ⟨id, h.compare⟩

/-- UC security at any pinned simulator space yields secure emulation. -/
theorem UCSecure.toSecurelyEmulates {Δ : PortBoundary} {Obs : Observation T}
    {protocol ideal : T.Obj Δ} {SimSpace : Type*}
    {simulate : SimSpace → T.Plug Δ → T.Plug Δ}
    (h : UCSecure protocol ideal Obs SimSpace simulate) :
    SecurelyEmulates protocol ideal Obs := by
  obtain ⟨s, hs⟩ := h
  exact ⟨simulate s, hs⟩

/-- Secure emulation is UC security over the full transformer space. -/
theorem SecurelyEmulates.toUCSecure {Δ : PortBoundary} {Obs : Observation T}
    {protocol ideal : T.Obj Δ} (h : SecurelyEmulates protocol ideal Obs) :
    UCSecure protocol ideal Obs (T.Plug Δ → T.Plug Δ) (fun f => f) :=
  h

/-! ## The emulation preorder -/

/-- Secure emulation orders the open systems at a fixed boundary: `W₁ ≤ W₂`
when `W₁` securely emulates `W₂` under `Obs`.

Definition A.1 of *UC, Categorically*.  A definition rather than an
instance: the order depends on the chosen observation, so no single instance
on `T.Obj Δ` is canonical.  Instance-reducible so that a local
`letI := securelyEmulatesPreorder Δ Obs` resolves `≤` through it. -/
@[instance_reducible]
def securelyEmulatesPreorder (Δ : PortBoundary) (Obs : Observation T) :
    Preorder (T.Obj Δ) where
  le W₁ W₂ := SecurelyEmulates W₁ W₂ Obs
  le_refl W := SecurelyEmulates.refl Obs W
  le_trans _ _ _ := SecurelyEmulates.trans

@[simp]
theorem securelyEmulatesPreorder_le_iff {Δ : PortBoundary} {Obs : Observation T}
    {W₁ W₂ : T.Obj Δ} :
    (securelyEmulatesPreorder Δ Obs).le W₁ W₂ ↔ SecurelyEmulates W₁ W₂ Obs :=
  Iff.rfl

/-! ## Relativized secure emulation -/

/-- Secure emulation against the contexts allowed by a sub-theory `D`.  The
simulator must map allowed contexts to allowed contexts, exactly as in
`UCSecureWithin`; without that condition transitivity would feed the second
simulator a context outside `D`. -/
def SecurelyEmulatesWithin (D : SubTheory T) {Δ : PortBoundary}
    (real ideal : T.Obj Δ) (Obs : Observation T) : Prop :=
  ∃ simulate : T.Plug Δ → T.Plug Δ,
    D.PreservesAllowedness simulate ∧
      ∀ K : T.Plug Δ, D.mem K →
        Obs.rel (T.close real K) (T.close ideal (simulate K))

namespace SecurelyEmulatesWithin

variable {D : SubTheory T} {Δ : PortBoundary} {Obs : Observation T}

/-- Every open system securely emulates itself relative to any allowed
class. -/
theorem refl (D : SubTheory T) (Obs : Observation T) (W : T.Obj Δ) :
    SecurelyEmulatesWithin D W W Obs :=
  ⟨id, fun _ hK => hK, fun _ _ => Obs.equiv.refl _⟩

/-- Relativized secure emulations compose; allowedness preservation is what
lets the second simulator receive the first simulator's output. -/
theorem trans {W₁ W₂ W₃ : T.Obj Δ} (h₁₂ : SecurelyEmulatesWithin D W₁ W₂ Obs)
    (h₂₃ : SecurelyEmulatesWithin D W₂ W₃ Obs) :
    SecurelyEmulatesWithin D W₁ W₃ Obs := by
  obtain ⟨f₁, hf₁mem, hf₁⟩ := h₁₂
  obtain ⟨f₂, hf₂mem, hf₂⟩ := h₂₃
  exact ⟨f₂ ∘ f₁, fun K hK => hf₂mem _ (hf₁mem K hK),
    fun K hK => Obs.equiv.trans (hf₁ K hK) (hf₂ (f₁ K) (hf₁mem K hK))⟩

end SecurelyEmulatesWithin

/-- Relativized emulation is relativized secure emulation via the identity
simulator. -/
theorem EmulatesWithin.toSecurelyEmulatesWithin {D : SubTheory T}
    {Δ : PortBoundary} {Obs : Observation T} {real ideal : T.Obj Δ}
    (h : EmulatesWithin D real ideal Obs) :
    SecurelyEmulatesWithin D real ideal Obs :=
  ⟨id, fun _ hK => hK, h.compare⟩

/-- Relativizing secure emulation to the class that allows everything is a
no-op. -/
theorem securelyEmulatesWithin_top_iff {Δ : PortBoundary} {Obs : Observation T}
    {real ideal : T.Obj Δ} :
    SecurelyEmulatesWithin (SubTheory.top T) real ideal Obs ↔
      SecurelyEmulates real ideal Obs :=
  ⟨fun ⟨f, _, hf⟩ => ⟨f, fun K => hf K trivial⟩,
    fun ⟨f, hf⟩ => ⟨f, fun _ _ => trivial, fun K _ => hf K⟩⟩

end UC
end Interaction
