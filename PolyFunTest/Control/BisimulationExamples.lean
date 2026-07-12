/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Bisimulation

/-!
# Examples for the generic silent-absorbing bisimulation

Regression tests and worked examples for `Control.WeakBisim`
(`PolyFun/Control/Bisimulation.lean`).

The headline example (`idle_weakBisim_plain`) is the crypto-free shape of "what
bisimulation buys for internal state plumbing": a system that spins on a silent
internal **idle** move is weakly bisimilar to one that does not — the silent
step is absorbed, so it is unobservable. The generic `refl`/`symm`/`trans`
lemmas apply to it without any per-example metatheory.
-/

@[expose] public section

namespace Control
namespace BisimulationExamples

/-- A one-state system that, at its single state, can either take a **silent**
idle move (`false`) that loops back, or a **visible** tick (`true`, observing
`true : Bool`) that also loops back. -/
def idleLTS : LTS Bool where
  State := Unit
  Move _ := Bool
  next _ _ := ()
  label _ b := if b then some true else none

/-- The same observable behaviour with no idle move: a single visible tick. -/
def plainLTS : LTS Bool where
  State := Unit
  Move _ := Unit
  next _ _ := ()
  label _ _ := some true

/-- **Internal idling is unobservable.** The system with a silent idle self-loop
is weakly bisimilar to the one without: the idle move is absorbed (stuttered),
and the visible ticks match. -/
theorem idle_weakBisim_plain : WeakBisim idleLTS plainLTS :=
  ⟨fun _ _ => True, by
    refine ⟨fun _ => ⟨(), trivial⟩, fun _ => ⟨(), trivial⟩, ?_, ?_, ?_, ?_⟩
    · -- silent_forward: the idle move (`false`) is stuttered.
      rintro _ _ _ b _
      exact .inr trivial
    · -- visible_forward: the tick (`true`) is matched by `plainLTS`'s tick.
      rintro _ _ _ b o hb
      cases b with
      | false => simp [idleLTS] at hb
      | true =>
        refine ⟨(), ?_, trivial⟩
        simp_all [idleLTS, plainLTS]
    · -- silent_backward: `plainLTS` has no silent move.
      rintro _ _ _ μ hμ
      simp [plainLTS] at hμ
    · -- visible_backward: `plainLTS`'s tick is matched by `idleLTS`'s tick.
      rintro _ _ _ μ o hμ
      refine ⟨true, ?_, trivial⟩
      simp_all [idleLTS, plainLTS]⟩

/-- The equivalence laws are available generically, with no per-system proof. -/
example : WeakBisim idleLTS idleLTS := WeakBisim.refl _
example : WeakBisim plainLTS idleLTS := WeakBisim.symm idle_weakBisim_plain
example : WeakBisim idleLTS idleLTS :=
  WeakBisim.trans idle_weakBisim_plain (WeakBisim.symm idle_weakBisim_plain)

end BisimulationExamples
end Control
