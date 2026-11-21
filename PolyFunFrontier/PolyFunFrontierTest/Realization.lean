/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunFrontier.IPFunctor.Scoped.PolyTime
public import PolyFunFrontier.PFunctor.Free.Realization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Tactic.PPT

/-!
# Fair-word realization at variable input length

A branching source runs with both a one-bit port and a two-read implementation. A concrete tape
distinguishes those installations, and the complete two-read program has a finite fair-coin machine.
A variable-length word sampler also runs over either summand of a combined interface.
-/

public section

namespace PolyFunFrontierTest.Realization

open PFunctor Turing.MultiTapeTM

abbrev Coin := monomial Unit Bool

@[expose] def flip : Coin.FreeM Bool := FreeM.lift ()

noncomputable def fair : Handler Cslib.ProbComp Coin := fun _ => Cslib.ProbComp.uniform Bool

/-- Read the next bit of a concrete tape, with false as the exhausted-tape default. -/
@[expose] def readBit : Handler (StateM (List Bool)) Coin :=
  fun _ tape => (tape.headD false, tape.tail)

/-- Implement one request by consuming two target bits and returning the second. -/
@[expose] def secondBit : Handler (FreeM Coin) Coin := fun _ => do
  let _ ← flip
  flip

/-- A single open program branches on its first answer and may ask for another. -/
@[expose] def consecutive : Coin.FreeM Bool := do
  if ← flip then flip else pure false

/-- The one-bit handler stops on the first false and leaves the remaining tape untouched. -/
theorem consecutive_direct :
    (consecutive.liftM readBit).run [false, true, false, true] =
      (false, [true, false, true]) := rfl

/-- Installing the two-read implementation changes both the result and the consumed tape.
Running through the composite handler and folding the installed program agree. -/
theorem consecutive_installed :
    (consecutive.liftM (readBit.comp secondBit)).run [false, true, false, true] = (true, []) := by
  rw [Handler.liftM_comp]
  rfl

/-- One request to the installed port consumes two independent fair bits. -/
private theorem twoRead_call {α : Type} (input : α ↪ List Bool) :
    FreeM.PPTProgram (fair.comp secondBit) input encBool (fun _ : α => flip) := by
  have h : Cslib.Probability.IsPPTOn input encBool (fun _ : α => (fair.comp secondBit) ()) := by
    change Cslib.Probability.IsPPTOn input encBool (fun _ : α => do
      let _ ← Cslib.ProbComp.uniform Bool
      Cslib.ProbComp.uniform Bool)
    exact (Cslib.Probability.isPPTOn_uniform_bool input).bind
      (Cslib.Probability.isPPTOn_uniform_bool encBool)
  apply (FreeM.PPTProgram.call (H := fair.comp secondBit) (query := fun _ : α => ())
    (answer := fun _ => id) (by simpa only [id_map] using h)).congr
  exact fun _ => id_map flip

/-- Certify the complete branching program after installing the two-read handler. -/
theorem consecutive_pptProgram :
    FreeM.PPTProgram fair encBits encBool (fun _ : List Bool => consecutive.liftM secondBit) := by
  apply FreeM.PPTProgram.substitute
  apply (twoRead_call encBits).bindWith (next := fun _ b => if b then flip else pure false)
  exact .branch (condition := Prod.snd) (ComputableInPolyTime.snd encBits encBool)
    (twoRead_call (encPair encBits encBool)) (.localMap (ComputableInPolyTime.const false))

/-- One finite machine implements every input to the installed program. -/
noncomputable def consecutiveMachine :
    FreeM.MachineRealization fair encBits encBool
      (fun _ : List Bool => consecutive.liftM secondBit) :=
  .ofPPTProgram consecutive_pptProgram

/-- Running the machine gives the output law of the original program with the composite handler. -/
theorem consecutiveMachine_output (w : List Bool) :
    consecutiveMachine.output w =
      (Cslib.ProbComp.eval (consecutive.liftM (fair.comp secondBit))).map encBool := by
  simpa only [FreeM.MachineRealization.output, Handler.liftM_comp] using
    consecutiveMachine.encoded_law w

example : ((FreeM.sampleBits flip 0).liftM readBit).run [true] = ([], [true]) := rfl

example : ((FreeM.sampleBits flip 2).liftM readBit).run [true, false] = ([true, false], []) := rfl

example : FreeM.sampleBits flip 1 ≠ pure [] := by
  intro h
  cases h

open IPFunctor.ScopedSignature in
example : ComputableInPolyTime
    (fun p : List Bool × List Bool => p.2.zipWith Bool.and (p.1.zipWith Bool.or p.2))
    (encPair encBits encBits) encBits := by
  simpa only [Binary.denote_app, Binary.denote_fst, Binary.denote_snd] using
    wordTerm_polyTime (Binary.app Bool.and Binary.snd (Binary.app Bool.or Binary.fst Binary.snd))

theorem wordCertificate :
    FreeM.PPTProgram fair encBits encBits (fun word => FreeM.sampleBits flip word.length) := by
  apply FreeM.PPTProgram.sampleBits
  · exact FreeM.liftM_lift (P := Coin) fair ()
  · polytime

example : FreeM.PPTProgram fair encBits encBool (fun _ : List Bool => flip) := by
  have hfair : Cslib.Probability.IsPPTOn encBits encBool
      (fun _ : List Bool => Cslib.ProbComp.uniform Bool) := by ppt
  apply (FreeM.PPTProgram.call (H := fair) (query := fun _ : List Bool => ())
    (answer := fun _ => id) (by simpa only [id_map, fair] using hfair)).congr
  exact fun _ => id_map flip

example : Cslib.Probability.IsPPTOn encBits encBits (fun word =>
    ((FreeM.sampleBits flip word.length).mapLens (Lens.inl (Q := Coin))).liftM (fair.sum fair)) :=
  (wordCertificate.sumLeft fair).isPPTOn

example : Cslib.Probability.IsPPTOn encBits encBits (fun word =>
    ((FreeM.sampleBits flip word.length).mapLens (Lens.inr (P := Coin))).liftM (fair.sum fair)) :=
  (wordCertificate.sumRight fair).isPPTOn

end PolyFunFrontierTest.Realization
