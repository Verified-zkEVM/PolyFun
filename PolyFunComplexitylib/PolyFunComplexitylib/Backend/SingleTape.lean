/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ComplexityBackends.CslibSingleTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.SingleTape
public import PolyFunComplexitylib.Backend.Quantitative

/-!
# From the single-tape backend to tidy multi-tape machines

PolyFun's `ComplexityBackends.CslibSingleTape` backend certifies a map by a CSLib single-tape
machine computing a string function that intertwines the encodings (`EncPolyTime`).
complexitylib's simulation of single-tape machines on tidy multi-tape machines
(`Cslib.Turing.SingleTapeTM.PolyTimeComputable.computableTidilyInPolyTime`) transfers such a
certificate to `PolyFunComplexitylib.polyTimeStepClass`, once the encodings are injective.

The single-tape backend represents types by arbitrary functions into bit strings, so a backend
simulation `PFunctor.QuantitativeStepClass.SimulatedBy` between the two backends needs a
restriction to injective encodings. The translation below chooses multi-tape code without
tracking the simulation's time bound, because complexitylib's conversion from untidy to tidy
computation does not expose its overhead.
-/

@[expose] public section

namespace ComplexityBackends.CslibSingleTape.EncPolyTime

open Turing.MultiTapeTM

variable {α β : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool} {f : α → β}

/-- A single-tape polynomial-time certificate between injective encodings is a multi-tape tidy
polynomial-time computation. -/
theorem computableTidilyInPolyTime (c : EncPolyTime ea eb f) :
    ComputableTidilyInPolyTime f ea eb :=
  c.polyTime.computableTidilyInPolyTime ea eb f c.map_encode

/-- Multi-tape code for a single-tape certificate between injective encodings. -/
noncomputable def toPolyTimeCode (c : EncPolyTime ea eb f) :
    PolyFunComplexitylib.PolyTimeCode ea eb f :=
  .ofComputable c.computableTidilyInPolyTime

end ComplexityBackends.CslibSingleTape.EncPolyTime
