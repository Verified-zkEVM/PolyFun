/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Samuel Schlesinger
-/

module
-- frontier: CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

public import PolyFun.Realizability.StepClass
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Polynomial-time multi-tape machines as a step class

A represented type carries an injective binary encoding. The admissible local steps are
Frontier's polynomial-time functions on these encodings. The step class uses the same framed
pair encoding as the machine operations for pairing and projecting results.
-/

public section

namespace PFunctor.StepClass

open Turing.MultiTapeTM

universe u

/-- The represented maps computed in polynomial time by deterministic multi-tape machines. -/
abbrev multiTapePolyTime : StepClass.{u, u} where
  Str A := A ↪ List Bool
  Hom input output f := ComputableInPolyTime f input output
  id_mem _ := ComputableInPolyTime.id'
  comp_mem hf hg := hg.comp hf

/-- Product representations use Frontier's framed concatenation of the two encoded values. -/
instance : multiTapePolyTime.{u}.HasProd where
  prod := encPair
  fst_mem := ComputableInPolyTime.fst
  snd_mem := ComputableInPolyTime.snd
  pair_mem := ComputableInPolyTime.prod

end PFunctor.StepClass
