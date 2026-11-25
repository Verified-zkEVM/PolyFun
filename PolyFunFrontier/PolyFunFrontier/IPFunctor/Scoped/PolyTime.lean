/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

public import PolyFun.Realizability.Scoped
public import PolyFunFrontier.Realizability.MultiTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Tactic.PolyTime

/-!
# Polynomial-time interpretations of scoped terms

A binary operation in the word language zips its two arguments with a Boolean truth table.
Every fixed term in two variables computes a polynomial-time function of the encoded word pair.
The variables may occur repeatedly or in either order, and the words may have different lengths.
-/

public section

namespace IPFunctor.ScopedSignature

open PFunctor Turing.MultiTapeTM

/-- Every fixed binary word term computes a polynomial-time function on a pair of word inputs. -/
theorem wordTerm_polyTime (t : (Binary.signature (Bool → Bool → Bool)).Term [(), ()] ()) :
    ComputableInPolyTime (fun p : List Bool × List Bool =>
      t.denote (Binary.algebra (fun op x y => List.zipWith op x y)) (Binary.pairEnv p))
      (encPair encBits encBits) encBits :=
  Binary.denote_admissible (C := StepClass.multiTapePolyTime) (repr := encBits)
    (applyOp := fun op x y => List.zipWith op x y) (fun op => by
      change ComputableInPolyTime (fun p : List Bool × List Bool => p.1.zipWith op p.2)
        (encPair encBits encBits) encBits
      polytime) t

/-- Pointwise XOR applies a single truth table to the two variables. -/
theorem wordXor_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => p.1.zipWith Bool.xor p.2)
      (encPair encBits encBits) encBits :=
  wordTerm_polyTime (Binary.term Bool.xor)

end IPFunctor.ScopedSignature
