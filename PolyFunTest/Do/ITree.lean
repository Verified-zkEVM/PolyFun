/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.WP.Upstream

/-!
# Interaction-tree readings as core interpretations

The total and partial readings installed as core `WPMonad`s:
* their `wp` is the reading;
* silent divergence satisfies every postcondition partially and none totally, so the two
  interpretations differ;
* both are exact, so core's `wp` distributes over `bind` by the `ExactWPMonad` simp set;
* the demonic support reading agrees with the partial demonic interpretation.
-/

public section

open Std.WP PFunctor

namespace PolyFunTest.DoITree

/-- One operation, a coin flip answered by a Boolean. -/
@[reducible] def CoinE : PFunctor.{0, 0} where
  A := PUnit
  B _ := Bool

theorem coin_mono : (OpSpec.demonic CoinE).Monotone :=
  OpSpec.demonic_mono

/-- The partial interpretation accepts silent divergence for every postcondition. -/
example : ((ITree.wpMonadPartial (OpSpec.demonic CoinE) coin_mono).toWP Nat).wp
    (ITree.diverge : ITree CoinE Nat) (fun _ => False) () := by
  rw [ITree.wpMonadPartial_wp]
  simp

/-- The total interpretation rejects silent divergence. Swapping the two interpretations breaks
this and the previous example. -/
example : ¬ ((ITree.wpMonadTotal (OpSpec.demonic CoinE) coin_mono).toWP Nat).wp
    (ITree.diverge : ITree CoinE Nat) (fun _ => True) () := by
  rw [ITree.wpMonadTotal_wp]
  simp

/-- The total interpretation is exact: core's `wp` distributes over `bind`. -/
example (t : ITree CoinE Bool) (k : Bool → ITree CoinE Bool) (post : Bool → Prop) :
    letI := ITree.wpMonadTotal (OpSpec.demonic CoinE) coin_mono
    wp (t >>= k) post () = wp t (fun a => wp (k a) post ()) () := by
  simp only [ExactWPMonad.wp_bind]

/-- The partial interpretation is exact. -/
example (t : ITree CoinE Bool) (k : Bool → ITree CoinE Bool) (post : Bool → Prop) :
    letI := ITree.wpMonadPartial (OpSpec.demonic CoinE) coin_mono
    wp (t >>= k) post () = wp t (fun a => wp (k a) post ()) () := by
  simp only [ExactWPMonad.wp_bind]

/-- The demonic support reading is the partial demonic interpretation. -/
example (t : ITree CoinE Nat) (post : Nat → Prop) :
    ((MonadAttach.toWPMonadDemonic (m := ITree CoinE)).toWP Nat).wp t post () =
      ((ITree.wpMonadPartial (OpSpec.demonic CoinE) coin_mono).toWP Nat).wp t post () := by
  rw [ITree.toWPMonadDemonic_wp_eq_wpPartial, ITree.wpMonadPartial_wp]

end PolyFunTest.DoITree
