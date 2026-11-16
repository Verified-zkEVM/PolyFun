/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Do.Normalization
public import PolyFun.Control.Monad.Algebra.WP
public import Mathlib.Data.ENat.Lattice

/-!
# Normalizing verification conditions with `wp_norm`

Checks for `PolyFun.Control.Do.Normalization` and the transfer lemmas of
`ToCslib.Order.LeanOrder`:

* each transfer lemma rewrites one of core's lattice operations on a bridged carrier, `ℕ∞` or
  `Set ℕ`, into Mathlib's;
* `simp only [wp_norm]` turns core's assertion vocabulary into Mathlib's order and lattice
  operations on `ℕ∞`, into `Prop`'s connectives on `Prop`, into pointwise operations on a function
  carrier, into the reversed order on an order dual, and through `pushOption`, `pushExcept` and
  `binderNameHint`;
* on `Prop` the result is in `Prop`'s connectives, although the bridge lemmas also apply there;
* the names that downstream tactics match keep resolving: `ExactWPMonad.wp_ite` and
  `ExactWPMonad.wp_dite` with no warning, and `MAlgOrdered.iInf_eq_iInf` with a deprecation
  warning.

`PolyFunTest.Do.Charge` and `PolyFunTest.Do.FreeM` apply `wp_norm` to what `vcgen` leaves.
-/

@[expose] public section

open Std.WP

namespace PolyFunTest.Do.Normalization

/-! ## The transfer lemmas -/

example : (Lean.Order.top : ℕ∞) = ⊤ := LeanOrder.top_eq_top

example : @Lean.Order.bot ℕ∞ Lean.Order.instCCPOOfCompleteLattice = ⊥ := LeanOrder.bot_eq_bot

example (a b : ℕ∞) : Lean.Order.meet a b = a ⊓ b := LeanOrder.meet_eq_inf a b

example (a b : ℕ∞) : Lean.Order.join a b = a ⊔ b := LeanOrder.join_eq_sup a b

example (f : ℕ → ℕ∞) : Lean.Order.iInf f = ⨅ n, f n := LeanOrder.iInf_eq_iInf f

example (f : ℕ → ℕ∞) : Lean.Order.iSup f = ⨆ n, f n := LeanOrder.iSup_eq_iSup f

/-- Sets form a Mathlib frame, so core's Heyting implication on them is Mathlib's. -/
example (s t : Set ℕ) : Lean.Order.himp s t = s ⇨ t := LeanOrder.himp_eq_himp s t

example (n : ℕ) :
    (Lean.Order.CompleteLattice.ofProp (n = 0) : ℕ∞) = if n = 0 then ⊤ else ⊥ :=
  LeanOrder.ofProp_eq_ite (n = 0)

/-! ## `wp_norm` -/

/-- On `ℕ∞`, core's order and lattice operations become Mathlib's. -/
example (a b c : ℕ∞) (f : ℕ → ℕ∞) :
    Lean.Order.PartialOrder.rel (Lean.Order.meet a (Lean.Order.iSup f)) (Lean.Order.join b c) ↔
      a ⊓ ⨆ n, f n ≤ b ⊔ c := by
  simp only [wp_norm]

/-- `⌜p⌝` on `ℕ∞` becomes a conditional when `p` is decidable. -/
example (n : ℕ) (x : ℕ∞) :
    Lean.Order.meet (Lean.Order.CompleteLattice.ofProp (n = 0)) x =
      (if n = 0 then ⊤ else ⊥) ⊓ x := by
  simp only [wp_norm]

/-- On `Prop`, the result is in `Prop`'s connectives rather than in Mathlib's lattice operations
on `Prop`. -/
example (p q : Prop) (f : ℕ → Prop) :
    Lean.Order.PartialOrder.rel (Lean.Order.meet p (Lean.Order.CompleteLattice.ofProp q))
        (Lean.Order.iInf f) ↔
      (p ∧ q → ∀ n, f n) := by
  simp only [wp_norm]

/-- On a function carrier, such as the state-passing assertions of `StateT`, the operations apply
pointwise. -/
example (f g : ℕ → Prop) (s : ℕ) : Lean.Order.meet f g s ↔ f s ∧ g s := by
  simp only [wp_norm]

/-- On an order dual, as an upper-bound reading uses, the order is reversed. -/
example (a b : ℕ∞) :
    Lean.Order.PartialOrder.rel (OrderDual.toDual a) (OrderDual.toDual b) ↔ b ≤ a := by
  simp only [wp_norm]

/-- The postconditions that `OptionT` and `ExceptT` push to the base monad select a branch on a
constructor. -/
example (post : ℕ → Prop) (e : Unit → Prop) (n : ℕ) :
    Lean.Order.pushOption post e (some n) = post n ∧ Lean.Order.pushOption post e none = e () := by
  simp only [wp_norm, and_self]

example (post : ℕ → Prop) (e : String → Prop) (n : ℕ) (msg : String) :
    Lean.Order.pushExcept post e (.ok n) = post n ∧
      Lean.Order.pushExcept post e (.error msg) = e msg := by
  simp only [wp_norm, and_self]

/-- The binder-name markers around continuations disappear. -/
example (p : ℕ → Prop) (n : ℕ) : binderNameHint n (fun m : ℕ => m) (p n) ↔ p n := by
  simp only [wp_norm]

/-! ## Names that downstream tactics match -/

#guard_msgs in
example (c : Prop) [Decidable c] (x y : Id ℕ) (post : ℕ → Prop) :
    wp (if c then x else y) post estack⟨⟩ =
      if c then wp x post estack⟨⟩ else wp y post estack⟨⟩ :=
  ExactWPMonad.wp_ite c x y post estack⟨⟩

#guard_msgs in
example (c : Prop) [Decidable c] (x : c → Id ℕ) (y : ¬c → Id ℕ) (post : ℕ → Prop) :
    wp (if h : c then x h else y h) post estack⟨⟩ =
      if h : c then wp (x h) post estack⟨⟩ else wp (y h) post estack⟨⟩ :=
  ExactWPMonad.wp_dite c x y post estack⟨⟩

/- The deprecated name still rewrites; only its deprecation warning is reported. -/
#guard_msgs (drop warning) in
example (f : ℕ → ℕ∞) : Lean.Order.iInf f = ⨅ n, f n := by
  rw [MAlgOrdered.iInf_eq_iInf]

end PolyFunTest.Do.Normalization
