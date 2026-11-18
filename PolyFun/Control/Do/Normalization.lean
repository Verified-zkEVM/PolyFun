/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Do.Normalization.Attr
public import ToCslib.Order.LeanOrder
public import Std.WP

/-!
# Normalizing the verification conditions of `vcgen`

`vcgen` leaves its verification conditions in the assertion vocabulary of core's `Std.WP`. That
vocabulary consists of the order `⊑`, core's lattice operations (`Lean.Order.meet`, `iInf`, …), and
the embedding `⌜p⌝` of a proposition. It also has the postconditions `pushOption` and
`pushExcept`, which the `OptionT` and `ExceptT` interpretations push to the base monad, and the
`binderNameHint` markers around continuations. The simp set `wp_norm` rewrites them into the
vocabulary of the assertion carrier:

* on `Prop`, into implication, the connectives and the quantifiers;
* on a carrier whose lattice is Mathlib's, through the bridge `ToCslib.Order.LeanOrder`, into
  Mathlib's `≤`, `⊤`, `⊥`, `⊓`, `⊔`, `⨅`, `⨆`, `⇨`, and `if p then ⊤ else ⊥` (for decidable `p`);
* on a function carrier, such as the state-passing assertions of `StateT`, into the operations
  applied pointwise;
* on an order dual, as an upper-bound reading uses (`ExactWPMonad.dual`), into the reversed order
  of the original carrier;
* on `pushOption` and `pushExcept` applied to a constructor, into the branch it selects.

Run `simp only [wp_norm]` on what `vcgen` leaves, adding the equations of the program's own reading.
Every lemma of the set is an unconditional equation whose right-hand side removes core vocabulary
or moves it to a smaller carrier, so rewriting with the set terminates. Most of them are also
`simp` lemmas. The set lets a proof normalize the residue without the whole `simp` set, which on a
concrete interface also reduces the value types that later rules match on.
-/

public section

attribute [wp_norm ↓] binderNameHint

/-! ## The order and the bridged lattice operations -/

attribute [wp_norm] Lean.Order.rel_eq_le Lean.Order.rel_orderDual LeanOrder.top_eq_top
  LeanOrder.bot_eq_bot LeanOrder.meet_eq_inf LeanOrder.join_eq_sup LeanOrder.iInf_eq_iInf
  LeanOrder.iSup_eq_iSup LeanOrder.himp_eq_himp LeanOrder.ofProp_eq_ite

/-! ## The carrier `Prop`

Core's lattice on `Prop` unifies with the bridge of Mathlib's, so the bridge lemmas also apply on
`Prop`. The `Prop` lemmas take priority, so that the result is in `Prop`'s connectives rather than
in Mathlib's lattice operations on `Prop`. -/

attribute [wp_norm high] Lean.Order.le_prop_eq_imp Lean.Order.CompleteLattice.ofProp_prop_eq
  Lean.Order.meet_prop_eq_and Lean.Order.join_prop_eq_or Lean.Order.himp_prop_eq_imp
  Lean.Order.top_prop_eq Lean.Order.bot_prop_eq Lean.Order.iInf_prop_eq_forall
  Lean.Order.iSup_prop_eq_exists

/-! ## Function carriers -/

attribute [wp_norm] Lean.Order.meet_apply Lean.Order.join_apply Lean.Order.iInf_apply
  Lean.Order.iSup_apply Lean.Order.top_apply Lean.Order.bot_apply
  Lean.Order.CompleteLattice.ofProp_apply Lean.Order.himp_apply

/-! ## Order duals -/

attribute [wp_norm] OrderDual.toDual_le_toDual OrderDual.ofDual_toDual OrderDual.toDual_ofDual

/-! ## Pushed postconditions -/

attribute [wp_norm] Lean.Order.pushOption_some Lean.Order.pushOption_none
  Lean.Order.pushExcept_ok Lean.Order.pushExcept_error
