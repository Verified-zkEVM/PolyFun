/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler.Settled

/-!
# Uniform decoding from a public hint

A decoder sees a hint and a request. Its answer must meet a relation for every hidden state
with that hint. For partial handlers, a decoder preserving settled runs exists exactly when
two states with the same hint never answer the same request differently.
-/

public section

namespace PFunctor.Handler.Hint

universe u v w z

variable {T : Type u} {H : Type v} {A : Type w} {C : A → Type z}

/-- The decoder meets the relation at every hidden state and request using only the public hint. -/
abbrev Valid (R : T → (a : A) → C a → Prop) (hint : T → H)
    (decode : H → (a : A) → C a) : Prop :=
  ∀ t a, R t a (decode (hint t) a)

/-- A total decoder exists precisely when each hint and request has a common admissible answer.
This formulation includes unused hints and allows empty answer types. -/
theorem exists_valid_iff (R : T → (a : A) → C a → Prop) (hint : T → H) :
    (∃ decode, Valid R hint decode) ↔ ∀ s a, ∃ c, ∀ t, hint t = s → R t a c := by
  constructor
  · rintro ⟨d, hd⟩ s a
    exact ⟨d s a, fun t ht => ht ▸ hd t a⟩
  · intro cells
    exact ⟨fun s a => (cells s a).choose, fun t a => (cells (hint t) a).choose_spec t rfl⟩

variable {P : PFunctor.{w, z}}

/-- The decoded partial handler supplies the same answer whenever the hidden handler answers. -/
abbrev PreservesSettled (source : T → Handler Option P) (hint : T → H)
    (decode : H → Handler Option P) : Prop :=
  Valid (fun t a c => ∀ b, source t a = some b → c = some b) hint decode

/-- Preserving settled answers is equivalent to preserving every settled adaptive program.
Single-request programs give the reverse implication. -/
theorem preservesSettled_iff_liftM (source : T → Handler Option P) (hint : T → H)
    (decode : H → Handler Option P) :
    PreservesSettled source hint decode ↔
      ∀ t {α : Type z} (x : FreeM P α) (v : α),
        x.liftM (source t) = some v → x.liftM (decode (hint t)) = some v := by
  constructor
  · intro h t α x v
    exact FreeM.liftM_eq_some_of_le _ _ (h t)
  · intro h t a b hb
    simpa only [FreeM.liftM_lift] using
      h t (FreeM.lift a) b (by simpa only [FreeM.liftM_lift] using hb)

/-- Exact agreement on requests is equivalent to agreement on every adaptive program,
including programs whose evaluation fails. -/
theorem exact_iff_liftM (source : T → Handler Option P) (hint : T → H)
    (decode : H → Handler Option P) :
    Valid (fun t a c => source t a = c) hint decode ↔
      ∀ t {α : Type z} (x : FreeM P α), x.liftM (source t) = x.liftM (decode (hint t)) := by
  constructor
  · intro h t α x
    rw [show source t = decode (hint t) from funext (h t)]
  · intro h t a
    simpa only [FreeM.liftM_lift] using h t (FreeM.lift a)

/-- A family admits a common settled decoder on each hint fiber exactly when the answers
present in that fiber are consistent. The decoder can leave a request unanswered when no
state in the fiber answers it. -/
theorem exists_preservesSettled_iff (source : T → Handler Option P) (hint : T → H) :
    (∃ decode, PreservesSettled source hint decode) ↔
      ∀ t t', hint t = hint t' → ∀ a b b', source t a = some b → source t' a = some b' →
        b = b' := by
  constructor
  · rintro ⟨decode, hd⟩ t t' he a b b' hb hb'
    have hs := hd t a b hb
    rw [he] at hs
    exact Option.some.inj (hs.symm.trans (hd t' a b' hb'))
  · intro consistent
    apply (exists_valid_iff _ _).2
    intro s a
    by_cases available : ∃ b, ∃ t, hint t = s ∧ source t a = some b
    · obtain ⟨b, t, ht, hb⟩ := available
      exact ⟨some b, fun t' ht' b' hb' => congrArg some
        (consistent t t' (ht.trans ht'.symm) a b b' hb hb')⟩
    · exact ⟨none, fun t ht b hb => (available ⟨b, t, ht, hb⟩).elim⟩

end PFunctor.Handler.Hint
