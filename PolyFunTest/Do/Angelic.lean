/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunTest.Do.FreeM
public import PolyFun.Control.Monad.Support.WP
public import PolyFun.Control.Monad.Support.Instances

/-!
# The angelic interpretation on core's `Std.WP`

`MonadAttach.toWPAngelic` reads `wp x post` as "some possible output of `x` satisfies `post`".
These canaries pin what that buys and what it deliberately does not: the characterization by
`rfl`, the pure and bind laws with a branch-dependent witness, falsity on empty support, a `vcgen`
run that proves existential reachability of a free program without conjunctivity, and — on the
two-element support `{0, 1}` — the failure of conjunctivity and of core's universal soundness
`LawfulWPMonadAttach`, first as ordinary theorems and then against the classes themselves. The
module acknowledges the tactic's experimental status with `set_option experimental.vcgen true`;
`PolyFunTest.Do.Algebra` pins the diagnostic itself.
-/

@[expose] public section

open Std.WP MonadAttach PFunctor
open scoped PFunctor.FreeM.AngelicWP Lean.Order

set_option experimental.vcgen true

universe u v

namespace PolyFunTest.Do.Angelic

section Characterization

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

/-- The angelic `wp` is the "sometimes" judgment, definitionally. -/
example {α : Type u} (x : m α) (post : α → Prop) (epost : EStack⟨⟩) :
    (toWPAngelic (m := m) α).wp x post epost ↔ SomeOutput post x :=
  Iff.rfl

/-- The `WPMonad` interpretation routes through the same transformer. -/
example {α : Type u} (x : m α) (post : α → Prop) (epost : EStack⟨⟩) :
    ((toWPMonadAngelic (m := m)).toWP α).wp x post epost =
      (toWPAngelic (m := m) α).wp x post epost :=
  rfl

/-- Pure: the postcondition at the returned value. -/
example {α : Type u} (a : α) (post : α → Prop) (epost : EStack⟨⟩) :
    (toWPAngelic (m := m) α).wp (pure a) post epost ↔ post a :=
  someOutput_pure post a

/-- Core's triple is the guarded "sometimes" judgment. -/
example {α : Type u} (x : m α) (pre : Prop) (post : α → Prop) (epost : EStack⟨⟩) :
    @Triple Prop EStack⟨⟩ (m α) α _ _ x ((toWPMonadAngelic (m := m)).toWP α) pre post epost ↔
      (pre → SomeOutput post x) :=
  toWPMonadAngelic_triple_iff x pre post epost

end Characterization

section Powerset

/-- The two-element support. -/
def zeroOne : SetM ℕ := ({0, 1} : Set ℕ)

/-- A second choice, reached only through the `1` branch below. -/
def sevenEight : SetM ℕ := ({7, 8} : Set ℕ)

/-- A branch-dependent continuation: `0` leads to `10`, anything else to `sevenEight`. -/
def branch : SetM ℕ := do
  let n ← zeroOne
  match n with
  | 0 => pure 10
  | _ => sevenEight

/-- Bind with a branch-dependent witness: `8` is reachable by choosing `1`, then `8`. Both stages
of the existential choice are exercised. -/
example : (toWPAngelic (m := SetM) ℕ).wp branch (· = 8) estack⟨⟩ :=
  ⟨8, canReturn_bind_iff.mpr ⟨1, Or.inr rfl, Or.inr rfl⟩, rfl⟩

/-- The same fact through the bind law rather than the witness. -/
example : (toWPAngelic (m := SetM) ℕ).wp branch (· = 8) estack⟨⟩ :=
  (someOutput_bind (· = 8) zeroOne _).mpr ⟨1, Or.inr rfl, 8, Or.inr rfl, rfl⟩

/-- The demonic reading rejects the same postcondition: `0` leads to `10`. -/
example : ¬ (toWPDemonic (m := SetM) ℕ).wp branch (· = 8) estack⟨⟩ :=
  fun h => absurd (h 10 (canReturn_bind_iff.mpr ⟨0, Or.inl rfl, rfl⟩)) (by decide)

/-- The empty computation. -/
def nothing : SetM ℕ := (∅ : Set ℕ)

/-- Empty support makes the angelic `wp` false … -/
example (post : ℕ → Prop) : ¬ (toWPAngelic (m := SetM) ℕ).wp nothing post estack⟨⟩ :=
  fun ⟨_, h, _⟩ => h

/-- … where the demonic `wp` is vacuously true. -/
example (post : ℕ → Prop) : (toWPDemonic (m := SetM) ℕ).wp nothing post estack⟨⟩ :=
  fun _ h => False.elim h

end Powerset

section Reachability

/-- Under the angelic interpretation `flipNot` can return `true`: `vcgen` reduces the triple to
the existence of one favourable response, with no conjunctivity anywhere. -/
example : ⦃ True ⦄ flipNot ⦃ fun r => r = true ⦄ := by
  vcgen [flipNot]
  exact ⟨false, (someOutput_pure _ _).mpr rfl⟩

/-- The angelic `wp` of a free program is the "sometimes" judgment, so the discharged triple is a
reachability fact about the program's support. -/
example : SomeOutput (fun r => r = true) flipNot :=
  ⟨true, canReturn_bind_iff.mpr ⟨false, by
    rw [← mem_support, FreeM.support_lift]; exact Set.mem_univ _, canReturn_pure_iff.mpr rfl⟩, rfl⟩

end Reachability

section Canaries

/-! The two-element support refutes both properties the demonic reading enjoys. -/

/-- Each conjunct holds angelically … -/
example : (toWPAngelic (m := SetM) ℕ).wp zeroOne (· = 0) estack⟨⟩ ∧
    (toWPAngelic (m := SetM) ℕ).wp zeroOne (· = 1) estack⟨⟩ :=
  ⟨⟨0, Or.inl rfl, rfl⟩, ⟨1, Or.inr rfl, rfl⟩⟩

/-- … but their conjunction does not: no single output is both `0` and `1`. -/
example : ¬ (toWPAngelic (m := SetM) ℕ).wp zeroOne (fun a => a = 0 ∧ a = 1) estack⟨⟩ :=
  fun ⟨_, _, h₀, h₁⟩ => Nat.zero_ne_one (h₀.symm.trans h₁)

/-- Hence the angelic transformer is not `WPConjunctive` at `zeroOne`. -/
example : ¬ @WPConjunctive (SetM ℕ) ℕ Prop EStack⟨⟩ _ _ (toWPAngelic (m := SetM) ℕ) zeroOne := by
  intro h
  let inst := toWPAngelic (m := SetM) ℕ
  have hc := h.wp_meet_wp_le (· = 0) (· = 1) estack⟨⟩ estack⟨⟩
  change Lean.Order.meet (SomeOutput _ zeroOne) (SomeOutput _ zeroOne) →
    SomeOutput (Lean.Order.meet _ _) zeroOne at hc
  rw [Lean.Order.meet_prop_eq_and] at hc
  obtain ⟨a, -, ha⟩ := hc ⟨⟨0, Or.inl rfl, rfl⟩, ⟨1, Or.inr rfl, rfl⟩⟩
  rw [Lean.Order.meet_apply, Lean.Order.meet_prop_eq_and] at ha
  exact Nat.zero_ne_one (ha.1.symm.trans ha.2)

/-- `wp zeroOne (· = 0)` holds while `1` is reachable and `1 ≠ 0`: an angelic `wp` proof says
nothing about every reachable output. -/
example : (toWPAngelic (m := SetM) ℕ).wp zeroOne (· = 0) estack⟨⟩ ∧
    CanReturn zeroOne 1 ∧ (1 : ℕ) ≠ 0 :=
  ⟨⟨0, Or.inl rfl, rfl⟩, Or.inr rfl, Nat.one_ne_zero⟩

/-- Hence the angelic `WPMonad` has no core soundness instance. -/
example :
    ¬ @LawfulWPMonadAttach SetM.{0} Prop EStack⟨⟩ _ _ _ _ _ (toWPMonadAngelic (m := SetM.{0})) := by
  intro h
  let inst := toWPMonadAngelic (m := SetM.{0})
  have hwp : Lean.Order.top ⊑ wp zeroOne (fun a => ⌜a = 0⌝) Lean.Order.top := by
    intro _
    change SomeOutput (fun a => ⌜a = 0⌝) zeroOne
    exact ⟨0, Or.inl rfl, (Lean.Order.ofProp_prop_eq _).mpr rfl⟩
  have h₁ : CanReturn zeroOne 1 := Or.inr rfl
  have h₀ := h.of_canReturn_wp h₁ hwp
  exact Nat.one_ne_zero h₀

end Canaries

end PolyFunTest.Do.Angelic
