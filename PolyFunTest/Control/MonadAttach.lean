/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Support

/-!
# Examples for exact monadic support and the always/never judgments

These examples pin the definitional-transfer contract of the support layer: the satisfaction
judgments must stay `Iff.rfl`-convertible both to their bounded-quantifier spellings and to
`MonadAttach.CanReturn`, so downstream support-based statements transfer without rewriting.
They also exercise the scoped `⊨ₐ` / `⊨ₛ` / `⊭` notation, the structural recursion of the
judgments over free-monad trees, and `MonadAttach.pbind`.

The `StateT` section is the executable justification for `StateT σ m` having a `MonadAttach`
instance but *not* an `ExactMonadAttach` one: both introduction rules genuinely fail there.
-/

@[expose] public section

universe u v uA uB

open MonadAttach
open scoped MonadAttach

section DefinitionalTransfer

variable {m : Type u → Type v} [MonadAttach m] {α : Type u} (p : α → Prop) (x : m α)

/-- `AllOutputs` is definitionally the bounded universal quantifier. -/
example : (x ⊨ₐ p) ↔ ∀ a ∈ support x, p a := Iff.rfl

/-- `SomeOutput` is definitionally the bounded existential quantifier. -/
example : (x ⊨ₛ p) ↔ ∃ a ∈ support x, p a := Iff.rfl

/-- `NoOutput` is definitionally the negated bounded quantifier. -/
example : (x ⊭ p) ↔ ∀ a ∈ support x, ¬ p a := Iff.rfl

/-- Membership in the support is `CanReturn`, definitionally. -/
example (a : α) : a ∈ support x ↔ CanReturn x a := Iff.rfl

/-- The "always" judgment is definitionally a quantifier over `CanReturn`. -/
example : (x ⊨ₐ p) ↔ ∀ a, CanReturn x a → p a := Iff.rfl

end DefinitionalTransfer

section Judgments

/-- A two-direction query interface: one position, boolean responses. -/
abbrev coinP : PFunctor.{0, 0} := ⟨PUnit, fun _ => Bool⟩

open PFunctor in
/-- Flip one coin and return it. -/
def flipCoin : FreeM coinP Bool := FreeM.lift (P := coinP) PUnit.unit

open PFunctor in
/-- Flip two coins and return their conjunction. -/
def flipTwo : FreeM coinP Bool := do
  let a ← flipCoin
  let b ← flipCoin
  pure (a && b)

/-- Every outcome of a coin flip is a boolean tautology's witness. -/
example : flipCoin ⊨ₐ fun b => b = true ∨ b = false := by
  intro b _
  cases b <;> simp

/-- Some outcome of `flipTwo` is `true`, witnessed by two `true` flips. -/
example : flipTwo ⊨ₛ fun b => b = true := by
  rw [someOutput_iff_exists_support]
  refine ⟨true, ?_, rfl⟩
  rw [show flipTwo = flipCoin >>= (fun a => flipCoin >>= fun b => pure (a && b)) from rfl,
    mem_support_bind]
  have hcoin : (true : Bool) ∈ support flipCoin := by
    rw [flipCoin, PFunctor.FreeM.support_lift]
    exact Set.mem_univ true
  refine ⟨true, hcoin, ?_⟩
  rw [mem_support_bind]
  exact ⟨true, hcoin, by simp⟩

/-- No outcome of `flipTwo` lies outside `Bool`'s two values. -/
example : flipTwo ⊭ fun b => b ≠ true ∧ b ≠ false := by
  intro b _ hb
  cases b <;> simp_all

/-- `attach` is computable on free programs, so `pbind` can carry reachability proofs into
the continuation. -/
example : PFunctor.FreeM coinP {b : Bool // CanReturn flipCoin b} :=
  MonadAttach.attach flipCoin

/-- `pbind` gives the continuation a proof that its input was reachable. -/
example : PFunctor.FreeM coinP Bool :=
  MonadAttach.pbind flipCoin fun b (_ : CanReturn flipCoin b) => pure (!b)

end Judgments

section StatefulCounterexamples

/-! `StateT σ m` has a canonical `MonadAttach` instance — the union over initial states — so
`support` is defined and the elimination theory applies. It is not `ExactMonadAttach`: both
introduction rules fail, as the two examples below witness. Reason per run instead. -/

/-- Possible outputs do *not* compose along `bind` for `StateT`: the continuation may
observe a state the prefix never produced. -/
example : ¬ (∀ {α β : Type} {x : StateT Bool Id α} {f : α → StateT Bool Id β} {a : α}
      {b : β}, CanReturn x a → CanReturn (f a) b → CanReturn (x >>= f) b) := by
  intro h
  have hx : CanReturn (m := StateT Bool Id) (fun _ => ((), true)) () := ⟨false, true, rfl⟩
  have hf : CanReturn (m := StateT Bool Id) (fun s => (s, s)) false := ⟨false, false, rfl⟩
  obtain ⟨s, s', hs⟩ := h (x := fun _ => ((), true)) (f := fun _ => fun s => (s, s)) hx hf
  simp only [CanReturn, Id.run] at hs
  exact Bool.noConfusion (congrArg Prod.fst hs)

/-- Even the `pure` introduction rule fails when the state type is empty: there is no
initial state to run from. -/
example (a : Nat) : ¬ CanReturn (m := StateT Empty Id) (pure a) a := by
  rintro ⟨s, -, -⟩
  exact s.elim

/-- The usable form: state facts about a `StateT` computation per run. -/
example {m : Type → Type v} [Monad m] [MonadAttach m] {σ α : Type} (x : StateT σ m α)
    (a : α) : a ∈ support x ↔ ∃ s s', (a, s') ∈ support (x.run s) :=
  mem_support_stateT_iff

end StatefulCounterexamples

section TrivialTriple

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
variable {α : Type}

/-- The "always" judgment is the trivial-precondition `Prop`-valued triple. -/
example (x : m α) (p : α → Prop) :
    MAlgOrdered.Triple (l := Prop) ⊤ x p ↔ (x ⊨ₐ p) :=
  triple_top_iff_allOutputs x p

end TrivialTriple
