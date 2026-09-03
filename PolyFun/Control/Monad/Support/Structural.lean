/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Support

/-!
# Structural Laws of Exact Support for the `do` Fragment

`PolyFun.Control.Monad.Support` keys the exact-support laws on `pure` and `bind` and pushes the
set-valued `support` through `map`, `seq`, `ite`, and `dite`. `do`-notation elaborates to more
than that: applicative sequencing `<*` / `*>`, `if` / `if h :`, and `match` on `Option` and `Sum`
(elaborated through `Option.elim` / `Sum.elim`, or left as a `match` that `split` reduces to the
same shapes). This file states each of those for the reachability predicate `CanReturn` and for
the three judgments `AllOutputs` / `SomeOutput` / `NoOutput`, so that a goal about a `do` block
decomposes without unfolding the judgments.

### Automation contract

The `CanReturn` equations for `Option.elim` and `Sum.elim` are `@[simp, grind =]`, extending the
`canReturn_pure_iff` / `bind_iff` / `map_iff` chain. Those for `ite` / `dite` and for `<*` / `*>`
are `@[simp]` only: `grind` handles `if` by its own case splitting and refuses `ite` as a pattern
head, and the second operand of `<*` / `*>` sits under the thunk `fun _ => y`, which a pattern
cannot bind. The judgment-level rules are `@[simp]` only, following the root file's contract:
they quantify over outputs, and letting `grind` instantiate quantifier characterizations
saturates it.
-/

@[expose] public section

universe u v w w'

namespace MonadAttach

variable {m : Type u → Type v} {α β : Type u} {γ : Type w} {δ : Type w'}

/-! ## Branching -/

section Branching

variable [MonadAttach m]

@[simp]
theorem canReturn_ite (c : Prop) [Decidable c] (x y : m α) (a : α) :
    CanReturn (if c then x else y) a ↔ if c then CanReturn x a else CanReturn y a := by
  split <;> rfl

@[simp]
theorem canReturn_dite (c : Prop) [Decidable c] (x : c → m α) (y : ¬ c → m α) (a : α) :
    CanReturn (if h : c then x h else y h) a ↔
      if h : c then CanReturn (x h) a else CanReturn (y h) a := by
  split <;> rfl

@[simp, grind =]
theorem canReturn_option_elim (o : Option γ) (x : m α) (f : γ → m α) (a : α) :
    CanReturn (o.elim x f) a ↔
      (o = none → CanReturn x a) ∧ ∀ c, o = some c → CanReturn (f c) a := by
  cases o <;> simp

@[simp, grind =]
theorem canReturn_sum_elim (s : γ ⊕ δ) (f : γ → m α) (g : δ → m α) (a : α) :
    CanReturn (s.elim f g) a ↔
      (∀ c, s = .inl c → CanReturn (f c) a) ∧ ∀ d, s = .inr d → CanReturn (g d) a := by
  cases s <;> simp

@[simp]
theorem allOutputs_ite (c : Prop) [Decidable c] (p : α → Prop) (x y : m α) :
    AllOutputs p (if c then x else y) ↔ if c then AllOutputs p x else AllOutputs p y := by
  split <;> rfl

@[simp]
theorem allOutputs_dite (c : Prop) [Decidable c] (p : α → Prop) (x : c → m α)
    (y : ¬ c → m α) :
    AllOutputs p (if h : c then x h else y h) ↔
      if h : c then AllOutputs p (x h) else AllOutputs p (y h) := by
  split <;> rfl

@[simp]
theorem someOutput_ite (c : Prop) [Decidable c] (p : α → Prop) (x y : m α) :
    SomeOutput p (if c then x else y) ↔ if c then SomeOutput p x else SomeOutput p y := by
  split <;> rfl

@[simp]
theorem someOutput_dite (c : Prop) [Decidable c] (p : α → Prop) (x : c → m α)
    (y : ¬ c → m α) :
    SomeOutput p (if h : c then x h else y h) ↔
      if h : c then SomeOutput p (x h) else SomeOutput p (y h) := by
  split <;> rfl

@[simp]
theorem noOutput_ite (c : Prop) [Decidable c] (p : α → Prop) (x y : m α) :
    NoOutput p (if c then x else y) ↔ if c then NoOutput p x else NoOutput p y := by
  split <;> rfl

@[simp]
theorem noOutput_dite (c : Prop) [Decidable c] (p : α → Prop) (x : c → m α)
    (y : ¬ c → m α) :
    NoOutput p (if h : c then x h else y h) ↔
      if h : c then NoOutput p (x h) else NoOutput p (y h) := by
  split <;> rfl

@[simp]
theorem allOutputs_option_elim (o : Option γ) (p : α → Prop) (x : m α) (f : γ → m α) :
    AllOutputs p (o.elim x f) ↔
      (o = none → AllOutputs p x) ∧ ∀ c, o = some c → AllOutputs p (f c) := by
  cases o <;> simp

@[simp]
theorem someOutput_option_elim (o : Option γ) (p : α → Prop) (x : m α) (f : γ → m α) :
    SomeOutput p (o.elim x f) ↔
      (o = none → SomeOutput p x) ∧ ∀ c, o = some c → SomeOutput p (f c) := by
  cases o <;> simp

@[simp]
theorem allOutputs_sum_elim (s : γ ⊕ δ) (p : α → Prop) (f : γ → m α) (g : δ → m α) :
    AllOutputs p (s.elim f g) ↔
      (∀ c, s = .inl c → AllOutputs p (f c)) ∧ ∀ d, s = .inr d → AllOutputs p (g d) := by
  cases s <;> simp

@[simp]
theorem someOutput_sum_elim (s : γ ⊕ δ) (p : α → Prop) (f : γ → m α) (g : δ → m α) :
    SomeOutput p (s.elim f g) ↔
      (∀ c, s = .inl c → SomeOutput p (f c)) ∧ ∀ d, s = .inr d → SomeOutput p (g d) := by
  cases s <;> simp

end Branching

/-! ## Functor and applicative structure -/

section Applicative

variable [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

@[simp]
theorem allOutputs_map_iff (p : β → Prop) (g : α → β) (x : m α) :
    AllOutputs p (g <$> x) ↔ AllOutputs (fun a => p (g a)) x := by
  simp only [AllOutputs, canReturn_map_iff]
  exact ⟨fun h a ha => h (g a) ⟨a, ha, rfl⟩, fun h _ ⟨a, ha, hab⟩ => hab ▸ h a ha⟩

@[simp]
theorem someOutput_map_iff (p : β → Prop) (g : α → β) (x : m α) :
    SomeOutput p (g <$> x) ↔ SomeOutput (fun a => p (g a)) x := by
  simp only [SomeOutput, canReturn_map_iff]
  exact ⟨fun ⟨_, ⟨a, ha, hab⟩, hp⟩ => ⟨a, ha, hab ▸ hp⟩, fun ⟨a, ha, hp⟩ => ⟨g a, ⟨a, ha, rfl⟩, hp⟩⟩

@[simp]
theorem noOutput_map_iff (p : β → Prop) (g : α → β) (x : m α) :
    NoOutput p (g <$> x) ↔ NoOutput (fun a => p (g a)) x :=
  allOutputs_map_iff (fun b => ¬ p b) g x

@[simp]
theorem allOutputs_seq_iff (p : β → Prop) (f : m (α → β)) (x : m α) :
    AllOutputs p (f <*> x) ↔ AllOutputs (fun g => AllOutputs (fun a => p (g a)) x) f := by
  rw [seq_eq_bind_map, allOutputs_bind]
  simp only [allOutputs_map_iff]
  exact Iff.rfl

@[simp]
theorem someOutput_seq_iff (p : β → Prop) (f : m (α → β)) (x : m α) :
    SomeOutput p (f <*> x) ↔ SomeOutput (fun g => SomeOutput (fun a => p (g a)) x) f := by
  rw [seq_eq_bind_map, someOutput_bind]
  simp only [someOutput_map_iff]
  exact Iff.rfl

@[simp]
theorem canReturn_seqLeft_iff {x : m α} {y : m β} {a : α} :
    CanReturn (x <* y) a ↔ CanReturn x a ∧ ∃ b, CanReturn y b := by
  rw [seqLeft_eq_bind]
  simp only [canReturn_bind_iff, canReturn_pure_iff]
  exact ⟨fun ⟨_, ha, b, hb, hab⟩ => hab ▸ ⟨ha, b, hb⟩, fun ⟨ha, b, hb⟩ => ⟨a, ha, b, hb, rfl⟩⟩

@[simp]
theorem canReturn_seqRight_iff {x : m α} {y : m β} {b : β} :
    CanReturn (x *> y) b ↔ (∃ a, CanReturn x a) ∧ CanReturn y b := by
  rw [seqRight_eq_bind]
  simp only [canReturn_bind_iff]
  exact ⟨fun ⟨a, ha, hb⟩ => ⟨⟨a, ha⟩, hb⟩, fun ⟨⟨a, ha⟩, hb⟩ => ⟨a, ha, hb⟩⟩

@[simp]
theorem support_seqLeft (x : m α) (y : m β) :
    support (x <* y) = {a | a ∈ support x ∧ (support y).Nonempty} := by
  ext a
  simp [Set.Nonempty]

@[simp]
theorem support_seqRight (x : m α) (y : m β) :
    support (x *> y) = {b | (support x).Nonempty ∧ b ∈ support y} := by
  ext b
  simp [Set.Nonempty]

@[simp]
theorem allOutputs_seqLeft_iff (p : α → Prop) (x : m α) (y : m β) :
    AllOutputs p (x <* y) ↔ ((∃ b, CanReturn y b) → AllOutputs p x) := by
  simp only [AllOutputs, canReturn_seqLeft_iff]
  exact ⟨fun h hy a ha => h a ⟨ha, hy⟩, fun h a ⟨ha, hy⟩ => h hy a ha⟩

@[simp]
theorem allOutputs_seqRight_iff (p : β → Prop) (x : m α) (y : m β) :
    AllOutputs p (x *> y) ↔ ((∃ a, CanReturn x a) → AllOutputs p y) := by
  simp only [AllOutputs, canReturn_seqRight_iff]
  exact ⟨fun h hx b hb => h b ⟨hx, hb⟩, fun h b ⟨hx, hb⟩ => h hx b hb⟩

@[simp]
theorem someOutput_seqLeft_iff (p : α → Prop) (x : m α) (y : m β) :
    SomeOutput p (x <* y) ↔ SomeOutput p x ∧ ∃ b, CanReturn y b := by
  simp only [SomeOutput, canReturn_seqLeft_iff]
  exact ⟨fun ⟨a, ⟨ha, hy⟩, hp⟩ => ⟨⟨a, ha, hp⟩, hy⟩, fun ⟨⟨a, ha, hp⟩, hy⟩ => ⟨a, ⟨ha, hy⟩, hp⟩⟩

@[simp]
theorem someOutput_seqRight_iff (p : β → Prop) (x : m α) (y : m β) :
    SomeOutput p (x *> y) ↔ (∃ a, CanReturn x a) ∧ SomeOutput p y := by
  simp only [SomeOutput, canReturn_seqRight_iff]
  exact ⟨fun ⟨b, ⟨hx, hb⟩, hp⟩ => ⟨hx, b, hb, hp⟩, fun ⟨hx, b, hb, hp⟩ => ⟨b, ⟨hx, hb⟩, hp⟩⟩

end Applicative

end MonadAttach
