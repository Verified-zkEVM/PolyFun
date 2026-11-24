/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.Control.Monad.Algebra
public import PolyFun.Control.Monad.ExactWP
public import ToCslib.Order.LeanOrder
public import Std.WP

/-!
# Ordered monad algebras as exact core weakest-precondition monads

Core's lattice-generic program logic (`Std.WP`) interprets a monad through
`WPMonad m Pred EPred`: a monotone predicate transformer per program, sound for `pure` and `bind`
up to `⊑`. An ordered monad algebra `MAlgOrdered m l` presents such an interpretation with no
exception layer, `wp x post := μ (x >>= fun a => pure (post a))`. `ToCslib.Order.LeanOrder` makes
Mathlib's `CompleteLattice l` an `Assertion`, and the algebra's laws make the interpretation
exact (`instExactWPMonadToWPMonad`).

The construction is deliberately not an instance. Install `MAlgOrdered.toWPMonad` at the base
monad (`letI` or `local instance`), and core's `StateT`, `ReaderT`, `ExceptT`, and `OptionT`
instances lift it with honest exception postconditions. Exactness lifts through the same
transformers (`PolyFun.Control.Monad.ExactWP`).

Reasoning happens on core's `wp`, under the equational `simp` set of
`PolyFun.Control.Monad.ExactWP`. The value of the interpretation is definitional
(`toWPMonad_wp`), and it is deliberately not `@[simp]`, so that `simp` keeps core's head. The
module imports the `Std.WP` root rather than its `WP` submodules, so that the `@[spec]` database
`vcgen` consults is loaded wherever an instance built here is installed. That database includes
`Spec.bind`, which lives in `Std.WP.Triple.SpecLemmas`. On a bridged carrier, the lattice
operations that core's lemmas are stated with are Mathlib's, and the transfer lemmas of
`ToCslib.Order.LeanOrder` (`LeanOrder.meet_eq_inf` and its siblings) let `simp` move between the
two spellings.
-/

public section

universe u v w

open Std.WP

namespace MAlgOrdered

variable {m : Type u → Type v} {l : Type u} [Monad m] [_root_.CompleteLattice l] [MAlgOrdered m l]
variable {α β : Type u}

/-! ## The interpretation -/

/-- The algebra fixes a pure program with a mapped output. -/
theorem μ_pure_bind_pure [LawfulMonad m] (a : α) (post : α → l) :
    MAlgOrdered.μ ((pure a : m α) >>= fun b => pure (post b)) = post a := by
  simp [MAlgOrdered.μ_pure]

/-- The algebra of a bind with a mapped output is the algebra of the first program against the
algebra of the continuations. -/
theorem μ_bind_bind_pure [LawfulMonad m] (x : m α) (f : α → m β) (post : β → l) :
    MAlgOrdered.μ ((x >>= f) >>= fun b => pure (post b)) =
      MAlgOrdered.μ (x >>= fun a => pure (MAlgOrdered.μ (f a >>= fun b => pure (post b)))) := by
  rw [bind_assoc]
  exact μ_bind x _ _ fun a => (MAlgOrdered.μ_pure _).symm

/-- The algebra of a program with a mapped output is monotone in the map. -/
theorem μ_bind_pure_mono (x : m α) {post post' : α → l} (h : ∀ a, post a ≤ post' a) :
    MAlgOrdered.μ (x >>= fun a => pure (post a)) ≤ MAlgOrdered.μ (x >>= fun a => pure (post' a)) :=
  MAlgOrdered.μ_bind_mono _ _ (fun a => by simpa [MAlgOrdered.μ_pure] using h a) x

/-- The predicate-transformer interpretation of `m α` induced by an ordered monad algebra: the
algebra of the program with its outputs mapped through the postcondition, ignoring the empty
exception postcondition. -/
@[expose, instance_reducible]
def toWP (α : Type u) : WP (m α) α l EStack⟨⟩ where
  trans x := ⟨fun post _ => MAlgOrdered.μ (x >>= fun a => pure (post a))⟩
  trans_monotone x _ _ _ _ _ hpost := μ_bind_pure_mono x hpost

/-- The value of the derived transformer. Not `@[simp]`, like `toWPMonad_wp`. -/
theorem toWP_wp {α : Type u} (x : m α) (post : α → l) (epost : EStack⟨⟩) :
    (toWP (m := m) (l := l) α).wp x post epost = MAlgOrdered.μ (x >>= fun a => pure (post a)) :=
  rfl

/-- Core's triple through the derived interpretation is Mathlib's order on the algebra. -/
theorem toWP_triple_iff {α : Type u} (x : m α) (pre : l) (post : α → l) (epost : EStack⟨⟩) :
    @Std.WP.Triple l EStack⟨⟩ (m α) α _ _ x (toWP α) pre post epost ↔
      pre ≤ MAlgOrdered.μ (x >>= fun a => pure (post a)) :=
  WP.triple_iff _

/-- An ordered monad algebra is a core weakest-precondition monad, with its soundness laws
holding as equations (`instExactWPMonadToWPMonad`). Not an instance. -/
@[expose, instance_reducible]
def toWPMonad [LawfulMonad m] : WPMonad m l EStack⟨⟩ where
  toLawfulMonad := inferInstance
  toWP := toWP
  pure_le_wp_pure x post _ := Lean.Order.PartialOrder.rel_of_eq (μ_pure_bind_pure x post).symm
  bind_le_wp_bind x f post _ :=
    Lean.Order.PartialOrder.rel_of_eq (μ_bind_bind_pure x f post).symm

/-- Core's `wp` through the derived interpretation is the algebra of the mapped program. Not
`@[simp]`: core's `wp` is the normal form, driven by the exact equations of `ExactWPMonad`. -/
theorem toWPMonad_wp [LawfulMonad m] {α : Type u} (x : m α) (post : α → l) (epost : EStack⟨⟩) :
    ((toWPMonad (m := m) (l := l)).toWP α).wp x post epost =
      MAlgOrdered.μ (x >>= fun a => pure (post a)) :=
  rfl

/-- The interpretation derived from an ordered monad algebra is exact: `wp_pure` and `wp_bind`
hold with equality. -/
instance instExactWPMonadToWPMonad [LawfulMonad m] :
    @ExactWPMonad m l EStack⟨⟩ _ _ _ (toWPMonad (m := m) (l := l)) :=
  let _ := toWPMonad (m := m) (l := l)
  ExactWPMonad.of_eq (fun a post _ => μ_pure_bind_pure a post)
    (fun x f post _ => μ_bind_bind_pure x f post)

/-- The derived interpretation is conjunctive at `x` whenever the algebra of the mapped program
preserves binary meets of postconditions. -/
theorem wpConjunctive_toWP {α : Type u} (x : m α)
    (h : ∀ Q₁ Q₂ : α → l,
      MAlgOrdered.μ (x >>= fun a => pure (Q₁ a)) ⊓ MAlgOrdered.μ (x >>= fun a => pure (Q₂ a)) ≤
        MAlgOrdered.μ (x >>= fun a => pure (Q₁ a ⊓ Q₂ a))) :
    @WPConjunctive (m α) α l EStack⟨⟩ _ _ (toWP α) x :=
  (WP.wpConjunctive_iff _ x).mpr fun Q₁ Q₂ _ _ => by
    rw [toWP_wp, toWP_wp, toWP_wp, LeanOrder.meet_eq_inf]
    refine _root_.le_trans (h Q₁ Q₂) (μ_bind_pure_mono x fun a => ?_)
    rw [Lean.Order.meet_apply, LeanOrder.meet_eq_inf]

end MAlgOrdered
