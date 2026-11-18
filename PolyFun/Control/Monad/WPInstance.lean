/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Std.WP

/-!
# Core's judgments at an explicit interpretation

Core's `Triple`, `WPConjunctive`, and `LawfulWPMonadAttach` take their interpretation as an
instance-implicit argument, and so do their constructors and projections. Some interpretations
are constructions rather than instances, such as `MAlgOrdered.toWP α` or
`MonadAttach.toWPMonadDemonic`. A proof about one of them cannot build or project these structures
directly: `⟨h⟩` and `h.le_wp` search for the interpretation again, and instance search does not
find a construction. The lemmas here take the interpretation as an explicit argument, which a goal
or a hypothesis determines by unification. Each states its judgment through `inst.wp`:

* `WP.triple_iff` and `WP.triple_of_le_wp` for core's `Triple`;
* `WP.wpConjunctive_iff` for conjunctivity at a program;
* `WPMonad.lawfulWPMonadAttach_iff` for soundness with respect to lawful attachment.

They are upstream candidates for core's `Std.WP`, and they live in its namespaces.
-/

public section

universe u v w w' z

namespace Std.WP

open Lean.Order

namespace WP

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type w'} [Assertion Pred]
  [Assertion EPred]

/-- `Triple.iff` at an explicit interpretation: a triple is an entailment of the weakest
precondition. Upstream candidate. -/
theorem triple_iff (inst : WP Prog Value Pred EPred) {x : Prog} {pre : Pred}
    {post : Value → Pred} {epost : EPred} :
    (letI := inst; Triple x pre post epost) ↔ pre ⊑ inst.wp x post epost :=
  letI := inst
  Triple.iff

/-- `Triple.intro` at an explicit interpretation. Upstream candidate. -/
theorem triple_of_le_wp (inst : WP Prog Value Pred EPred) {x : Prog} {pre : Pred}
    {post : Value → Pred} {epost : EPred} (h : pre ⊑ inst.wp x post epost) :
    letI := inst; Triple x pre post epost :=
  (triple_iff inst).mpr h

/-- Conjunctivity at a program, at an explicit interpretation: the meet of two weakest
preconditions lies below the weakest precondition of the meets. Upstream candidate. -/
theorem wpConjunctive_iff (inst : WP Prog Value Pred EPred) (x : Prog) :
    (letI := inst; WPConjunctive x) ↔
      ∀ (Q₁ Q₂ : Value → Pred) (E₁ E₂ : EPred),
        meet (inst.wp x Q₁ E₁) (inst.wp x Q₂ E₂) ⊑ inst.wp x (meet Q₁ Q₂) (meet E₁ E₂) :=
  letI := inst
  ⟨fun h => h.wp_meet_wp_le, fun h => ⟨h⟩⟩

end WP

namespace WPMonad

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type z} [Monad m] [MonadAttach m]
  [LawfulMonadAttach m] [Assertion Pred] [Assertion EPred]

/-- Soundness with respect to lawful attachment, at an explicit interpretation: a postcondition
that the weakest precondition proves holds at every value the program can return. Upstream
candidate. -/
theorem lawfulWPMonadAttach_iff (inst : WPMonad m Pred EPred) :
    (letI := inst; LawfulWPMonadAttach m Pred EPred) ↔
      ∀ {α : Type u} {x : m α} {P : α → Prop} {a : α}, MonadAttach.CanReturn x a →
        top ⊑ (inst.toWP α).wp x (fun a => ⌜P a⌝) top → P a :=
  letI := inst
  ⟨fun h => h.of_canReturn_wp, fun h => ⟨h⟩⟩

end WPMonad

end Std.WP
