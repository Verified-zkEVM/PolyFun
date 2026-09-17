/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Control.Monad.Writer
public import Std.Internal.Do

/-!
# `WriterT` on core's weakest-precondition stack

Core lifts a `WPMonad` interpretation through its own transformers (`StateT`, `ReaderT`,
`ExceptT`, `OptionT`); `WriterT` is Mathlib's, so its lift lives here. The carrier is `ω → Pred`,
indexed by the log written so far, exactly as `MAlgOrdered.instWriterT` indexes its lattice:
`bind` multiplies the prefix's log into the continuation's, so a postcondition that mentions the
log has to be told what has already been written, and reading the interpretation at the unit
recovers the log-oblivious one.

`WriterT.wpMonadOf` takes explicit empty/append operations and their laws, so it also
interprets append-based logs without a `Monoid` instance. The monoid specialization is scoped
under `WriterT.MonoidWP`; clients opt in with `open scoped WriterT.MonoidWP` or install an
explicit interpretation locally. Importing the module does not choose a writer interpretation.
The `@[spec]` rules for `tell`, `monadLift`, `mk`, and `run`
live in `PolyFun.Control.Do.Spec`, the tactic tier of the `Std.Do` quarantine; the entailments
they wrap are stated here.
-/

public section

universe u v w z

open Std.Internal.Do
open scoped Lean.Order

namespace WriterT

variable {m : Type u → Type v} {ω : Type u} {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] {α β : Type u}

/-- `WriterT`'s `WP` interpretation: the base interpretation of the run, with the postcondition
told the log accumulated so far. -/
@[expose, instance_reducible]
def wpInstOf (append : ω → ω → ω) [WP (m (α × ω)) (α × ω) Pred EPred] :
    WP (WriterT ω m α) α (ω → Pred) EPred where
  wpTrans x := ⟨fun post epost w => wp x.run (fun p => post p.1 (append w p.2)) epost⟩
  wp_trans_monotone x := fun _ _ _ _ hepost hpost w => by
    apply WP.wp_consequence_econs (x := x.run)
    · intro p
      exact hpost p.1 (append w p.2)
    · exact hepost

variable [Monad m] [WPMonad m Pred EPred]

/-- Interpret a writer with explicit log operations. The lawfulness witness must use the
same `WriterT.monad empty append`; no monoid instance is installed on the log type. -/
@[expose, instance_reducible]
def wpMonadOf (empty : ω) (append : ω → ω → ω)
    (right_id : ∀ w, append w empty = w)
    (assoc : ∀ a b c, append (append a b) c = append a (append b c))
    [@LawfulMonad (WriterT ω m) (WriterT.monad empty append)] :
    letI := WriterT.monad (M := m) empty append
    WPMonad (WriterT ω m) (ω → Pred) EPred := by
  letI := WriterT.monad (M := m) empty append
  exact {
    toLawfulMonad := inferInstance
    toWP _ := wpInstOf append
    pure_le_wp_pure := fun {α} x post epost w => by
      change post x w ⊑ wp (pure (x, empty) : m (α × ω))
        (fun p => post p.1 (append w p.2)) epost
      simpa only [right_id] using
        WPMonad.pure_le_wp_pure (m := m) (x, empty)
          (fun p => post p.1 (append w p.2)) epost
    bind_le_wp_bind := fun {α β} x f post epost w => by
      change wp x.run (fun p => wp (f p.1).run
        (fun q => post q.1 (append (append w p.2) q.2)) epost) epost ⊑
          wp (x.run >>= fun p => (fun q : β × ω => (q.1, append p.2 q.2)) <$> (f p.1).run)
            (fun q => post q.1 (append w q.2)) epost
      refine Lean.Order.PartialOrder.rel_trans (WP.wp_consequence x.run _ _ epost fun p => ?_)
        (WPMonad.bind_le_wp_bind x.run _ _ epost)
      exact WPMonad.map_le_wp_map' _ (f p.1).run _ _ epost (funext fun q => by rw [assoc]) }

/-- The explicit writer interpretation exposes its accumulated-log equation. -/
@[simp]
theorem wpInstOf_apply_eq (append : ω → ω → ω) (x : WriterT ω m α)
    (post : α → ω → Pred) (epost : EPred) (w : ω) :
    (wpInstOf append).wp x post epost w =
      wp x.run (fun p => post p.1 (append w p.2)) epost := rfl

/-- Writing a log fragment extends the accumulated log with the chosen append operation. -/
theorem le_wp_tell_of (append : ω → ω → ω) (out : ω)
    (post : PUnit → ω → Pred) (epost : EPred) :
    (fun w => post ⟨⟩ (append w out)) ⊑
      (wpInstOf append).wp (MonadWriter.tell out : WriterT ω m PUnit) post epost :=
  fun w => WPMonad.pure_le_wp_pure (m := m) (⟨⟩, out)
    (fun p => post p.1 (append w p.2)) epost

/-- Lifting with the chosen empty log leaves the accumulated prefix unchanged. -/
theorem le_wp_liftTell_of (empty : ω) (append : ω → ω → ω)
    (right_id : ∀ w, append w empty = w) (x : m α)
    (post : α → ω → Pred) (epost : EPred) :
    (fun w => wp x (fun a => post a w) epost) ⊑
      (wpInstOf append).wp ((WriterT.liftTell empty).monadLift x) post epost :=
  fun w => WPMonad.map_le_wp_map' (fun a => (a, empty)) x _ _ epost
    (funext fun a => by simp only [right_id])

/-- Starting the accumulated-log interpretation at a left identity gives the base run. -/
theorem wp_run_eq_of (empty : ω) (append : ω → ω → ω)
    (left_id : ∀ w, append empty w = w) (x : WriterT ω m α)
    (post : α × ω → Pred) (epost : EPred) :
    wp x.run post epost = (wpInstOf append).wp x (fun a w => post (a, w)) epost empty := by
  simp only [wpInstOf_apply_eq, left_id]

variable [Monoid ω]

/-- The accumulated-log interpretation for multiplicative monoid logs. -/
@[expose, instance_reducible]
def wpInst [WP (m (α × ω)) (α × ω) Pred EPred] :
    WP (WriterT ω m α) α (ω → Pred) EPred := wpInstOf (· * ·)

namespace MonoidWP

/-- Opt-in writer interpretation for multiplicative monoid logs. -/
scoped instance instWPMonad : WPMonad (WriterT ω m) (ω → Pred) EPred :=
  wpMonadOf 1 (· * ·) mul_one mul_assoc

end MonoidWP

open scoped MonoidWP

@[simp, grind =]
theorem wp_apply_eq (x : WriterT ω m α) (post : α → ω → Pred) (epost : EPred) (w : ω) :
    wp x post epost w = wp x.run (fun p => post p.1 (w * p.2)) epost :=
  rfl

/-- Writing to the log advances the accumulated log the postcondition sees. -/
theorem le_wp_tell (out : ω) (post : PUnit → ω → Pred) (epost : EPred) :
    (fun w => post ⟨⟩ (w * out)) ⊑ wp (MonadWriter.tell out : WriterT ω m PUnit) post epost :=
  fun w => WPMonad.pure_le_wp_pure (m := m) (⟨⟩, out) (fun p => post p.1 (w * p.2)) epost

/-- A lifted base computation writes nothing. -/
theorem le_wp_monadLift (x : m α) (post : α → ω → Pred) (epost : EPred) :
    (fun w => wp x (fun a => post a w) epost) ⊑
      wp (MonadLift.monadLift x : WriterT ω m α) post epost :=
  fun w => WPMonad.map_le_wp_map' (fun a => (a, (1 : ω))) x _ _ epost
    (funext fun a => by simp only [mul_one])

@[simp, grind =]
theorem wp_mk_apply_eq (x : m (α × ω)) (post : α → ω → Pred) (epost : EPred) (w : ω) :
    wp (WriterT.mk x : WriterT ω m α) post epost w = wp x (fun p => post p.1 (w * p.2)) epost :=
  rfl

/-- Running a writer computation from the empty log. -/
theorem wp_run_eq (x : WriterT ω m α) (post : α × ω → Pred) (epost : EPred) :
    wp x.run post epost = wp x (fun a w => post (a, w)) epost 1 := by
  simp only [wp_apply_eq, one_mul]

end WriterT
