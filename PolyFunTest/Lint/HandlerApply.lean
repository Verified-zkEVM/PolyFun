/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Handler
public meta import PolyFun.Lint.HandlerApply

/-!
# The application-lemma linter

Each definition below is checked by the linter `handlerApply`. A handler built by the constructor
with no equation, or a reducible one, is reported. A handler with a generated or hand-written
equation, a combinator, and a function are not.
-/

@[expose] public section

open Lean Batteries.Tactic.Lint

namespace PFunctor.HandlerApplyTest

variable {P : PFunctor.{0, 0}}

/-- Has no application lemma. -/
def missing [∀ a, Inhabited (P.B a)] : Handler Id P where toFun _ := default

/-- Has a generated application lemma. -/
@[simps] def tagged [∀ a, Inhabited (P.B a)] : Handler Id P where toFun _ := default

/-- Is reducible, although it has an application lemma. -/
@[reducible, simps] def reducibleTagged [∀ a, Inhabited (P.B a)] : Handler Id P where
  toFun _ := default

/-- Has a hand-written equation for an answer. -/
def stated [∀ a, Inhabited (P.B a)] : Handler Id P where toFun _ := default

theorem run_stated [∀ a, Inhabited (P.B a)] (a : P.A) : stated (P := P) a = default := rfl

/-- Has only the equation lemma that `rw` derives from its definition. -/
def unfolded [∀ a, Inhabited (P.B a)] : Handler Id P where toFun _ := default

theorem eq_of_unfolded [∀ a, Inhabited (P.B a)] (h : Handler Id P) (hh : h = unfolded) :
    h = ⟨fun _ => default⟩ := by
  rw [hh, unfolded]

/-- Is built from another handler. -/
def combined (h : Handler Id P) : Handler Id P := h

/-- Is a raw function. -/
def raw (h : Handler Id P) (a : P.A) : P.B a := h a

/--
info: missing: reported
tagged: accepted
reducibleTagged: reported
stated: accepted
unfolded: reported
combined: accepted
raw: accepted
-/
#guard_msgs in
run_meta do
  let mut out : MessageData := ""
  for n in [``missing, ``tagged, ``reducibleTagged, ``stated, ``unfolded, ``combined, ``raw] do
    let r ← PolyFun.Lint.handlerApply.test n
    let verdict := if r.isSome then "reported" else "accepted"
    out := out ++ m!"{n.getString!}: {verdict}\n"
  logInfo out

end PFunctor.HandlerApplyTest
