/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters, Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.WP

/-!
# Restricting the answers of an interface

`P.restrict allows` is the interface with the positions of `P` and, at a position `a`, only the
answers `b` with `allows a b`. Including those answers back into `P.B a` is a lens
`Lens.restrict P allows : Lens P (P.restrict allows)`, identity on positions with injective maps of
directions, so it is vertical in the sense of `PolyFun.PFunctor.Lens.Factorization`.
`x.restrict allows` relabels a program along it: each call keeps its position, and its
continuation is cut down to the allowed answers.

A fold over the restricted program is a fold over the original whose spec reads the continuation
only at allowed answers (`FreeM.wpFold_mapLens`). The demonic reading over the restricted program
is `demonicUnder allows` (`wpFold_demonic_restrict_iff`), and the budget, roll and worst-case
readings restricted to allowed answers are the plain readings of the restricted program
(`isChargeBoundUnder_iff_restrict`, `isRollBoundUnder_iff_restrict`,
`costUnder_eq_cost_restrict`).
-/

@[expose] public section

universe uA uB v

namespace PFunctor

/-- The interface with the positions of `P` and, at a position `a`, the answers admitted by
`allows`. -/
def restrict (P : PFunctor.{uA, uB}) (allows : (a : P.A) → P.B a → Prop) : PFunctor.{uA, uB} :=
  ⟨P.A, fun a => {b : P.B a // allows a b}⟩

/-- The inclusion of the allowed answers, as a lens from `P` to its restriction: positions are
fixed and an allowed answer is sent to itself. -/
def Lens.restrict (P : PFunctor.{uA, uB}) (allows : (a : P.A) → P.B a → Prop) :
    Lens P (P.restrict allows) :=
  id ⇆ fun _ b => b.1

namespace FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- A program relabelled along the inclusion of the allowed answers: each call keeps its position,
and its continuation is cut down to the answers admitted by `allows`. -/
protected def restrict (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α) :
    FreeM (P.restrict allows) α :=
  x.mapLens (Lens.restrict P allows)

/-- The demonic reading of the restricted program is the demonic reading over allowed answers. -/
theorem wpFold_demonic_restrict_iff (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α)
    (post : α → Prop) :
    wpFold (OpSpec.demonic (P.restrict allows)) (x.restrict allows) post ↔
      wpFold (OpSpec.demonicUnder allows) x post := by
  rw [FreeM.restrict, wpFold_mapLens]
  induction x with
  | pure a => exact Iff.rfl
  | lift_bind a r ih =>
    exact ⟨fun h b hb => (ih b).1 (h ⟨b, hb⟩), fun h b => (ih b.1).2 (h b.1 b.2)⟩

end FreeM

end PFunctor
