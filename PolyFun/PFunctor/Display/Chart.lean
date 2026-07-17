/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.PFunctor.Display.Basic
public import PolyFun.PFunctor.Chart.Basic

/-!
# Displays as polynomial charts

A display over `P` has a normalized total polynomial whose positions and
directions are the total spaces of the displayed position and direction
families. Projecting those total spaces gives a chart back to `P`.

This is a comparison theorem, not the primary representation: keeping the
fibers as `PFunctor.Display.position` and `PFunctor.Display.direction` avoids
the equality transports required to recover them from an arbitrary chart.

Conversely, `Display.ofChart f` takes the literal fibers of an arbitrary chart
`f : Chart Q P`. Its displayed positions and directions therefore contain
equality witnesses. Thus displays are a fiberwise normal form for charts into
`P`, while a display is preferable when those fibers are the primitive data.
-/

@[expose] public section

universe uA uB uC uD uA' uB'

namespace PFunctor
namespace Display

variable {P : PFunctor.{uA, uB}}

/-- The total polynomial of a display. Its positions pair a base position
with a displayed position, and its directions pair a base direction with a
displayed direction above it. -/
def total (S : Display.{uA, uB, uC, uD} P) :
    PFunctor.{max uA uC, max uB uD} where
  A := Σ a, S.position a
  B ac := Σ b, S.direction ac.1 ac.2 b

@[simp]
theorem total_A (S : Display.{uA, uB, uC, uD} P) :
    S.total.A = (Σ a, S.position a) :=
  rfl

@[simp]
theorem total_B (S : Display.{uA, uB, uC, uD} P)
    (a : P.A) (c : S.position a) :
    S.total.B ⟨a, c⟩ = (Σ b, S.direction a c b) :=
  rfl

/-- The chart forgetting displayed positions and directions. -/
def forget (S : Display.{uA, uB, uC, uD} P) : Chart S.total P where
  toFunA ac := ac.1
  toFunB _ bd := bd.1

@[simp]
theorem forget_toFunA (S : Display.{uA, uB, uC, uD} P)
    (a : P.A) (c : S.position a) :
    S.forget.toFunA ⟨a, c⟩ = a :=
  rfl

@[simp]
theorem forget_toFunB (S : Display.{uA, uB, uC, uD} P)
    (a : P.A) (c : S.position a) (b : P.B a)
    (d : S.direction a c b) :
    S.forget.toFunB ⟨a, c⟩ ⟨b, d⟩ = b :=
  rfl

/-! ## Recovering fibers from a chart -/

/-- The display whose positions and directions are the literal fibers of a
chart into `P`.

Unlike a primitive display, this representation carries equality witnesses
and transports because the source polynomial was not originally presented as
dependent fibers over `P`. -/
def ofChart {Q : PFunctor.{uA', uB'}} (f : Chart Q P) :
    Display.{uA, uB, uA', uB'} P where
  position a := {q : Q.A // f.toFunA q = a}
  direction _a q b :=
    {d : Q.B q.1 // q.2 ▸ f.toFunB q.1 d = b}

@[simp]
theorem ofChart_position {Q : PFunctor.{uA', uB'}} (f : Chart Q P)
    (a : P.A) :
    (ofChart f).position a = {q : Q.A // f.toFunA q = a} :=
  rfl

@[simp]
theorem ofChart_direction {Q : PFunctor.{uA', uB'}} (f : Chart Q P)
    (a : P.A) (q : (ofChart f).position a) (b : P.B a) :
    (ofChart f).direction a q b =
      {d : Q.B q.1 // q.2 ▸ f.toFunB q.1 d = b} :=
  rfl

/-- Forget the equality witnesses in the total polynomial of the fiber display
of a chart. -/
def ofChartSource {Q : PFunctor.{uA', uB'}} (f : Chart Q P) :
    Chart (ofChart f).total Q where
  toFunA aq := aq.2.1
  toFunB _ bd := bd.2.1

/-- Present each source position and direction as an inhabitant of its literal
fiber in `ofChart f`. -/
def ofChartLift {Q : PFunctor.{uA', uB'}} (f : Chart Q P) :
    Chart Q (ofChart f).total where
  toFunA q := ⟨f.toFunA q, ⟨q, rfl⟩⟩
  toFunB q d := ⟨f.toFunB q d, ⟨d, rfl⟩⟩

@[simp]
theorem ofChartSource_toFunA {Q : PFunctor.{uA', uB'}} (f : Chart Q P)
    (a : P.A) (q : (ofChart f).position a) :
    (ofChartSource f).toFunA ⟨a, q⟩ = q.1 :=
  rfl

@[simp]
theorem ofChartSource_toFunB {Q : PFunctor.{uA', uB'}} (f : Chart Q P)
    (a : P.A) (q : (ofChart f).position a) (b : P.B a)
    (d : (ofChart f).direction a q b) :
    (ofChartSource f).toFunB ⟨a, q⟩ ⟨b, d⟩ = d.1 :=
  rfl

@[simp]
theorem ofChartLift_toFunA {Q : PFunctor.{uA', uB'}} (f : Chart Q P)
    (q : Q.A) :
    (ofChartLift f).toFunA q = ⟨f.toFunA q, ⟨q, rfl⟩⟩ :=
  rfl

@[simp]
theorem ofChartLift_toFunB {Q : PFunctor.{uA', uB'}} (f : Chart Q P)
    (q : Q.A) (d : Q.B q) :
    (ofChartLift f).toFunB q d = ⟨f.toFunB q d, ⟨d, rfl⟩⟩ :=
  rfl

/-- The total polynomial of the literal fiber display of a chart is chart-
equivalent to its source polynomial. This makes the fiber-normal-form claim
precise. -/
def ofChartEquiv {Q : PFunctor.{uA', uB'}} (f : Chart Q P) :
    (ofChart f).total ≃c Q where
  toChart := ofChartSource f
  invChart := ofChartLift f
  left_inv := by
    ext ac bd
    · rcases ac with ⟨a, q, hq⟩
      cases hq
      rfl
    · rcases ac with ⟨a, q, hq⟩
      cases hq
      rcases bd with ⟨b, d, hd⟩
      cases hd
      rfl
  right_inv := rfl

end Display
end PFunctor
