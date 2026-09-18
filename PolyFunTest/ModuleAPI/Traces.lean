/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Supply.Trace

/-!
# Trace observations through ordinary imports

Generic consumers use monoid operations and public observation equations.
The concrete trace interleaves different response fibers and repeats a position
with distinct answers, so counting alone cannot certify its order or lookups.
-/

@[expose] public section

universe uA uB uC uD uE uF v

namespace PolyFunTest.ModuleAPI.Traces

open PFunctor

example {P : PFunctor.{uA, uB}} (first second : TraceList P) :
    TraceList.positions (first * second) =
      TraceList.positions first ++ TraceList.positions second := by
  rw [TraceList.positions_mul]

example {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (target : P.A) (first second : TraceList P) :
    TraceList.occurrences target (first * second) =
      TraceList.occurrences target first + TraceList.occurrences target second := by
  rw [TraceList.occurrences_mul]

example {P : PFunctor.{uA, uB}} [DecidableEq P.A]
    (before after : TraceList P) (target : P.A) (answer : P.B target) :
    TraceList.getAt? (before * (FreeMonoid.of (α := P.Idx) ⟨target, answer⟩ * after))
      target (TraceList.occurrences target before) = some answer :=
  TraceList.getAt?_mul_self_occurrences before after target answer

example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uC, uD}}
    {R : PFunctor.{uE, uF}} (f : P.Idx → Option Q.Idx) (g : Q.Idx → Option R.Idx)
    (first second : TraceList P) :
    TraceList.mapPartial g (TraceList.mapPartial f (first * second)) =
      TraceList.mapPartial (fun event => (f event).bind g) first *
        TraceList.mapPartial (fun event => (f event).bind g) second := by
  rw [TraceList.mapPartial_comp, TraceList.mapPartial_mul]

example {P : PFunctor.{uA, uB}} {Q : PFunctor.{uC, uD}} {X : Type v}
    (trace : Trace P X) : Trace.mapPartial (Q := Q) (fun _ => none) trace = 1 := by
  simp only [Trace.mapPartial_none]

example {P : PFunctor.{uA, uB}} {α : Type v} (a : P.A)
    (next : P.B a → FreeM P α) (answer : P.B a) (tail : FreeM.Path (next answer)) :
    FreeM.Path.trace (FreeM.liftBind a next) ⟨answer, tail⟩ =
      FreeMonoid.of (α := P.Idx) ⟨a, answer⟩ * FreeM.Path.trace (next answer) tail :=
  FreeM.Path.trace_liftBind_eq_mul a next answer tail

example {P : PFunctor.{uA, uB}} [DecidableEq P.A] {α : Type v}
    (program : FreeM P α) {s s' : Supply P} {path : FreeM.Path program}
    (h : Supply.runPath program s = some (path, s')) (a : P.A) :
    s' a = (s a).drop (TraceList.occurrences a (FreeM.Path.trace program path)) := by
  rw [Supply.apply_eq_drop_occurrences program h]

/-- Two positions whose response types differ. -/
abbrev signature : PFunctor := ⟨Bool, fun | false => Nat | true => Bool⟩

/-- An ordered trace with two distinct answers at the repeated position. -/
def events : TraceList signature :=
  FreeMonoid.of (α := signature.Idx) ⟨false, 7⟩ *
    (FreeMonoid.of (α := signature.Idx) ⟨true, true⟩ *
      FreeMonoid.of (α := signature.Idx) ⟨false, 11⟩)

/-- Keep the natural-number responses without changing their dependent payload. -/
def keepNaturals (event : signature.Idx) : Option signature.Idx :=
  if event.1 then none else some event

example : TraceList.positions events = [false, true, false] := rfl

example : TraceList.occurrences false events = 2 := by decide

example : TraceList.occurrences true events = 1 := by decide

example : TraceList.getAt? events false 0 = some 7 := by decide

example : TraceList.getAt? events false 1 = some 11 := by decide

example : TraceList.getAt? events true 0 = some true := by decide

example : TraceList.getAt? events false 2 = none := by decide

example : TraceList.getAt? (1 : TraceList signature) true 0 = none := rfl

example : (TraceList.mapPartial keepNaturals events).toList =
    [(⟨false, 7⟩ : signature.Idx), ⟨false, 11⟩] := rfl

example : TraceList.positions (TraceList.mapPartial keepNaturals events) =
    [false, false] := rfl

example : TraceList.getAt? (TraceList.mapPartial keepNaturals events) false 1 =
    some 11 := by decide

example : TraceList.getAt? (TraceList.mapPartial keepNaturals events) true 0 =
    none := by decide

example : TraceList.mapPartial (Q := signature) (fun _ => none)
    (TraceList.mapPartial keepNaturals events) = 1 := by
  rw [TraceList.mapPartial_comp]
  simp only [Option.bind_fun_none, TraceList.mapPartial_none]

end PolyFunTest.ModuleAPI.Traces
