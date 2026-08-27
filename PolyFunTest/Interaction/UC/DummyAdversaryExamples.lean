/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Interaction.UC.DummyAdversary
public import PolyFun.Interaction.UC.OpenSyntax.Expr

/-!
# Dummy-adversary examples

Regression checks that the dummy-adversary and split-mono reductions apply on
the free syntax model, whose strict compact-closed instance supplies both the
zig-zag laws and (through `respectsFactorization_of_hasPlugWireFactor`) the
observation laws for every observation.
-/

@[expose] public section

universe u

namespace Interaction.UC.DummyAdversaryExamples

variable {Atom : PortBoundary → Type u}
  (Obs : Observation (OpenSyntax.Expr.theory Atom))

/-- Checking emulation against the dummy adversary suffices on the free
model. -/
example {Δm Δa : PortBoundary}
    {π idl : (OpenSyntax.Expr.theory Atom).Obj (PortBoundary.tensor Δm Δa)}
    (h : Emulates
      ((OpenSyntax.Expr.theory Atom).wire π
        (OpenTheory.HasIdWire.idWire (T := OpenSyntax.Expr.theory Atom) Δa))
      ((OpenSyntax.Expr.theory Atom).wire idl
        (OpenTheory.HasIdWire.idWire (T := OpenSyntax.Expr.theory Atom) Δa))
      Obs) :
    Emulates π idl Obs :=
  Emulates.of_wire_dummy h

/-- Checking emulation against any split-mono adversary suffices on the free
model. -/
example {Δm Δa β : PortBoundary}
    {π idl : (OpenSyntax.Expr.theory Atom).Obj (PortBoundary.tensor Δm Δa)}
    {A : (OpenSyntax.Expr.theory Atom).Obj
      (PortBoundary.tensor (PortBoundary.swap Δa) β)}
    {Rt : (OpenSyntax.Expr.theory Atom).Obj
      (PortBoundary.tensor (PortBoundary.swap β) Δa)}
    (hRetract : (OpenSyntax.Expr.theory Atom).wire A Rt =
      OpenTheory.HasIdWire.idWire (T := OpenSyntax.Expr.theory Atom) Δa)
    (h : Emulates ((OpenSyntax.Expr.theory Atom).wire π A)
      ((OpenSyntax.Expr.theory Atom).wire idl A) Obs) :
    Emulates π idl Obs :=
  Emulates.of_wire_splitMono hRetract h

end Interaction.UC.DummyAdversaryExamples
