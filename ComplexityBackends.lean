/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Elias Judin, Quang Dao
-/

module

public import ComplexityBackends.CslibSingleTape.Backend
public import ComplexityBackends.CslibSingleTape.BasicMachines
public import ComplexityBackends.CslibSingleTape.BitEncoding
public import ComplexityBackends.CslibSingleTape.Counting
public import ComplexityBackends.CslibSingleTape.Description
public import ComplexityBackends.CslibSingleTape.Family
public import ComplexityBackends.CslibSingleTape.Nontriviality
public import ComplexityBackends.CslibSingleTape.PPoly
public import ComplexityBackends.CslibSingleTape.PolyTime
public import ComplexityBackends.CslibSingleTape.Snoc

/-!
# Concrete complexity backends for PolyFun realizability

This library hosts optional concrete backends that instantiate PolyFun's abstract quantitative
realizability layer (`PolyFun.Realizability.Quantitative`) with a specific machine model. Each
backend lives in its own subdirectory and is self-contained: `CslibSingleTape` grounds encoded
polynomial-time families, finite-table machine constructions, and a counting separation in cslib's
single-tape Turing machines, then certifies PolyFun step maps with them. The library imports
`PolyFun`, `ToCslib`, cslib, and Mathlib; it is a separate Lake library and is intentionally absent
from the backend-neutral `PolyFun` umbrella.
-/
