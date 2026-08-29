/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Elias Judin
-/

module

public import ToCslib.Computability.BitEncoding
public import ToCslib.Computability.SingleTape.Counting
public import ToCslib.Data.BitVec

/-!
# Extensions of the pinned cslib machine library

This library contains reusable facts and constructions about cslib machines. It
does not import PolyFun's realizability theory or any downstream oracle or
cryptographic semantics. Backend adapters in `PolyFun.Realizability.Backend`
may import these modules explicitly.
-/
