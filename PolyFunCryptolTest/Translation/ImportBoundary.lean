/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunCryptolTest.Tutorial.Mix
import PolyFunCryptolTest.Translation.ImportModule

/-! # Imported declarations through an ordinary import

`cryptol_import` exports the bodies of the bundle, roots and checked terms, and of a module's
bundle, bodies and elaborated module, so a client module reduces them and reuses their
acceptance theorems. -/

open Cryptol Cryptol.Tests.Tutorial

example : Imported.mix.root.text = "mix" := rfl

example : Imported.bundle.roots.length = 2 := rfl

example : Imported.clear = .lam (.wordLogic .xor (.shift .right (.var .zero) (.integer 3))
    (.shift .right (.var .zero) (.integer 5))) := rfl

example : Translation.SourceElaboration.check Imported.bundle Imported.mix.root =
    .ok ⟨_, Imported.mix⟩ := Imported.mix.accepted

example : Tests.ImportModule.Loops.imported.declarations.length = 3 := rfl

example : Tests.ImportModule.Loops.imported.source = Tests.ImportModule.Loops.source := rfl

example : Tests.ImportModule.Loops.bundle.elaborate "ModuleLoops" =
    .ok Tests.ImportModule.Loops.imported := Tests.ImportModule.Loops.accepted
