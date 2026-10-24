/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.Import
import PolyFunCryptol.Translation.SourceScope
import PolyFunCryptol.Translation.SourceLink
import PolyFunCryptol.Model.Reference.Dependencies
import all Mathlib.Data.List.Sort
import PolyFunCryptol.Translation.OpenTypes
import PolyFunCryptol.Translation.OpenElaboration
import PolyFunCryptol.Translation.ModuleElaboration
import PolyFunCryptol.Translation.Declarations
import PolyFunCryptol.Model.Reference.Kinds
import PolyFunCryptol.Model.Reference.Types
import PolyFunCryptol.Model.Reference.Syntax
import PolyFunCryptol.Model.Types
import PolyFunCryptol.Model.Scheme
import PolyFunCryptol.Model.Length
import PolyFunCryptol.Model.Parameters
import PolyFunCryptol.Model.PolyScope

/-!
# Importing a whole module

`ModuleLoops` declares a recursive loop, a polymorphic combinator and a counter that calls the
loop through two integer primitives. The bundle keeps only the prelude primitives the module
reaches, and the kernel re-runs module elaboration on it.
-/

public section

namespace Cryptol.Tests.ImportModule

open Cryptol Translation Polymorphic

cryptol_import Loops from "PolyFunCryptol/artifacts/modules/canaries.json" module "ModuleLoops"

/-- The restricted bundle keeps the module and the prelude declarations it reaches. -/
example : Loops.bundle.modules.map (·.provenance.name) = ["Cryptol", "ModuleLoops"] := rfl

/-- Numeric literals and both integer primitives become explicit requirements. -/
example : Loops.imported.requirements.map (·.declaration.name.origin) =
    ["Cryptol::number", "(Cryptol::-)", "(Cryptol::>)"] := rfl

/-- The three declarations share one checked environment. -/
example : Loops.imported.declarations.length = 3 := rfl

/-- The acceptance theorem is the elaboration certificate. -/
example : Loops.bundle.ElaborationCertificate "ModuleLoops" :=
  ⟨10000, Loops.imported, Loops.accepted⟩

end Cryptol.Tests.ImportModule
