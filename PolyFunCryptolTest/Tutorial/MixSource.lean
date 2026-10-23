/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceBundle

/-!
# Quoted tutorial source

Raw constructor data from `PolyFunCryptol/artifacts/references/tutorial.json`, including
source identities, schemes and annotations. `PolyFunCryptol/scripts/export_cases.py`
checks byte-for-byte reproduction from the pinned official frontend.
-/

public section

namespace Cryptol.Tests.Tutorial.MixSource

open Cryptol Translation

/-- Source declaration 1 in dependency order. -/
@[expose] def declaration0 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4226 ">>>" "(Cryptol::>>>)" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 331 .number), (Reference.Parameter.mk 332 .value),
  (Reference.Parameter.mk 333 .value)] [(.constructor "PC PFin" [(.var (Reference.Parameter.mk
  331 .number))]), (.constructor "PC PIntegral" [(.var (Reference.Parameter.mk 332 .value))])]
  (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 331
  .number)), (.var (Reference.Parameter.mk 333 .value))]), (.constructor "TC TCFun" [(.var
  (Reference.Parameter.mk 332 .value)), (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk
  331 .number)), (.var (Reference.Parameter.mk 333 .value))])])])) .primitive)

/-- Source declaration 2 in dependency order. -/
@[expose] def declaration1 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4224 ">>" "(Cryptol::>>)" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 325 .number), (Reference.Parameter.mk 326 .value),
  (Reference.Parameter.mk 327 .value)] [(.constructor "PC PIntegral" [(.var
  (Reference.Parameter.mk 326 .value))]), (.constructor "PC PZero" [(.var (Reference.Parameter.mk
  327 .value))])] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.var
  (Reference.Parameter.mk 325 .number)), (.var (Reference.Parameter.mk 327 .value))]),
  (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 326 .value)), (.constructor "TC TCSeq"
  [(.var (Reference.Parameter.mk 325 .number)), (.var (Reference.Parameter.mk 327 .value))])])]))
  .primitive)

/-- Source declaration 3 in dependency order. -/
@[expose] def declaration2 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4146 "^" "(Cryptol::^)" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 77 .value)] [(.constructor "PC PLogic" [(.var (Reference.Parameter.mk
  77 .value))])] (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 77 .value)),
  (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 77 .value)), (.var
  (Reference.Parameter.mk 77 .value))])])) .primitive)

/-- Source declaration 4 in dependency order. -/
@[expose] def declaration3 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4129 "number" "Cryptol::number" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 33 .number), (Reference.Parameter.mk 34 .value)] [(.constructor
  "PC PLiteral" [(.var (Reference.Parameter.mk 33 .number)), (.var (Reference.Parameter.mk 34
  .value))])] (.var (Reference.Parameter.mk 34 .value))) .primitive)

/-- Source declaration 5 in dependency order. -/
@[expose] def declaration4 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4683 "mix" "Tutorial::mix" ) (Reference.Schema.mk [] []
  (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 8), (.constructor "TC TCBit"
  [])]), (.constructor "TC TCSeq" [(.number 8), (.constructor "TC TCBit" [])])])) (.expression
  (.abs (Reference.Name.mk 4685 "x" "x" ) (.constructor "TC TCSeq" [(.number 8), (.constructor
  "TC TCBit" [])]) (.app (.app (.proofApp (.typeApp (.var (Reference.Name.mk 4146 "^"
  "(Cryptol::^)" )) (.constructor "TC TCSeq" [(.number 8), (.constructor "TC TCBit" [])]))) (.app
  (.app (.proofApp (.proofApp (.typeApp (.typeApp (.typeApp (.var (Reference.Name.mk 4226 ">>>"
  "(Cryptol::>>>)" )) (.number 8)) (.constructor "TC TCInteger" [])) (.constructor "TC TCBit"
  [])))) (.var (Reference.Name.mk 4685 "x" "x" ))) (.proofApp (.typeApp (.typeApp (.var
  (Reference.Name.mk 4129 "number" "Cryptol::number" )) (.number 3)) (.constructor "TC TCInteger"
  []))))) (.app (.app (.proofApp (.proofApp (.typeApp (.typeApp (.typeApp (.var
  (Reference.Name.mk 4224 ">>" "(Cryptol::>>)" )) (.number 8)) (.constructor "TC TCInteger" []))
  (.constructor "TC TCBit" [])))) (.var (Reference.Name.mk 4685 "x" "x" ))) (.proofApp (.typeApp
  (.typeApp (.var (Reference.Name.mk 4129 "number" "Cryptol::number" )) (.number 5))
  (.constructor "TC TCInteger" []))))))))

/-- Source declaration 6 in dependency order. -/
@[expose] def declaration5 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4684 "clear" "Tutorial::clear" ) (Reference.Schema.mk []
  [] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 8), (.constructor "TC TCBit"
  [])]), (.constructor "TC TCSeq" [(.number 8), (.constructor "TC TCBit" [])])])) (.expression
  (.abs (Reference.Name.mk 4686 "x" "x" ) (.constructor "TC TCSeq" [(.number 8), (.constructor
  "TC TCBit" [])]) (.app (.app (.proofApp (.typeApp (.var (Reference.Name.mk 4146 "^"
  "(Cryptol::^)" )) (.constructor "TC TCSeq" [(.number 8), (.constructor "TC TCBit" [])]))) (.app
  (.app (.proofApp (.proofApp (.typeApp (.typeApp (.typeApp (.var (Reference.Name.mk 4224 ">>"
  "(Cryptol::>>)" )) (.number 8)) (.constructor "TC TCInteger" [])) (.constructor "TC TCBit"
  [])))) (.var (Reference.Name.mk 4686 "x" "x" ))) (.proofApp (.typeApp (.typeApp (.var
  (Reference.Name.mk 4129 "number" "Cryptol::number" )) (.number 3)) (.constructor "TC TCInteger"
  []))))) (.app (.app (.proofApp (.proofApp (.typeApp (.typeApp (.typeApp (.var
  (Reference.Name.mk 4224 ">>" "(Cryptol::>>)" )) (.number 8)) (.constructor "TC TCInteger" []))
  (.constructor "TC TCBit" [])))) (.var (Reference.Name.mk 4686 "x" "x" ))) (.proofApp (.typeApp
  (.typeApp (.var (Reference.Name.mk 4129 "number" "Cryptol::number" )) (.number 5))
  (.constructor "TC TCInteger" []))))))))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root0 : SourceRoot :=
  (SourceRoot.mk "mix" (.var (Reference.Name.mk 4683 "mix" "Tutorial::mix" ))
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 8),
  (.constructor "TC TCBit" [])]), (.constructor "TC TCSeq" [(.number 8), (.constructor "TC TCBit"
  [])])])))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root1 : SourceRoot :=
  (SourceRoot.mk "clear" (.var (Reference.Name.mk 4684 "clear" "Tutorial::clear" ))
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 8),
  (.constructor "TC TCBit" [])]), (.constructor "TC TCSeq" [(.number 8), (.constructor "TC TCBit"
  [])])])))

/-- The exact exported scalar bundle, retaining its provenance metadata. -/
@[expose] def bundle : SourceBundle :=
  (SourceBundle.mk "61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b" [root0, root1] [(.nonrecursive
  declaration0), (.nonrecursive declaration1), (.nonrecursive declaration2), (.nonrecursive
  declaration3), (.nonrecursive declaration4), (.nonrecursive declaration5)] [(SourceModule.mk
  "Cryptol" "$builtin/Cryptol" "8ace6e6308a863e17355e0b8289ea52eb16c12e36b51e76f7ac668bf03a7f59e"
  []), (SourceModule.mk "Tutorial" "$entry/Tutorial.cry"
  "ffee675a6784c47a16fcc399acfbb95b276d03eed7f86441770c48a9f917f8cd" [])] [] [
  "cffd4082d3347aba60c131d2e7d33f8b8fdfaf6afa4aedd52d8d2fff7bb30a2e" ])

end Cryptol.Tests.Tutorial.MixSource
