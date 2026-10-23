/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceBundle

/-!
# Quoted importer canaries

Raw constructor data from `PolyFunCryptol/artifacts/references/import-canaries.json`, including
source identities, schemes and annotations. `PolyFunCryptol/scripts/export_cases.py`
checks byte-for-byte reproduction from the pinned official frontend.
-/

public section

namespace Cryptol.Tests.ImportedCanariesSource

open Cryptol Translation

/-- Source declaration 1 in dependency order. -/
@[expose] def declaration0 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4686 "higherOrder" "ImportCanaries::higherOrder" )
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCFun" [(.constructor
  "TC TCInteger" []), (.constructor "TC TCInteger" [])]), (.constructor "TC TCFun" [(.constructor
  "TC TCFun" [(.constructor "TC TCInteger" []), (.constructor "TC TCInteger" [])]), (.constructor
  "TC TCFun" [(.constructor "TC TCInteger" []), (.constructor "TC TCInteger" [])])])]))
  (.expression (.abs (Reference.Name.mk 4699 "f" "f" ) (.constructor "TC TCFun" [(.constructor
  "TC TCInteger" []), (.constructor "TC TCInteger" [])]) (.abs (Reference.Name.mk 4700 "g" "g" )
  (.constructor "TC TCFun" [(.constructor "TC TCInteger" []), (.constructor "TC TCInteger" [])])
  (.abs (Reference.Name.mk 4701 "x" "x" ) (.constructor "TC TCInteger" []) (.app (.var
  (Reference.Name.mk 4699 "f" "f" )) (.app (.var (Reference.Name.mk 4700 "g" "g" )) (.var
  (Reference.Name.mk 4701 "x" "x" )))))))))

/-- Source declaration 2 in dependency order. -/
@[expose] def declaration1 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4685 "tupleSelect" "ImportCanaries::tupleSelect" )
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.tuple 2 [(.constructor "TC TCInteger"
  []), (.constructor "TC TCBit" [])]), (.constructor "TC TCInteger" [])])) (.expression (.abs
  (Reference.Name.mk 4698 "p" "p" ) (.tuple 2 [(.constructor "TC TCInteger" []), (.constructor
  "TC TCBit" [])]) (.select (.var (Reference.Name.mk 4698 "p" "p" )) (.tuple 0 .none)))))

/-- Source declaration 3 in dependency order. -/
@[expose] def declaration2 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4684 "recordSelect" "ImportCanaries::recordSelect" )
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.record [(Prod.mk "flag" (.constructor
  "TC TCBit" [])), (Prod.mk "value" (.constructor "TC TCInteger" []))]), (.constructor
  "TC TCInteger" [])])) (.expression (.abs (Reference.Name.mk 4697 "r" "r" ) (.record [(Prod.mk
  "flag" (.constructor "TC TCBit" [])), (Prod.mk "value" (.constructor "TC TCInteger" []))])
  (.select (.var (Reference.Name.mk 4697 "r" "r" )) (.record "value" .none)))))

/-- Source declaration 4 in dependency order. -/
@[expose] def declaration3 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4255 "foldl" "Cryptol::foldl" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 366 .number), (Reference.Parameter.mk 367 .value),
  (Reference.Parameter.mk 368 .value)] [(.constructor "PC PFin" [(.var (Reference.Parameter.mk
  366 .number))])] (.constructor "TC TCFun" [(.constructor "TC TCFun" [(.var
  (Reference.Parameter.mk 367 .value)), (.constructor "TC TCFun" [(.var (Reference.Parameter.mk
  368 .value)), (.var (Reference.Parameter.mk 367 .value))])]), (.constructor "TC TCFun" [(.var
  (Reference.Parameter.mk 367 .value)), (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.var
  (Reference.Parameter.mk 366 .number)), (.var (Reference.Parameter.mk 368 .value))]), (.var
  (Reference.Parameter.mk 367 .value))])])])) .primitive)

/-- Source declaration 5 in dependency order. -/
@[expose] def declaration4 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4227 "@" "(Cryptol::@)" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 188 .number), (Reference.Parameter.mk 189 .value),
  (Reference.Parameter.mk 190 .value)] [(.constructor "PC PIntegral" [(.var
  (Reference.Parameter.mk 190 .value))])] (.constructor "TC TCFun" [(.constructor "TC TCSeq"
  [(.var (Reference.Parameter.mk 188 .number)), (.var (Reference.Parameter.mk 189 .value))]),
  (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 190 .value)), (.var
  (Reference.Parameter.mk 189 .value))])])) .primitive)

/-- Source declaration 6 in dependency order. -/
@[expose] def declaration5 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4150 "+" "(Cryptol::+)" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 80 .value)] [(.constructor "PC PRing" [(.var (Reference.Parameter.mk
  80 .value))])] (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 80 .value)),
  (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 80 .value)), (.var
  (Reference.Parameter.mk 80 .value))])])) .primitive)

/-- Source declaration 7 in dependency order. -/
@[expose] def declaration6 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4683 "capture" "ImportCanaries::capture" )
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCInteger" []),
  (.constructor "TC TCFun" [(.constructor "TC TCInteger" []), (.constructor "TC TCInteger"
  [])])])) (.expression (.abs (Reference.Name.mk 4693 "x" "x" ) (.constructor "TC TCInteger" [])
  (.whereE (.var (Reference.Name.mk 4695 "answer" "answer" )) [(.nonrecursive (Reference.Decl.mk
  (Reference.Name.mk 4694 "saved" "saved" ) (Reference.Schema.mk [] [] (.constructor
  "TC TCInteger" [])) (.expression (.var (Reference.Name.mk 4693 "x" "x" ))))), (.nonrecursive
  (Reference.Decl.mk (Reference.Name.mk 4695 "answer" "answer" ) (Reference.Schema.mk [] []
  (.constructor "TC TCFun" [(.constructor "TC TCInteger" []), (.constructor "TC TCInteger" [])]))
  (.expression (.abs (Reference.Name.mk 4696 "y" "y" ) (.constructor "TC TCInteger" []) (.app
  (.app (.proofApp (.typeApp (.var (Reference.Name.mk 4150 "+" "(Cryptol::+)" )) (.constructor
  "TC TCInteger" []))) (.var (Reference.Name.mk 4694 "saved" "saved" ))) (.var (Reference.Name.mk
  4696 "y" "y" )))))))]))))

/-- Source declaration 8 in dependency order. -/
@[expose] def declaration7 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4129 "number" "Cryptol::number" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 33 .number), (Reference.Parameter.mk 34 .value)] [(.constructor
  "PC PLiteral" [(.var (Reference.Parameter.mk 33 .number)), (.var (Reference.Parameter.mk 34
  .value))])] (.var (Reference.Parameter.mk 34 .value))) .primitive)

/-- Source declaration 9 in dependency order. -/
@[expose] def declaration8 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4687 "mapped" "ImportCanaries::mapped" )
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 3),
  (.constructor "TC TCInteger" [])]), (.constructor "TC TCSeq" [(.number 3), (.constructor
  "TC TCInteger" [])])])) (.expression (.abs (Reference.Name.mk 4702 "xs" "xs" ) (.constructor
  "TC TCSeq" [(.number 3), (.constructor "TC TCInteger" [])]) (.comprehension (.number 3)
  (.constructor "TC TCInteger" []) (.app (.app (.proofApp (.typeApp (.var (Reference.Name.mk 4150
  "+" "(Cryptol::+)" )) (.constructor "TC TCInteger" []))) (.var (Reference.Name.mk 4703 "x" "x"
  ))) (.proofApp (.typeApp (.typeApp (.var (Reference.Name.mk 4129 "number" "Cryptol::number" ))
  (.number 1)) (.constructor "TC TCInteger" [])))) [[(.from (Reference.Name.mk 4703 "x" "x" )
  (.number 3) (.constructor "TC TCInteger" []) (.var (Reference.Name.mk 4702 "xs" "xs" )))]]))))

/-- Source declaration 10 in dependency order. -/
@[expose] def declaration9 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4688 "streamMap" "ImportCanaries::streamMap" )
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.constructor
  "TC TCInf" []), (.constructor "TC TCInteger" [])]), (.constructor "TC TCSeq" [(.constructor
  "TC TCInf" []), (.constructor "TC TCInteger" [])])])) (.expression (.abs (Reference.Name.mk
  4704 "xs" "xs" ) (.constructor "TC TCSeq" [(.constructor "TC TCInf" []), (.constructor
  "TC TCInteger" [])]) (.comprehension (.constructor "TC TCInf" []) (.constructor "TC TCInteger"
  []) (.app (.app (.proofApp (.typeApp (.var (Reference.Name.mk 4150 "+" "(Cryptol::+)" ))
  (.constructor "TC TCInteger" []))) (.var (Reference.Name.mk 4705 "x" "x" ))) (.proofApp
  (.typeApp (.typeApp (.var (Reference.Name.mk 4129 "number" "Cryptol::number" )) (.number 1))
  (.constructor "TC TCInteger" [])))) [[(.from (Reference.Name.mk 4705 "x" "x" ) (.constructor
  "TC TCInf" []) (.constructor "TC TCInteger" []) (.var (Reference.Name.mk 4704 "xs" "xs"
  )))]]))))

/-- Source declaration 11 in dependency order. -/
@[expose] def declaration10 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4689 "folded" "ImportCanaries::folded" )
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 3),
  (.constructor "TC TCInteger" [])]), (.constructor "TC TCInteger" [])])) (.expression (.abs
  (Reference.Name.mk 4706 "xs" "xs" ) (.constructor "TC TCSeq" [(.number 3), (.constructor
  "TC TCInteger" [])]) (.app (.app (.app (.proofApp (.typeApp (.typeApp (.typeApp (.var
  (Reference.Name.mk 4255 "foldl" "Cryptol::foldl" )) (.number 3)) (.constructor "TC TCInteger"
  [])) (.constructor "TC TCInteger" []))) (.proofApp (.typeApp (.var (Reference.Name.mk 4150 "+"
  "(Cryptol::+)" )) (.constructor "TC TCInteger" [])))) (.proofApp (.typeApp (.typeApp (.var
  (Reference.Name.mk 4129 "number" "Cryptol::number" )) (.number 0)) (.constructor "TC TCInteger"
  [])))) (.var (Reference.Name.mk 4706 "xs" "xs" ))))))

/-- Source declaration 12 in dependency order. -/
@[expose] def declaration11 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4691 "guarded(n == 0)" "ImportCanaries::guarded(n == 0)"
  ) (Reference.Schema.mk [(Reference.Parameter.mk 929 .number)] [(.constructor "PC PFin" [(.var
  (Reference.Parameter.mk 929 .number))]), (.constructor "PC PEqual" [(.var
  (Reference.Parameter.mk 929 .number)), (.number 0)])] (.constructor "TC TCFun" [(.constructor
  "TC TCSeq" [(.var (Reference.Parameter.mk 929 .number)), (.constructor "TC TCInteger" [])]),
  (.constructor "TC TCInteger" [])])) (.expression (.typeAbs (Reference.Parameter.mk 929 .number)
  (.proofAbs (.constructor "PC PFin" [(.var (Reference.Parameter.mk 929 .number))]) (.proofAbs
  (.constructor "PC PEqual" [(.var (Reference.Parameter.mk 929 .number)), (.number 0)]) (.abs
  (Reference.Name.mk 4709 "xs" "xs" ) (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 929
  .number)), (.constructor "TC TCInteger" [])]) (.proofApp (.typeApp (.typeApp (.var
  (Reference.Name.mk 4129 "number" "Cryptol::number" )) (.number 0)) (.constructor "TC TCInteger"
  [])))))))))

/-- Source declaration 13 in dependency order. -/
@[expose] def declaration12 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4692 "guarded(n >= 1)" "ImportCanaries::guarded(n >= 1)"
  ) (Reference.Schema.mk [(Reference.Parameter.mk 931 .number)] [(.constructor "PC PFin" [(.var
  (Reference.Parameter.mk 931 .number))]), (.constructor "PC PGeq" [(.var (Reference.Parameter.mk
  931 .number)), (.number 1)])] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.var
  (Reference.Parameter.mk 931 .number)), (.constructor "TC TCInteger" [])]), (.constructor
  "TC TCInteger" [])])) (.expression (.typeAbs (Reference.Parameter.mk 931 .number) (.proofAbs
  (.constructor "PC PFin" [(.var (Reference.Parameter.mk 931 .number))]) (.proofAbs (.constructor
  "PC PGeq" [(.var (Reference.Parameter.mk 931 .number)), (.number 1)]) (.abs (Reference.Name.mk
  4711 "xs" "xs" ) (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 931 .number)),
  (.constructor "TC TCInteger" [])]) (.app (.app (.proofApp (.typeApp (.typeApp (.typeApp (.var
  (Reference.Name.mk 4227 "@" "(Cryptol::@)" )) (.var (Reference.Parameter.mk 931 .number)))
  (.constructor "TC TCInteger" [])) (.constructor "TC TCInteger" []))) (.var (Reference.Name.mk
  4711 "xs" "xs" ))) (.proofApp (.typeApp (.typeApp (.var (Reference.Name.mk 4129 "number"
  "Cryptol::number" )) (.number 0)) (.constructor "TC TCInteger" []))))))))))

/-- Source declaration 14 in dependency order. -/
@[expose] def declaration13 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4690 "guarded" "ImportCanaries::guarded" )
  (Reference.Schema.mk [(Reference.Parameter.mk 938 .number)] [(.constructor "PC PFin" [(.var
  (Reference.Parameter.mk 938 .number))])] (.constructor "TC TCFun" [(.constructor "TC TCSeq"
  [(.var (Reference.Parameter.mk 938 .number)), (.constructor "TC TCInteger" [])]), (.constructor
  "TC TCInteger" [])])) (.expression (.typeAbs (Reference.Parameter.mk 938 .number) (.proofAbs
  (.constructor "PC PFin" [(.var (Reference.Parameter.mk 938 .number))]) (.guards (.constructor
  "TC TCFun" [(.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 938 .number)),
  (.constructor "TC TCInteger" [])]), (.constructor "TC TCInteger" [])]) [(Prod.mk [(.constructor
  "PC PEqual" [(.var (Reference.Parameter.mk 938 .number)), (.number 0)])] (.proofApp (.proofApp
  (.typeApp (.var (Reference.Name.mk 4691 "guarded(n == 0)" "ImportCanaries::guarded(n == 0)" ))
  (.var (Reference.Parameter.mk 938 .number)))))), (Prod.mk [(.constructor "PC PGeq" [(.var
  (Reference.Parameter.mk 938 .number)), (.number 1)])] (.proofApp (.proofApp (.typeApp (.var
  (Reference.Name.mk 4692 "guarded(n >= 1)" "ImportCanaries::guarded(n >= 1)" )) (.var
  (Reference.Parameter.mk 938 .number))))))])))))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root0 : SourceRoot :=
  (SourceRoot.mk "capture" (.var (Reference.Name.mk 4683 "capture" "ImportCanaries::capture" ))
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCInteger" []),
  (.constructor "TC TCFun" [(.constructor "TC TCInteger" []), (.constructor "TC TCInteger"
  [])])])))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root1 : SourceRoot :=
  (SourceRoot.mk "recordSelect" (.var (Reference.Name.mk 4684 "recordSelect"
  "ImportCanaries::recordSelect" )) (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.record
  [(Prod.mk "flag" (.constructor "TC TCBit" [])), (Prod.mk "value" (.constructor "TC TCInteger"
  []))]), (.constructor "TC TCInteger" [])])))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root2 : SourceRoot :=
  (SourceRoot.mk "tupleSelect" (.var (Reference.Name.mk 4685 "tupleSelect"
  "ImportCanaries::tupleSelect" )) (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.tuple 2
  [(.constructor "TC TCInteger" []), (.constructor "TC TCBit" [])]), (.constructor "TC TCInteger"
  [])])))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root3 : SourceRoot :=
  (SourceRoot.mk "higherOrder" (.var (Reference.Name.mk 4686 "higherOrder"
  "ImportCanaries::higherOrder" )) (Reference.Schema.mk [] [] (.constructor "TC TCFun"
  [(.constructor "TC TCFun" [(.constructor "TC TCInteger" []), (.constructor "TC TCInteger"
  [])]), (.constructor "TC TCFun" [(.constructor "TC TCFun" [(.constructor "TC TCInteger" []),
  (.constructor "TC TCInteger" [])]), (.constructor "TC TCFun" [(.constructor "TC TCInteger" []),
  (.constructor "TC TCInteger" [])])])])))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root4 : SourceRoot :=
  (SourceRoot.mk "mapped" (.var (Reference.Name.mk 4687 "mapped" "ImportCanaries::mapped" ))
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 3),
  (.constructor "TC TCInteger" [])]), (.constructor "TC TCSeq" [(.number 3), (.constructor
  "TC TCInteger" [])])])))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root5 : SourceRoot :=
  (SourceRoot.mk "streamMap" (.var (Reference.Name.mk 4688 "streamMap"
  "ImportCanaries::streamMap" )) (Reference.Schema.mk [] [] (.constructor "TC TCFun"
  [(.constructor "TC TCSeq" [(.constructor "TC TCInf" []), (.constructor "TC TCInteger" [])]),
  (.constructor "TC TCSeq" [(.constructor "TC TCInf" []), (.constructor "TC TCInteger" [])])])))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root6 : SourceRoot :=
  (SourceRoot.mk "folded" (.var (Reference.Name.mk 4689 "folded" "ImportCanaries::folded" ))
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 3),
  (.constructor "TC TCInteger" [])]), (.constructor "TC TCInteger" [])])))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root7 : SourceRoot :=
  (SourceRoot.mk "(guarded : [0]Integer -> Integer)" (.proofApp (.typeApp (.var
  (Reference.Name.mk 4690 "guarded" "ImportCanaries::guarded" )) (.number 0)))
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 0),
  (.constructor "TC TCInteger" [])]), (.constructor "TC TCInteger" [])])))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root8 : SourceRoot :=
  (SourceRoot.mk "(guarded : [3]Integer -> Integer)" (.proofApp (.typeApp (.var
  (Reference.Name.mk 4690 "guarded" "ImportCanaries::guarded" )) (.number 3)))
  (Reference.Schema.mk [] [] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 3),
  (.constructor "TC TCInteger" [])]), (.constructor "TC TCInteger" [])])))

/-- The exact exported scalar bundle, retaining its provenance metadata. -/
@[expose] def bundle : SourceBundle :=
  (SourceBundle.mk "61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b" [root0, root1, root2, root3, root4,
  root5, root6, root7, root8] [(.nonrecursive declaration0), (.nonrecursive declaration1),
  (.nonrecursive declaration2), (.nonrecursive declaration3), (.nonrecursive declaration4),
  (.nonrecursive declaration5), (.nonrecursive declaration6), (.nonrecursive declaration7),
  (.nonrecursive declaration8), (.nonrecursive declaration9), (.nonrecursive declaration10),
  (.nonrecursive declaration11), (.nonrecursive declaration12), (.nonrecursive declaration13)]
  [(SourceModule.mk "Cryptol" "$builtin/Cryptol"
  "8ace6e6308a863e17355e0b8289ea52eb16c12e36b51e76f7ac668bf03a7f59e" []), (SourceModule.mk
  "ImportCanaries" "$entry/ImportCanaries.cry"
  "0955c9c3cb16f49389e57aa701f0a47d52954d58a084981f1a087ba6258af8e9" [])] [] [
  "cffd4082d3347aba60c131d2e7d33f8b8fdfaf6afa4aedd52d8d2fff7bb30a2e" ])

end Cryptol.Tests.ImportedCanariesSource
