{-# LANGUAGE CPP, LambdaCase, OverloadedStrings #-}
-- Copyright (c) 2026 PolyFun Contributors. Apache-2.0.
-- Serialize Cryptol 3.6.0's typechecked AST without erasing proof applications,
-- polymorphic binders, recursive groups, guards, or foreign fallback bodies.
module Main (main) where

import Control.Monad (unless, when)
import Data.Aeson (Value, object, (.=), toJSON, encode)
import Data.Graph (SCC(..), stronglyConnComp)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import System.Directory (canonicalizePath)
import System.Environment (getArgs)
import System.FilePath (makeRelative, takeFileName, isRelative, splitDirectories)
import System.Exit (die)

import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.TypeCheck.Type as T
import qualified Cryptol.TypeCheck.FFI.FFIType as FFI
import qualified Cryptol.ModuleSystem.Name as N
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem as Module
import qualified Cryptol.ModuleSystem.Base as Base
import qualified Cryptol.ModuleSystem.Monad as Module
import qualified Cryptol.Parser.Selector as S
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Parser.Position as Position
import qualified Cryptol.Utils.RecordMap as R
import qualified Cryptol.IR.FreeVars as F
import qualified Cryptol.REPL.Command as Cmd
import qualified Cryptol.REPL.Monad as Repl
import Cryptol.Utils.Ident (Ident, unpackIdent, preludeReferenceName, prelPrim, identText)
import Cryptol.Utils.PP (PP, pp)
import qualified Cryptol.TypeCheck.Solver.InfNat as Num
import qualified Cryptol.TypeCheck.Solver.Class as Class
import qualified Cryptol.TypeCheck.Solver.Types as Solve
import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Type as EvalType
import qualified Cryptol.Transform.Specialize as Specialize
import Cryptol.Utils.Logger (stderrLogger)
import Cryptol.ModuleSystem.Fingerprint (fingerprint, fingerprintHexString)

-- This is a build identity, checked against the linked source tree by the driver.
frontendPatches :: [Text.Text]
#ifdef CRYPTOL_CASE_BINDER_TYPES
frontendPatches = ["cffd4082d3347aba60c131d2e7d33f8b8fdfaf6afa4aedd52d8d2fff7bb30a2e"]
#else
frontendPatches = []
#endif

node :: String -> [Value] -> Value
node tag args = object ["tag" .= tag, "args" .= args]

shown :: Show a => a -> Value
shown = toJSON . show

pretty :: PP a => a -> String
pretty = show . pp

name :: N.Name -> Value
name n = object ["id" .= N.nameUnique n, "text" .= unpackIdent (N.nameIdent n),
                 "origin" .= pretty n]

kind :: T.Kind -> Value
kind = \case
  T.KNum -> node "num" []
  T.KType -> node "type" []
  T.KProp -> node "prop" []
  a T.:-> b -> node "arrow" [kind a, kind b]

parameter :: T.TParam -> Value
parameter p = object ["id" .= T.tpUnique p, "kind" .= kind (T.tpKind p)]

selector :: S.Selector -> Value
selector = \case
  S.TupleSel i shape -> node "tuple" [toJSON i, toJSON shape]
  S.RecordSel f shape -> node "record"
    [toJSON (unpackIdent f), toJSON (map unpackIdent <$> shape)]
  S.ListSel i shape -> node "list" [toJSON i, toJSON shape]

-- Versioned wire tags are independent of upstream Show instances.
constructorTag :: T.TCon -> Text.Text
constructorTag = \case
  T.TC T.TCInf -> "TC TCInf"
  T.TC T.TCBit -> "TC TCBit"
  T.TC T.TCInteger -> "TC TCInteger"
  T.TC T.TCFloat -> "TC TCFloat"
  T.TC T.TCIntMod -> "TC TCIntMod"
  T.TC T.TCRational -> "TC TCRational"
  T.TC T.TCArray -> "TC TCArray"
  T.TC T.TCSeq -> "TC TCSeq"
  T.TC T.TCFun -> "TC TCFun"
  T.PC T.PEqual -> "PC PEqual"
  T.PC T.PNeq -> "PC PNeq"
  T.PC T.PGeq -> "PC PGeq"
  T.PC T.PFin -> "PC PFin"
  T.PC T.PPrime -> "PC PPrime"
  T.PC T.PNotPrime -> "PC PNotPrime"
  T.PC T.PZero -> "PC PZero"
  T.PC T.PLogic -> "PC PLogic"
  T.PC T.PRing -> "PC PRing"
  T.PC T.PIntegral -> "PC PIntegral"
  T.PC T.PField -> "PC PField"
  T.PC T.PRound -> "PC PRound"
  T.PC T.PEq -> "PC PEq"
  T.PC T.PCmp -> "PC PCmp"
  T.PC T.PSignedCmp -> "PC PSignedCmp"
  T.PC T.PLiteral -> "PC PLiteral"
  T.PC T.PLiteralLessThan -> "PC PLiteralLessThan"
  T.PC T.PFLiteral -> "PC PFLiteral"
  T.PC T.PValidFloat -> "PC PValidFloat"
  T.PC T.PAnd -> "PC PAnd"
  T.PC T.PTrue -> "PC PTrue"
  T.TF T.TCAdd -> "TF TCAdd"
  T.TF T.TCSub -> "TF TCSub"
  T.TF T.TCMul -> "TF TCMul"
  T.TF T.TCDiv -> "TF TCDiv"
  T.TF T.TCMod -> "TF TCMod"
  T.TF T.TCExp -> "TF TCExp"
  T.TF T.TCWidth -> "TF TCWidth"
  T.TF T.TCMin -> "TF TCMin"
  T.TF T.TCMax -> "TF TCMax"
  T.TF T.TCCeilDiv -> "TF TCCeilDiv"
  T.TF T.TCCeilMod -> "TF TCCeilMod"
  T.TF T.TCLenFromThenTo -> "TF TCLenFromThenTo"
  T.TC (T.TCNum _) -> "invalid-numeric-arity"
  T.TC (T.TCTuple _) -> "invalid-tuple-arity"
  T.PC (T.PHas _) -> "invalid-selector-arity"
  T.TError _ -> "unresolved-type-error"

ty :: T.Type -> Value
ty = \case
  T.TVar (T.TVBound p) -> node "var" [parameter p]
  T.TVar (T.TVFree i k _ _) -> node "free" [toJSON i, kind k]
  T.TCon (T.TC (T.TCNum n)) [] -> node "num" [shown n]
  T.TCon (T.TC (T.TCTuple n)) ts -> node "tuple" [toJSON n, toJSON (map ty ts)]
  T.TCon (T.PC (T.PHas sel)) ts -> node "has" [selector sel, toJSON (map ty ts)]
  T.TCon con ts -> node "con" [toJSON (constructorTag con), toJSON (map ty ts)]
  T.TUser n args body -> node "synonym" [name n, toJSON (map ty args), ty body]
  T.TRec fs -> node "record" [fields ty fs]
  T.TNominal nt args -> node "nominal" [name (T.ntName nt), toJSON (map ty args)]

fields :: (a -> Value) -> R.RecordMap Ident a -> Value
fields f = toJSON . map (\(label, x) -> (unpackIdent label, f x)) . R.canonicalFields

schema :: T.Schema -> Value
schema (T.Forall ps cs body) = object
  ["parameters" .= map parameter ps, "constraints" .= map ty cs, "body" .= ty body]

expr :: C.Expr -> Value
expr = \case
  C.EList es t -> node "list" [ty t, toJSON (map expr es)]
  C.ETuple es -> node "tuple" [toJSON (map expr es)]
  C.ERec fs -> node "record" [fields expr fs]
  C.ESel e s -> node "select" [expr e, selector s]
  C.ESet t e s v -> node "update" [ty t, expr e, selector s, expr v]
  C.EIf c a b -> node "if" [expr c, expr a, expr b]
  C.ECase e arms def -> node "case" [expr e,
    toJSON [(unpackIdent n, alt a) | (n, a) <- Map.toAscList arms], toJSON (alt <$> def)]
  C.EComp n t e bs -> node "comprehension" [ty n, ty t, expr e,
    toJSON (map (map match) bs)]
  C.EVar n -> node "var" [name n]
  C.ETAbs p e -> node "typeAbs" [parameter p, expr e]
  C.ETApp e t -> node "typeApp" [expr e, ty t]
  C.EApp f x -> node "app" [expr f, expr x]
  C.EAbs n t e -> node "abs" [name n, ty t, expr e]
  C.ELocated _ e -> expr e
  C.EProofAbs c e -> node "proofAbs" [ty c, expr e]
  C.EProofApp e -> node "proofApp" [expr e]
  C.EWhere e gs -> node "where" [expr e, toJSON (map group gs)]
  C.EPropGuards gs t -> node "guards" [ty t,
    toJSON [(map ty cs, expr e) | (cs, e) <- gs]]
  where
    alt (C.CaseAlt bs e) = object
      ["bindings" .= [(name n, ty t) | (n,t) <- bs], "body" .= expr e]

match :: C.Match -> Value
match = \case
  C.From n len t e -> node "from" [name n, ty len, ty t, expr e]
  C.Let d -> node "let" [decl d]

decl :: C.Decl -> Value
decl d = object ["name" .= name (C.dName d), "schema" .= schema (C.dSignature d),
                 "definition" .= definition (C.dDefinition d)]
  where
    definition C.DPrim = node "primitive" []
    definition (C.DExpr e) = node "expression" [expr e]
    definition (C.DForeign ffi body) = node "foreign"
      [toJSON (Text.decodeUtf8 (BL.toStrict (encode (foreignInterface ffi)))),
       toJSON (expr <$> body)]

-- The raw Show instance includes checkout paths buried in parameter flavours.
-- Retain the actual ABI as canonical structured data inside the format's opaque
-- interface string, using the same parameter/type grammar as declarations.
foreignInterface :: C.FFI -> Value
foreignInterface = \case
  C.CallC f -> funType "c" ffiType f
  C.CallAbstract f -> funType "abstract" ty f
  where
    funType convention element f = object
      ["convention" .= (convention :: String),
       "parameters" .= map parameter (FFI.ffiTParams f),
       "arguments" .= map element (FFI.ffiArgTypes f), "result" .= element (FFI.ffiRetType f)]
    ffiType = \case
      FFI.FFIBool -> node "bool" []
      FFI.FFIBasic b -> node "basic" [basic b]
      FFI.FFIArray ns b -> node "array" [toJSON (map ty ns), basic b]
      FFI.FFITuple ts -> node "tuple" [toJSON (map ffiType ts)]
      FFI.FFIRecord fs -> node "record" [fields ffiType fs]
    basic = \case
      FFI.FFIBasicVal v -> node "value" [shown v]
      FFI.FFIBasicRef (FFI.FFIInteger modulus) -> node "integer" [toJSON (ty <$> modulus)]
      FFI.FFIBasicRef FFI.FFIRational -> node "rational" []

group :: C.DeclGroup -> Value
group = \case
  C.NonRecursive d -> node "nonrecursive" [decl d]
  C.Recursive ds -> node "recursive" [toJSON (map decl ds)]

sourceRange :: N.Name -> Value
sourceRange n = let r = N.nameLoc n in object
  ["source_basename" .= takeFileName (Position.source r),
   "start" .= [Position.line (Position.from r), Position.col (Position.from r)],
   "end" .= [Position.line (Position.to r), Position.col (Position.to r)]]

-- A frontend unique is only meaningful inside its bundle. This key records the
-- defining module, spelling and source position independently of that unique.
sourceKey :: N.Name -> Value
sourceKey n = object ["module" .= fmap pretty (N.nameModPathMaybe n),
  "name" .= unpackIdent (N.nameIdent n), "location" .= sourceRange n]

typeSynonym :: T.TySyn -> Value
typeSynonym s = object ["name" .= name (T.tsName s),
  "parameters" .= map parameter (T.tsParams s),
  "constraints" .= map ty (T.tsConstraints s), "body" .= ty (T.tsDef s)]

nominalType :: T.NominalType -> Value
nominalType t = object ["name" .= name (T.ntName t),
  "parameters" .= map parameter (T.ntParams t), "kind" .= kind (T.ntKind t),
  "constraints" .= map ty (T.ntConstraints t),
  "deriving" .= [(pretty c, map ty cs) | (c,cs) <- Map.toAscList (T.ntDeriving t)],
  "definition" .= case T.ntDef t of
    T.Abstract -> node "abstract" []
    T.Struct c -> node "struct" [name (T.ntConName c), fields ty (T.ntFields c)]
    T.Enum cs -> node "enum" [toJSON [object ["name" .= name (T.ecName c),
      "number" .= T.ecNumber c, "public" .= T.ecPublic c,
      "fields" .= map ty (T.ecFields c)] | c <- cs]]]

primitiveFallbacks :: [C.Module] -> Map.Map N.Name N.Name
primitiveFallbacks modules = Map.fromList [(C.dName d, n) |
  m <- modules, g <- C.mDecls m, d <- C.groupDecls g,
  C.DPrim <- [C.dDefinition d], n <- referenceNames,
  N.asPrim (C.dName d) == Just (prelPrim (identText (N.nameIdent n)))]
  where
    referenceNames = [C.dName d | m <- modules, C.mName m == preludeReferenceName,
      g <- C.mDecls m, d <- C.groupDecls g]

-- Retain entire recursive groups whenever any member is reachable.
closure :: Map.Map N.Name N.Name -> [C.DeclGroup] -> [C.Expr] -> Either String [C.DeclGroup]
closure fallbacks groups roots
  | length bindings /= Map.size owners = Left "Duplicate global declaration identity"
  | otherwise = go (F.valDeps (F.freeVars roots))
  where
    bindings = [(C.dName d, g) | g <- groups, d <- C.groupDecls g]
    owners = Map.fromList bindings
    go needed
      | not (Set.null missing) = Left ("Unresolved globals: " ++ show (map pretty (Set.toList missing)))
      | expanded == needed = dependencyOrder selected
      | otherwise = go expanded
      where
        missing = Set.difference needed (Map.keysSet owners)
        selected = filter (any ((`Set.member` needed) . C.dName) . C.groupDecls) groups
        redirects = Set.fromList [target | n <- Set.toList needed,
          Just target <- [Map.lookup n fallbacks]]
        expanded = Set.unions (needed : redirects : [Set.union (F.valDeps (F.freeVars g))
          (Set.fromList (map C.dName (C.groupDecls g))) | g <- selected])

dependencyOrder :: [C.DeclGroup] -> Either String [C.DeclGroup]
dependencyOrder groups = mapM acyclic (stronglyConnComp vertices)
  where
    indexed = zip [0 :: Int ..] groups
    owners = Map.fromList [(C.dName d, i) | (i,g) <- indexed, d <- C.groupDecls g]
    vertices = [(g, i, Set.toList (Set.fromList [j |
      n <- Set.toList (F.valDeps (F.freeVars g)), Just j <- [Map.lookup n owners]])) |
      (i,g) <- indexed]
    acyclic (AcyclicSCC g) = Right g
    acyclic (CyclicSCC _) = Left "Dependency cycle crosses declared recursive groups"

moduleInfo :: FilePath -> FilePath -> M.LoadedModule -> IO Value
moduleInfo base entry lm = sourceInfo base entry lm $ toJSON
  [(name n, pretty target) | (n,target) <- Map.toAscList (C.mModAliases (M.lmModule lm))]

sourceInfo :: FilePath -> FilePath -> M.LoadedModuleG a -> Value -> IO Value
sourceInfo base entry lm aliases = do
  (path, bytes) <- case M.lmFilePath lm of
    M.InFile p -> do
      absolute <- canonicalizePath p
      let relative = makeRelative base absolute
          portable = if isRelative relative && not (".." `elem` splitDirectories relative)
                     then relative else
                       (if absolute == entry then "$entry/" else "$cryptol/") ++ takeFileName absolute
      contents <- BS.readFile absolute
      pure (portable, contents)
    M.InMem label bytes -> pure ("$builtin/" ++ label, bytes)
  pure $ object ["name" .= pretty (M.lmName lm), "path" .= path,
    "sha256" .= fingerprintHexString (fingerprint bytes),
    "aliases" .= aliases]

numericCases :: Value
numericCases = toJSON $
  [entry op [a,b] (f a b) | (op,f) <- binary, a <- sizes, b <- sizes] ++
  [entry op [a] (Just (f a)) | (op,f) <- unary, a <- sizes] ++
  [entry "rangeLength" [a,b,c] (Num.nLenFromThenTo a b c) | a <- sizes, b <- sizes, c <- sizes]
  where
    sizes = map Num.Nat [0,1,2,7,8,17,63,64,65] ++ [Num.Inf]
    lengthValue Num.Inf = toJSON ("inf" :: String)
    lengthValue (Num.Nat n) = toJSON (show n)
    entry op args value = object ["op" .= (op :: String), "arguments" .= map lengthValue args,
                                 "result" .= fmap lengthValue value]
    unary = [("width",Num.nWidth),("lg2",Num.nLg2)]
    binary = [("add",\a b -> Just (Num.nAdd a b)), ("sub",Num.nSub),
      ("mul",\a b -> Just (Num.nMul a b)), ("div",Num.nDiv), ("mod",Num.nMod),
      ("exp",\a b -> Just (Num.nExp a b)), ("min",\a b -> Just (Num.nMin a b)),
      ("max",\a b -> Just (Num.nMax a b)), ("ceilDiv",Num.nCeilDiv), ("ceilMod",Num.nCeilMod)]

-- Resolve structural obligations with the official class solver, then evaluate
-- its closed numeric side conditions with the official numeric evaluator.
classHolds :: T.Prop -> Bool
classHolds p = case p of
  T.TCon (T.PC pc) [a] | Just solve <- lookup pc classes -> solved (solve a)
  T.TCon (T.PC T.PLiteral) [n,a] -> solved (Class.solveLiteralInst n a)
  T.TCon (T.PC T.PLiteralLessThan) [n,a] -> solved (Class.solveLiteralLessThanInst n a)
  T.TCon (T.PC T.PAnd) ps -> all classHolds ps
  T.TCon con args -> Eval.checkProp
    (T.TCon con (map (EvalType.tNumTy . EvalType.evalNumType mempty) args))
  _ -> error ("Unsupported closed obligation: " ++ pretty p)
  where
    solved (Solve.SolvedIf ps) = all classHolds ps
    solved Solve.Unsolvable = False
    solved Solve.Unsolved = error ("Unresolved closed obligation: " ++ pretty p)
    classes = [(T.PZero,Class.solveZeroInst), (T.PLogic,Class.solveLogicInst),
      (T.PRing,Class.solveRingInst), (T.PIntegral,Class.solveIntegralInst),
      (T.PEq,Class.solveEqInst), (T.PCmp,Class.solveCmpInst),
      (T.PSignedCmp,Class.solveSignedCmpInst)]

classCases :: Value
classCases = toJSON [object ["constraint" .= ty p, "result" .= classHolds p] | p <- cases]
  where
    sizes = map (T.tNum :: Integer -> T.Type) [0,1,2,7,8,255,256] ++ [T.tInf]
    scalars = [T.tBit, T.tInteger]
    sequences = [T.tSeq n a | n <- [T.tNum (0 :: Integer), T.tNum (8 :: Integer), T.tInf],
                 a <- scalars]
    types = scalars ++ sequences ++ [T.tTuple [], T.tTuple [T.tBit,T.tInteger],
      T.tTuple [T.tSeq (T.tNum (8 :: Integer)) T.tBit, T.tInteger],
      T.tRec (R.recordFromFields [("flag",T.tBit),("word",T.tSeq (T.tNum (8 :: Integer)) T.tBit)]),
      T.tFun T.tInteger T.tBit, T.tFun T.tBit T.tInteger,
      T.tSeq (T.tNum (2 :: Integer)) (T.tSeq (T.tNum (0 :: Integer)) T.tBit)]
    classes = [T.PZero,T.PLogic,T.PRing,T.PIntegral,T.PEq,T.PCmp,T.PSignedCmp]
    cases = [T.TCon (T.PC pc) [a] | pc <- classes, a <- types] ++
      [T.TCon (T.PC pc) [n,a] | pc <- [T.PLiteral,T.PLiteralLessThan], n <- sizes, a <- types]

-- Candidate generation is deliberately separate from the trusted typed export.
-- Consumers must supply a checked correspondence before using the transformed body.
-- The convenience 'specialize' entry point clones DPrim and loses its type
-- arguments (including the value of numeric literals). Keep primitive calls
-- explicit by excluding DPrim from the specializable declaration cache.
specializeDefinitions :: C.Expr -> Module.ModuleCmd C.Expr
specializeDefinitions expression input = Module.runModuleT input $
  fmap fst $ Specialize.runSpecT Map.empty $ do
    let (parameters, body) = Specialize.destETAbs expression
        ordinary d = case C.dDefinition d of C.DPrim -> False; _ -> True
        groups = concatMap (\case
          C.NonRecursive d -> [C.NonRecursive d | ordinary d]
          C.Recursive ds -> case filter ordinary ds of
            [] -> []
            kept -> [C.Recursive kept])
          (Specialize.allDeclGroups (Module.minpModuleEnv input))
    specialized <- Specialize.specializeEWhere body groups
    pure (foldr C.ETAbs specialized parameters)

exportRoots :: Bool -> FilePath -> FilePath -> [String] -> IO Value
exportRoots specialize foundation file roots = do
      base <- canonicalizePath foundation
      entry <- canonicalizePath file
      Repl.runREPL True False stderrLogger $ do
        Repl.prependSearchPath [base]
        loaded <- Cmd.loadCmd file
        unless (Cmd.crSuccess loaded) (Repl.io (die "Cryptol module loading failed"))
        checked <- mapM (\text -> do
          parsed <- Cmd.replParseExpr text (1,1) Nothing
          (_, e, s) <- Cmd.replCheckExpr (P.noPos parsed)
          pure (text, e, s)) roots
        env <- Repl.getModuleEnv
        let modules = M.loadedModules env
            allGroups = concatMap C.mDecls modules
            referenceNames = [C.dName d | m <- modules, C.mName m == preludeReferenceName,
              g <- C.mDecls m, d <- C.groupDecls g]
            fallbacks = Map.fromList [(C.dName d, n) | g <- allGroups, d <- C.groupDecls g,
              C.DPrim <- [C.dDefinition d], n <- referenceNames,
              N.asPrim (C.dName d) == Just (prelPrim (identText (N.nameIdent n)))]
        provenance <- Repl.io $ mapM (moduleInfo base entry)
          (M.getLoadedModules (M.meLoadedModules env))
        let bundle rs = do
              groups <- either (Repl.io . die) pure
                (closure fallbacks allGroups [e | (_,e,_) <- rs])
              let retained = Set.fromList [C.dName d | g <- groups, d <- C.groupDecls g]
              pure $ object ["format" .= ("cryptol-typed-ast" :: Text.Text),
                "version" .= (1 :: Int),
                "cryptol_revision" .= ("61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b" :: Text.Text),
                "frontend_patches" .= frontendPatches,
                "roots" .= [object ["text" .= t, "expression" .= expr e, "schema" .= schema s]
                             | (t,e,s) <- rs],
                "groups" .= map group groups, "modules" .= provenance,
                "primitive_fallbacks" .= [(name n, name target) |
                  (n,target) <- Map.toAscList fallbacks, Set.member n retained]]
        source <- bundle checked
        if not specialize then pure source else do
          specialized <- mapM (\(t,e,s) -> do
            candidate <- Cmd.liftModuleCmd (specializeDefinitions e)
            pure (t,candidate,s)) checked
          candidate <- bundle specialized
          pure $ object ["format" .= ("cryptol-specialization-candidate" :: Text.Text),
            "version" .= (1 :: Int),
            "pass" .= ("Cryptol.Transform.Specialize.specializeEWhere" :: Text.Text),
            "primitive_policy" .= ("retain-explicit-instantiations" :: Text.Text),
            "source" .= source, "candidate" .= candidate]

-- Inventory uses the official module loader, including parameterized modules.
-- It is discovery data, not evidence that the Lean semantic importer accepts a module.
exportModule :: Bool -> FilePath -> FilePath -> IO Value
exportModule complete foundation file = do
  base <- canonicalizePath foundation
  entry <- canonicalizePath file
  Repl.runREPL True False stderrLogger $ do
    Repl.prependSearchPath [base]
    loaded <- Cmd.loadCmd file
    unless (Cmd.crSuccess loaded) (Repl.io (die "Cryptol module loading failed"))
    -- Loading alone need not load Reference. Retain the fallback source even
    -- when no evaluation command happened to trigger its loading.
    when complete $ do
      _ <- Cmd.liftModuleCmd (\input -> Module.runModuleT input $
        Base.loadModuleFrom True (Module.FromModule preludeReferenceName))
      pure ()
    env <- Repl.getModuleEnv
    modules <- Repl.io $ mapM (\lm -> do
      provenance <- moduleInfo base entry lm
      let m = M.lmModule lm
      pure $ object $ ["provenance" .= provenance,
        "type_parameters" .= [object ["name" .= name (T.mtpName p),
          "parameter" .= parameter (T.mtpParam p)] | p <- Map.elems (C.mParamTypes m)],
        "value_parameters" .= [object ["name" .= name (T.mvpName p),
          "schema" .= schema (T.mvpType p)] | p <- Map.elems (C.mParamFuns m)],
        "constraints" .= map (ty . P.thing) (C.mParamConstraints m),
        "exports" .= [object ["declaration" .= decl d,
          "property" .= (P.PragmaProperty `elem` C.dPragmas d),
          "location" .= let r = N.nameLoc (C.dName d) in object
            ["source_basename" .= takeFileName (Position.source r),
             "start" .= [Position.line (Position.from r), Position.col (Position.from r)],
             "end" .= [Position.line (Position.to r), Position.col (Position.to r)]]] |
          g <- C.mDecls m, d <- C.groupDecls g,
          C.isExportedBind (C.dName d) (C.mExports m)],
        "type_exports" .= [name n | n <- Map.keys (C.mTySyns m),
          C.isExportedType n (C.mExports m)],
        "nominal_exports" .= [name n | n <- Map.keys (C.mNominalTypes m),
          C.isExportedType n (C.mExports m)],
        "nested_functors" .= map name (Map.keys (C.mFunctors m)),
        "nested_signatures" .= map name (Map.keys (C.mSignatures m)),
        "groups" .= map group (C.mDecls m)] ++ if complete then
        ["type_synonyms" .= map typeSynonym (Map.elems (C.mTySyns m)),
         "nominal_types" .= map nominalType (Map.elems (C.mNominalTypes m)),
         "declarations" .= [object ["name" .= name (C.dName d),
           "source_key" .= sourceKey (C.dName d),
           "dependencies" .= map name (Set.toAscList (F.valDeps (F.freeVars d))),
           "property" .= (P.PragmaProperty `elem` C.dPragmas d)] |
           g <- C.mDecls m, d <- C.groupDecls g]] else [])
      (M.getLoadedModules (M.meLoadedModules env))
    signatures <- Repl.io $ mapM (\lm -> do
      provenance <- sourceInfo base entry lm (toJSON ([] :: [Value]))
      let sig = M.lmData lm
      pure $ object ["provenance" .= provenance,
        "type_parameters" .= [object ["name" .= name (T.mtpName p),
          "parameter" .= parameter (T.mtpParam p)] | p <- Map.elems (T.mpnTypes sig)],
        "value_parameters" .= [object ["name" .= name (T.mvpName p),
          "schema" .= schema (T.mvpType p)] | p <- Map.elems (T.mpnFuns sig)],
        "constraints" .= map (ty . P.thing) (T.mpnConstraints sig),
        "type_exports" .= map name (Map.keys (T.mpnTySyn sig)),
        "type_synonyms" .= map typeSynonym (Map.elems (T.mpnTySyn sig))])
      (M.lmLoadedSignatures (M.meLoadedModules env))
    pure $ object $ ["format" .= (if complete then "cryptol-module-bundle" else
      "cryptol-module-inventory" :: Text.Text),
      "version" .= (if complete then 3 else 1 :: Int),
      "modules" .= modules, "interfaces" .= signatures] ++ if complete then
      ["cryptol_revision" .= ("61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b" :: Text.Text),
       "frontend_patches" .= frontendPatches,
       "primitive_fallbacks" .= [(name n, name target) |
         (n,target) <- Map.toAscList (primitiveFallbacks (M.loadedModules env))]] else []

main :: IO ()
main = do
  args <- getArgs
  result <- case args of
    ["--numeric"] -> pure numericCases
    ["--classes"] -> pure classCases
    ["--module", foundation, file] -> exportModule False foundation file
    ["--module-bundle", foundation, file] -> exportModule True foundation file
    "--specialize" : foundation : file : roots@(_ : _) -> exportRoots True foundation file roots
    foundation : file : roots@(_ : _) -> exportRoots False foundation file roots
    _ -> die "Usage: cryptol-lean-export FOUNDATION MODULE ROOT [ROOT ...]"
  BL.putStrLn (encode result)
