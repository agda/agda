-- | Main module for Go backend.

module Agda.Compiler.GoLang.Compiler where

import Prelude hiding ( null, writeFile )
import Control.Monad.Trans
import Control.Monad (zipWithM)

import Data.Char     ( isSpace )
import Data.Foldable ( forM_ )
import Data.List     ( intercalate, partition )
import Data.Set      ( Set )
import Data.Maybe (fromMaybe)

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Text as T

import System.Directory   ( createDirectoryIfMissing )
import System.Environment ( setEnv )
import System.FilePath    ( splitFileName, (</>) )
import System.Process     ( callCommand )

import Paths_Agda

import Agda.Interaction.Options
import Agda.Interaction.Imports ( isNewerThan )

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name ( isNoName )
import Agda.Syntax.Abstract.Name
  ( ModuleName, QName,
    mnameToList, qnameName, qnameModule, nameId, qnameToList0, uglyShowName )
import Agda.Syntax.Internal
import Agda.Syntax.Literal ( Literal(..) )
import Agda.Syntax.Internal.Names (namesIn)
import qualified Agda.Syntax.Treeless as T
import Agda.Compiler.Treeless.NormalizeNames

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Quote
import Agda.TypeChecking.Reduce ( instantiateFull, reduce )
import Agda.TypeChecking.Substitute as TC ( TelV(..), raise, subst )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rewriting

import Agda.Utils.Function ( iterate' )
import Agda.Utils.List ( headWithDefault )
import Agda.Utils.List1 ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe ( boolToMaybe, catMaybes, caseMaybeM, whenNothing )
import Agda.Utils.Monad ( ifM, when )
import Agda.Utils.Null  ( null )
import Agda.Utils.Pretty (prettyShow, render)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.IO.Directory
import Agda.Utils.IO.UTF8 ( writeFile )
import Agda.Utils.Singleton ( singleton )

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.EliminateDefaults
import Agda.Compiler.Treeless.EliminateLiteralPatterns
import Agda.Compiler.Treeless.GuardsToPrims
import Agda.Compiler.Treeless.Erase ( computeErasedConstructorArgs, typeWithoutParams )
import Agda.Compiler.Treeless.Subst ()
import Agda.Compiler.Backend (Backend(..), Backend'(..), Recompile(..))

import Agda.Compiler.GoLang.Syntax
  ( Exp(Self,Global,Undefined,Null,String,Char,Integer,GoInterface,GoStruct,GoStructElement),
    LocalId(LocalId), GlobalId(GlobalId), MemberId(MemberId,MemberIndex), Module(Module, modName), Comment(Comment), TypeId(TypeId, ConstructorType, EmptyType),
    modName
  , GoQName
  )
import Agda.Compiler.GoLang.Substitution

import qualified Agda.Compiler.GoLang.Pretty as GoPretty

import Agda.Utils.Impossible (__IMPOSSIBLE__)

--------------------------------------------------
-- Entry point into the compiler
--------------------------------------------------

goBackend :: Backend
goBackend = Backend goBackend'

goBackend' :: Backend' GoOptions GoOptions GoModuleEnv Module (Maybe Exp)
goBackend' = Backend'
  { backendName           = goBackendName
  , backendVersion        = Nothing
  , options               = defaultGoOptions
  , commandLineFlags      = goCommandLineFlags
  , isEnabled             = optGoCompile
  , preCompile            = goPreCompile
  , postCompile           = goPostCompile
  , preModule             = goPreModule
  , postModule            = goPostModule
  , compileDef            = goCompileDef
  , scopeCheckingSuffices = False
  , mayEraseType          = const $ return False
      -- Andreas, 2019-05-09, see issue #3732.
      -- If you want to use Go data structures generated from Agda
      -- @data@/@record@, you might want to tell the treeless compiler
      -- not to erase these types even if they have no content,
      -- to get a stable interface.
  }

--- Options ---

data GoOptions = GoOptions
  { optGoCompile  :: Bool
  , optGoOptimize :: Bool
  , optGoMinify   :: Bool
      -- ^ Remove spaces etc. See https://en.wikipedia.org/wiki/Minification_(programming).
  , optGoVerify   :: Bool
      -- ^ Run generated code through interpreter.
  }

defaultGoOptions :: GoOptions
defaultGoOptions = GoOptions
  { optGoCompile  = False
  , optGoOptimize = False
  , optGoMinify   = False
  , optGoVerify   = False
  }

goCommandLineFlags :: [OptDescr (Flag GoOptions)]
goCommandLineFlags =
    [ Option [] ["go"] (NoArg enable) "compile program using the go backend"
    , Option [] ["go-optimize"] (NoArg enableOpt) "turn on optimizations during Go code generation"
    -- Minification is described at https://en.wikipedia.org/wiki/Minification_(programming)
    , Option [] ["go-minify"] (NoArg enableMin) "minify generated Go code"
    , Option [] ["go-verify"] (NoArg enableVerify) "except for main module, run generated Go modules through `node` (needs to be in PATH)"
    ]
  where
    enable       o = pure o{ optGoCompile  = True }
    enableOpt    o = pure o{ optGoOptimize = True }
    enableMin    o = pure o{ optGoMinify   = True }
    enableVerify o = pure o{ optGoVerify   = True }

--- Top-level compilation ---

goPreCompile :: GoOptions -> TCM GoOptions
goPreCompile opts = return opts

-- | After all modules have been compiled, copy RTE modules and verify compiled modules.

goPostCompile :: GoOptions -> IsMain -> Map.Map ModuleName Module -> TCM ()
goPostCompile opts _ ms = do

  -- Copy RTE modules.

  compDir  <- compileDir
  liftIO $ do
    dataDir <- getDataDir
    let srcDir = dataDir </> "Go"
    copyDirContent srcDir compDir

  -- Verify generated Go modules (except for main).

  reportSLn "compile.go.verify" 10 $ "Considering to verify generated Go modules"
  when (optGoVerify opts) $ do

    reportSLn "compile.go.verify" 10 $ "Verifying generated Go modules"
    liftIO $ setEnv "NODE_PATH" compDir

    forM_ ms $ \ Module{ modName } -> do
      goFile <- outFile modName
      reportSLn "compile.go.verify" 30 $ unwords [ "Considering Go module:" , goFile ]

      -- Since we do not run a Go program for real, we skip all modules that could
      -- have a call to main.
      -- Atm, modules whose compilation was skipped are also skipped during verification
      -- (they appear here as main modules).


mergeModules :: Map.Map ModuleName Module -> [(GlobalId, Exp)]
mergeModules ms
    = [ (goMod n, e)
      | (n, Module _ _ es) <- Map.toList ms
      , e <- es
      ]

--- Module compilation ---

type GoModuleEnv = Maybe CoinductionKit

goPreModule :: GoOptions -> IsMain -> ModuleName -> FilePath -> TCM (Recompile GoModuleEnv Module)
goPreModule _opts _ m ifile = ifM uptodate noComp yesComp
  where
    uptodate = liftIO =<< isNewerThan <$> outFile_ <*> pure ifile

    noComp = do
      m   <- prettyShow <$> curMName
      out <- outFile_
      reportSLn "compile.go" 1 $ repl [m, ifile, out] "Compiling go <<0>> in <<1>> to <<2>>"
      Recompile <$> coinductionKit

    -- A skipped module acts as a fake main module, to be skipped by --go-verify as well.
    skippedModule = Module (goMod m) mempty mempty

    yesComp = do
      m   <- prettyShow <$> curMName
      out <- outFile_
      reportSLn "compile.go" 1 $ repl [m, ifile, out] "Compiling go <<0>> in <<1>> to <<2>>"
      Recompile <$> coinductionKit

goPostModule :: GoOptions -> GoModuleEnv -> IsMain -> ModuleName -> [Maybe Exp] -> TCM Module
goPostModule opts _ isMain _ defs = do
  m             <- goMod <$> curMName
  is            <- map (goMod . fst) . iImportedModules <$> curIF
  let mod = Module m is es
  writeModule mod
  return mod
  where
  es       = catMaybes defs
  main     = MemberId "main"
  -- Andreas, 2020-10-27, only add invocation of "main" if such function is defined.
  -- This allows loading of generated .go files into an interpreter
  -- even if they do not define "main".


goCompileDef :: GoOptions -> GoModuleEnv -> IsMain -> Definition -> TCM (Maybe Exp)
goCompileDef opts kit _isMain def = definition (opts, kit) (defName def, def)

--------------------------------------------------
-- Naming
--------------------------------------------------

prefix :: [Char]
prefix = "golang"

goMod :: ModuleName -> GlobalId
goMod m = GlobalId (prefix : map prettyShow (mnameToList m))

goFileName :: GlobalId -> String
goFileName (GlobalId ms) = intercalate "." ms ++ ".go"

goMember :: Name -> MemberId
goMember n
  -- Anonymous fields are used for where clauses,
  -- and they're all given the concrete name "_",
  -- so we disambiguate them using their name id.
  | isNoName n = MemberId ("_" ++ show (nameId n))
  | otherwise  = MemberId $ prettyShow n

global' :: QName -> TCM (Exp, GoQName)
global' q = do
  i <- iModuleName <$> curIF
  modNm <- topLevelModuleName (qnameModule q)
  let
    -- Global module prefix
    qms = mnameToList $ qnameModule q
    -- File-local module prefix
    localms = drop (length $ mnameToList modNm) qms
    nm = fmap goMember $ List1.snoc localms $ qnameName q
  if modNm == i
    then return (Self, nm)
    else return (Global (goMod modNm), nm)

global :: QName -> TCM (Exp, GoQName)
global q = do
  d <- getConstInfo q
  case d of
    Defn { theDef = Constructor { conData = p } } -> do
      getConstInfo p >>= \case
        -- Andreas, 2020-10-27, comment quotes outdated fact.
        -- anon. constructors are now M.R.constructor.
        -- We could simplify/remove the workaround by switching "record"
        -- to "constructor", but this changes the output of the Go compiler
        -- maybe in ways that break user's developments
        -- (if they link to Agda-generated Go).
        -- -- Rather annoyingly, the anonymous constructor of a record R in module M
        -- -- is given the name M.recCon, but a named constructor C
        -- -- is given the name M.R.C, sigh. This causes a lot of hoop-jumping
        -- -- in the map from Agda names to Go names, which we patch by renaming
        -- -- anonymous constructors to M.R.record.
        Defn { theDef = Record { recNamedCon = False } } -> do
          (m,ls) <- global' p
          return (m, ls <> singleton (MemberId "record"))
        _ -> global' (defName d)
    _ -> global' (defName d)

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

type EnvWithOpts = (GoOptions, GoModuleEnv)

definition :: EnvWithOpts -> (QName,Definition) -> TCM (Maybe Exp)
definition kit (q,d) = do
  reportSDoc "compile.go" 10 $ "compiling def:" <+> prettyTCM q
  (_,ls) <- global q
  d <- instantiateFull d

  definition' kit q d (defType d) ls

defGoDef :: Definition -> Maybe String
defGoDef def =
  case defCompilerPragmas goBackendName def of
    [CompilerPragma _ s] -> Just (dropEquals s)
    []                   -> Nothing
    _:_:_                -> __IMPOSSIBLE__
  where
    dropEquals = dropWhile $ \ c -> isSpace c || c == '='

definition' :: EnvWithOpts -> QName -> Definition -> Type -> GoQName -> TCM (Maybe Exp)
definition' kit q d t ls = do
  case theDef d of
    -- coinduction
    Constructor{} | Just q == (nameOfSharp <$> snd kit) -> do
      reportSDoc "compile.go" 30 $ " con1:" <+> (text . show) d
      return Nothing
    Function{} | Just q == (nameOfFlat <$> snd kit) -> do
      reportSDoc "compile.go" 30 $ " f1:" <+> (text . show) d
      return Nothing
    DataOrRecSig{} -> __IMPOSSIBLE__
    Axiom -> return Nothing

    GeneralizableVar{} -> return Nothing
    PrimitiveSort{} -> return Nothing

    Function{} | otherwise -> do

      reportSDoc "function.go" 5 $ "compiling fun:" <+> prettyTCM q
      caseMaybeM (toTreeless T.EagerEvaluation q) (pure Nothing) $ \ treeless -> do
        used <- getCompiledArgUse q
        funBody <- eliminateCaseDefaults =<<
          eliminateLiteralPatterns
          (convertGuards treeless)
        def <- getConstInfo q  
        relv <- relView t
        let nameee = qnameToList0 q
        reportSDoc "function.go" 30 $ "\n nameee:" <+> (text . show) nameee
        reportSDoc "function.go" 45 $ "\n relv:" <+> (text . show) relv
        reportSDoc "function.go" 50 $ "\n def:" <+> (text . show) def
        (tel, tt) <- typeWithoutParams q
        reportSDoc "function.go" 35 $ "\n compiled treeless fun1:" <+> (text . show) funBody
        reportSDoc "function.go" 35 $ "\n compiled treeless tel:" <+> (text . show) tel
        reportSDoc "function.go" 35 $ "\n compiled treeless fun2:" <+> pretty funBody
        reportSDoc "function.go" 30 $ "\n used:" <+> (text . show) used
        let (body, given) = lamView funBody
              where
                lamView :: T.TTerm -> (T.TTerm, Int)
                lamView (T.TLam t) = (+1) <$> lamView t
                lamView t = (t, 0)
            etaN = length $ dropWhile id $ reverse $ drop given used
        normalized <- normalizeNames funBody
        reportSDoc "function.go" 30 $ "\n body:" <+> (text . show) body
        let ty  = (defType def)
        reportSDoc "function.go" 30 $ "\n ty:" <+> (text . show) ty
        reportSDoc "function.go" 30 $ "\n given:" <+> (text . show) given
        reportSDoc "function.go" 30 $ "\n etaN:" <+> (text . show) etaN
        return Nothing

    Primitive{primName = p} -> return Nothing
    Datatype{ dataPathCons = _ : _ } -> do
      reportSDoc "compile.go" 30 $ " data tupe:" <+> (text . show) q
      s <- render <$> prettyTCM q
      typeError $ NotImplemented $
        "Higher inductive types (" ++ s ++ ")"
    Datatype{} -> do
      reportSDoc "compile.go" 40 $ " data tupe2:" <+> (text . show) d
      let nameee = uglyShowName (qnameName q)
      reportSDoc "compile.go" 30 $ "\n nameee:" <+> (text . show) nameee
      computeErasedConstructorArgs q
      name <- liftTCM $ visitorName q
      return (Just $ GoInterface $ name)
    Record{} -> do
        computeErasedConstructorArgs q
        return Nothing

    c@Constructor{conData = p, conPars = nc, conSrcCon = ch, conArity = cona} -> do
      reportSDoc "compile.go" 40 $ " constructor :" <+> (text . show) c
      reportSDoc "compile.go" 40 $ " con2:" <+> (text . show) q
      let np = arity t - nc
      typear <- liftTCM $ typeArity t
      reportSDoc "compile.go" 30 $ " np:" <+> (text . show) np
      reportSDoc "compile.go" 30 $ " nc:" <+> (text . show) nc
      reportSDoc "compile.go" 30 $ " typear:" <+> (text . show) typear
      erased <- getErasedConArgs q
      reportSDoc "compile.go" 30 $ " erased:" <+> (text . show) erased
      reportSDoc "compile.go" 30 $ " cona:" <+> (text . show) cona
      TelV tel res <- telView t
      TelV tel22 res22 <- telViewUpTo np t
      reportSDoc "compile.go" 30 $ "\n tel22:" <+> (text . show) tel22
      let nameee = uglyShowName (qnameName q)
      let defPar = defGeneralizedParams d
      let sugName = suggestName (qnameName q)
      reportSDoc "compile.go" 30 $ "\n sugName:" <+> (text . show) sugName
      reportSDoc "compile.go" 30 $ "\n defPar:" <+> (text . show) defPar
      reportSDoc "compile.go" 30 $ "\n nameee:" <+> (text . show) nameee
      reportSDoc "compile.go" 30 $ "\n res22:" <+> (text . show) res22
      (teles, ignored) <- getOutputTypeName t
      let t2 = teleNames teles
      let t3 = teleArgNames teles
      reportSDoc "compile.go" 35 $ "\n t2:" <+> (text . show) teles
      reportSDoc "compile.go" 30 $ "\n t2:" <+> (text . show) t2
      reportSDoc "compile.go" 30 $ "\n t3:" <+> (text . show) t3
      let args = map (snd . unDom) (telToList tel)
      let le = length args
      reportSDoc "compile.go" 30 $ "\n tel:" <+> (text . show) tel
      reportSDoc "compile.go" 30 $ "\n res:" <+> (text . show) res
      reportSDoc "compile.go" 30 $ "\n args:" <+> (text . show) args
      reportSDoc "compile.go" 30 $ "\n le:" <+> (text . show) le
      d <- getConstInfo p
      reportSDoc "compile.go" 40 $ " type:" <+> (text . show)  t
      conInfo <- getConstructorInfo q
      reportSDoc "compile.go" 30 $ "\n conInfo:" <+> (text . show) conInfo
      name <- liftTCM $ visitorName q
      reportSDoc "compile.go" 40 $ "\n name:" <+> (text . show)  name
      defd <- getConstInfo q
      let l = List1.last ls
      let l1 = List1.head ls
      -- l galim naudot kaip struct name
      -- struct l {_1 interface{}; _2 List; }
      reportSDoc "compile.go" 30 $ " l:" <+> (text . show) l
      reportSDoc "compile.go" 30 $ " ls:" <+> (text . show) ls
      reportSDoc "compile.go" 30 $ " l1:" <+> (text . show) l1
      (goArg, goRes) <- goTelApproximation t
      reportSDoc "compile.go" 20 $ " goTypes:" <+> (text . show) goArg
      case theDef d of
        dt -> do
          reportSDoc "compile.go" 30 $ "index:" <+> (text . show) index
          return (Just $ GoStruct l goArg)
          where
            index | Datatype{} <- dt
                  , cs <- defConstructors dt
                  = [GoStructElement (LocalId i) (mkComment l1) | (i, x) <- zip [0..] cs, x == q]
                  | otherwise = []
            mkComment (MemberId s) = TypeId s      
            mkComment _ = TypeId "unknown"
      
    AbstractDefn{} -> __IMPOSSIBLE__
--------------------------------------------------
-- Writing out a Golang module
--------------------------------------------------
visitorName :: QName -> TCM MemberId
visitorName q = do (m,ls) <- global q; return (List1.last ls)

writeModule :: Module -> TCM ()
writeModule m = do
  out <- outFile (modName m)
  reportSDoc "compile.go" 10 $ "module: :" <+> (multiLineText (show m))
  liftIO (writeFile out (GoPretty.prettyPrintGo m))

outFile :: GlobalId -> TCM FilePath
outFile m = do
  mdir <- compileDir
  let (fdir, fn) = splitFileName (goFileName m)
  let dir = mdir </> fdir
      fp  = dir </> fn
  liftIO $ createDirectoryIfMissing True dir
  return fp

goTypeApproximation :: Int -> Type -> TCM TypeId
goTypeApproximation fv t = do
  let go n t = do
        let tu = unSpine t
        case tu of
          Pi a b -> return $ TypeId "pi"
          Def q els -> do
            (MemberId name) <- liftTCM $ visitorName q
            return $ ConstructorType ("_" ++ (show n)) name
          Sort{} -> return EmptyType
          _ -> return $ ConstructorType ("_" ++ (show n)) "interface{}"
  go fv (unEl t)

goTelApproximation :: Type -> TCM ([TypeId], TypeId)
goTelApproximation t = do
  TelV tel res <- telView t
  let args = map (snd . unDom) (telToList tel)
  (,) <$> zipWithM (goTypeApproximation) [0..] args <*> goTypeApproximation (length args) res

outFile_ :: TCM FilePath
outFile_ = do
  m <- curMName
  outFile (goMod m)

-- | Cubical primitives that are (currently) not compiled.
--
-- TODO: Primitives that are neither part of this set nor of
-- 'primitives', and for which 'defGoDef' does not return anything,
-- are silently compiled to 'Undefined'. Thus, if a cubical primitive
-- is by accident omitted from 'cubicalPrimitives', then programs that
-- should be rejected are compiled to something which might not work
-- as intended. A better approach might be to list exactly those
-- primitives which should be compiled to 'Undefined'.

cubicalPrimitives :: Set String
cubicalPrimitives = Set.fromList
  [ "primIMin"
  , "primIMax"
  , "primINeg"
  , "primPartial"
  , "primPartialP"
  , "primPFrom1"
  , "primPOr"
  , "primComp"
  , "primTransp"
  , "primHComp"
  , "primSubOut"
  ]

-- | Primitives implemented in the Go Agda RTS.
primitives :: Set String
primitives = Set.fromList
  [  "primShowInteger"

  -- Natural number functions
  -- , "primNatPlus"                 -- missing
  , "primNatMinus"
  -- , "primNatTimes"                -- missing
  -- , "primNatDivSucAux"            -- missing
  -- , "primNatModSucAux"            -- missing
  -- , "primNatEquality"             -- missing
  -- , "primNatLess"                 -- missing
  -- , "primShowNat"                 -- missing

  -- Machine words
  , "primWord64ToNat"
  , "primWord64FromNat"
  -- , "primWord64ToNatInjective"    -- missing

  -- Level functions
  -- , "primLevelZero"               -- missing
  -- , "primLevelSuc"                -- missing
  -- , "primLevelMax"                -- missing

  -- Sorts
  -- , "primSetOmega"                -- missing
  -- , "primStrictSetOmega"          -- missing

  -- Floating point functions
  , "primFloatEquality"
  , "primFloatInequality"
  , "primFloatLess"
  , "primFloatIsInfinite"
  , "primFloatIsNaN"
  , "primFloatIsNegativeZero"
  , "primFloatIsSafeInteger"
  , "primFloatToWord64"
  -- , "primFloatToWord64Injective"  -- missing
  , "primNatToFloat"
  , "primIntToFloat"
  -- , "primFloatRound"              -- in Agda.Builtin.Float
  -- , "primFloatFloor"              -- in Agda.Builtin.Float
  -- , "primFloatCeiling"            -- in Agda.Builtin.Float
  -- , "primFloatToRatio"            -- in Agda.Builtin.Float
  , "primRatioToFloat"
  -- , "primFloatDecode"             -- in Agda.Builtin.Float
  -- , "primFloatEncode"             -- in Agda.Builtin.Float
  , "primShowFloat"
  , "primFloatPlus"
  , "primFloatMinus"
  , "primFloatTimes"
  , "primFloatNegate"
  , "primFloatDiv"
  , "primFloatSqrt"
  , "primFloatExp"
  , "primFloatLog"
  , "primFloatSin"
  , "primFloatCos"
  , "primFloatTan"
  , "primFloatASin"
  , "primFloatACos"
  , "primFloatATan"
  , "primFloatATan2"
  , "primFloatSinh"
  , "primFloatCosh"
  , "primFloatTanh"
  , "primFloatASinh"
  , "primFloatACosh"
  , "primFloatATanh"
  , "primFloatPow"

  -- Character functions
  -- , "primCharEquality"            -- missing
  -- , "primIsLower"                 -- missing
  -- , "primIsDigit"                 -- missing
  -- , "primIsAlpha"                 -- missing
  -- , "primIsSpace"                 -- missing
  -- , "primIsAscii"                 -- missing
  -- , "primIsLatin1"                -- missing
  -- , "primIsPrint"                 -- missing
  -- , "primIsHexDigit"              -- missing
  -- , "primToUpper"                 -- missing
  -- , "primToLower"                 -- missing
  -- , "primCharToNat"               -- missing
  -- , "primCharToNatInjective"      -- missing
  -- , "primNatToChar"               -- missing
  -- , "primShowChar"                -- in Agda.Builtin.String

  -- String functions
  -- , "primStringToList"            -- in Agda.Builtin.String
  -- , "primStringToListInjective"   -- missing
  -- , "primStringFromList"          -- in Agda.Builtin.String
  -- , "primStringFromListInjective" -- missing
  -- , "primStringAppend"            -- in Agda.Builtin.String
  -- , "primStringEquality"          -- in Agda.Builtin.String
  -- , "primShowString"              -- in Agda.Builtin.String
  -- , "primStringUncons"            -- in Agda.Builtin.String

  -- Other stuff
  -- , "primEraseEquality"           -- missing
  -- , "primForce"                   -- missing
  -- , "primForceLemma"              -- missing
  , "primQNameEquality"
  , "primQNameLess"
  , "primShowQName"
  , "primQNameFixity"
  -- , "primQNameToWord64s"          -- missing
  -- , "primQNameToWord64sInjective" -- missing
  -- , "primMetaEquality"            -- missing
  -- , "primMetaLess"                -- missing
  -- , "primShowMeta"                -- missing
  -- , "primMetaToNat"               -- missing
  -- , "primMetaToNatInjective"      -- missing
  -- , "primIMin"                    -- missing
  -- , "primIMax"                    -- missing
  -- , "primINeg"                    -- missing
  -- , "primPOr"                     -- missing
  -- , "primComp"                    -- missing
  -- , builtinTrans                  -- missing
  -- , builtinHComp                  -- missing
  -- , "primIdJ"                     -- missing
  -- , "primPartial"                 -- missing
  -- , "primPartialP"                -- missing
  -- , builtinGlue                   -- missing
  -- , builtin_glue                  -- missing
  -- , builtin_unglue                -- missing
  -- , builtinFaceForall             -- missing
  -- , "primDepIMin"                 -- missing
  -- , "primIdFace"                  -- missing
  -- , "primIdPath"                  -- missing
  -- , builtinIdElim                 -- missing
  -- , builtinSubOut                 -- missing
  -- , builtin_glueU                 -- missing
  -- , builtin_unglueU               -- missing
  ]
