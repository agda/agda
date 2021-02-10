
module Agda.Compiler.MAlonzo.Compiler where

import Control.Arrow (second)
import Control.Monad.Except (throwError)
import Control.Monad.Reader
import Control.Monad.Writer hiding ((<>))

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Monoid (Monoid, mempty, mappend)
import Data.Semigroup ((<>))

import qualified Agda.Utils.Haskell.Syntax as HS

import System.Directory (createDirectoryIfMissing)
import System.FilePath hiding (normalise)

import Agda.Compiler.CallCompiler
import Agda.Compiler.Common
import Agda.Compiler.MAlonzo.Coerce
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Compiler.MAlonzo.Primitives
import Agda.Compiler.MAlonzo.HaskellTypes
import Agda.Compiler.MAlonzo.Pragmas
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.Unused
import Agda.Compiler.Treeless.Erase
import Agda.Compiler.Backend

import Agda.Interaction.Imports
import Agda.Interaction.Options

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Names (namesIn)
import qualified Agda.Syntax.Treeless as T
import Agda.Syntax.Literal

import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Primitive (getBuiltinName)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty hiding ((<>))
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings

import Agda.Utils.FileName (isNewerThan)
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Float
import Agda.Utils.IO.Directory
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow, render)
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.String

import Paths_Agda

import Agda.Utils.Impossible

-- The backend callbacks --------------------------------------------------

ghcBackend :: Backend
ghcBackend = Backend ghcBackend'

ghcBackend' :: Backend' GHCFlags GHCCompileEnv GHCModuleEnv GHCModule GHCDefinition
ghcBackend' = Backend'
  { backendName           = "GHC"
  , backendVersion        = Nothing
  , options               = defaultGHCFlags
  , commandLineFlags      = ghcCommandLineFlags
  , isEnabled             = flagGhcCompile
  , preCompile            = ghcPreCompile
  , postCompile           = ghcPostCompile
  , preModule             = ghcPreModule
  , postModule            = ghcPostModule
  , compileDef            = ghcCompileDef
  , scopeCheckingSuffices = False
  , mayEraseType          = ghcMayEraseType
  }

--- Command-line flags ---

data GHCFlags = GHCFlags
  { flagGhcCompile :: Bool
  , flagGhcCallGhc :: Bool
  , flagGhcBin     :: Maybe FilePath
    -- ^ Use the compiler at PATH instead of "ghc"
  , flagGhcFlags   :: [String]
  }

defaultGHCFlags :: GHCFlags
defaultGHCFlags = GHCFlags
  { flagGhcCompile = False
  , flagGhcCallGhc = True
  , flagGhcBin     = Nothing
  , flagGhcFlags   = []
  }

ghcCommandLineFlags :: [OptDescr (Flag GHCFlags)]
ghcCommandLineFlags =
    [ Option ['c']  ["compile", "ghc"] (NoArg enable)
                    "compile program using the GHC backend"
    , Option []     ["ghc-dont-call-ghc"] (NoArg dontCallGHC)
                    "don't call GHC, just write the GHC Haskell files."
    , Option []     ["ghc-flag"] (ReqArg ghcFlag "GHC-FLAG")
                    "give the flag GHC-FLAG to GHC"
    , Option []     ["with-compiler"] (ReqArg withCompilerFlag "PATH")
                    "use the compiler available at PATH"
    ]
  where
    enable      o = pure o{ flagGhcCompile = True }
    dontCallGHC o = pure o{ flagGhcCallGhc = False }
    ghcFlag f   o = pure o{ flagGhcFlags   = flagGhcFlags o ++ [f] }

withCompilerFlag :: FilePath -> Flag GHCFlags
withCompilerFlag fp o = case flagGhcBin o of
 Nothing -> pure o { flagGhcBin = Just fp }
 Just{}  -> throwError "only one compiler path allowed"

--- Context types ---

-- | The options derived from @GHCFlags@ and other shared options.
data GHCOptions = GHCOptions
  { optGhcCallGhc    :: Bool
  , optGhcBin        :: FilePath
    -- ^ Use the compiler at PATH instead of "ghc"
  , optGhcFlags      :: [String]
  , optGhcCompileDir :: FilePath
  }

-- | Monads that can read @GHCOptions@
class Monad m => ReadGHCOpts m where
  askGhcOpts :: m GHCOptions

instance Monad m => ReadGHCOpts (ReaderT GHCOptions m) where
  askGhcOpts = ask

data GHCCompileEnv = GHCCompileEnv
  { ghcCompileEnvOpts :: GHCOptions
  }

instance Monad m => ReadGHCOpts (ReaderT GHCCompileEnv m) where
  askGhcOpts = withReaderT ghcCompileEnvOpts askGhcOpts

-- | Module compilation environment, bundling the overall
--   backend session options along with the module's basic
--   readable properties.
data GHCModuleEnv = GHCModuleEnv
  { ghcModCompileEnv  :: GHCCompileEnv
  , ghcModHsModuleEnv :: HsModuleEnv
  }

instance Monad m => ReadGHCOpts (ReaderT GHCModuleEnv m) where
  askGhcOpts = withReaderT ghcModCompileEnv askGhcOpts

instance Monad m => ReadHsModuleEnv (ReaderT GHCModuleEnv m) where
  askHsModuleEnv = withReaderT ghcModHsModuleEnv askHsModuleEnv

data GHCModule = GHCModule
  { ghcModEnv                :: GHCModuleEnv
  , ghcModMainFuncs :: [MainFunctionDef]
  -- ^ The `main` function definition(s), if both the module is
  --   the @IsMain@ module (root/focused) and a suitable `main`
  --   function was defined.
  }

instance Monad m => ReadGHCOpts (ReaderT GHCModule m) where
  askGhcOpts = withReaderT ghcModEnv askGhcOpts

instance Monad m => ReadHsModuleEnv (ReaderT GHCModule m) where
  askHsModuleEnv = withReaderT ghcModEnv askHsModuleEnv

data GHCDefinition = GHCDefinition
  { ghcDefUsesFloat  :: UsesFloat
  , ghcDefDecls      :: [HS.Decl]
  , ghcDefDefinition :: Definition
  , ghcDefMainDef    :: Maybe MainFunctionDef
  , ghcDefImports    :: Set ModuleName
  }

--- Top-level compilation ---

ghcPreCompile :: GHCFlags -> TCM GHCCompileEnv
ghcPreCompile flags = do
  outDir <- compileDir
  let ghcOpts = GHCOptions
                { optGhcCallGhc    = flagGhcCallGhc flags
                , optGhcBin        = fromMaybe "ghc" (flagGhcBin flags)
                , optGhcFlags      = flagGhcFlags flags
                , optGhcCompileDir = outDir
                }
  return $ GHCCompileEnv ghcOpts

ghcPostCompile :: GHCCompileEnv -> IsMain -> Map ModuleName GHCModule -> TCM ()
ghcPostCompile _cenv _isMain mods = do
  -- FIXME: @curMName@ and @curIF@ are evil TCM state, but there does not appear to be
  --------- another way to retrieve the compilation root ("main" module or interaction focused).
  rootModuleName <- curMName
  rootModule <- ifJust (Map.lookup rootModuleName mods) pure
                $ genericError $ "Module " <> prettyShow rootModuleName <> " was not compiled!"
  flip runReaderT rootModule $ do
    copyRTEModules
    callGHC

--- Module compilation ---

ghcPreModule
  :: GHCCompileEnv
  -> IsMain      -- ^ Are we looking at the main module?
  -> ModuleName
  -> Maybe FilePath    -- ^ Path to the @.agdai@ file.
  -> TCM (Recompile GHCModuleEnv GHCModule)
                 -- ^ Could we confirm the existence of a main function?
ghcPreModule cenv isMain m mifile = ifM uptodate noComp yesComp
    `runReaderT` GHCModuleEnv cenv (HsModuleEnv m (isMain == IsMain))
  where
    uptodate = case mifile of
      Nothing -> pure False
      Just ifile -> liftIO =<< isNewerThan <$> curOutFile <*> pure ifile
    ifileDesc = fromMaybe "(memory)" mifile

    noComp = do
      reportSLn "compile.ghc" 2 . (++ " : no compilation is needed.") . prettyShow . A.mnameToConcrete =<< curMName
      menv <- ask
      mainDefs <- ifM curIsMainModule
                         (mainFunctionDefs <$> curIF)
                         (pure [])
      return . Skip $ GHCModule menv mainDefs

    yesComp = do
      m   <- prettyShow . A.mnameToConcrete <$> curMName
      out <- curOutFile
      reportSLn "compile.ghc" 1 $ repl [m, ifileDesc, out] "Compiling <<0>> in <<1>> to <<2>>"
      asks Recompile

ghcPostModule
  :: GHCCompileEnv
  -> GHCModuleEnv
  -> IsMain        -- ^ Are we looking at the main module?
  -> ModuleName
  -> [GHCDefinition]   -- ^ Compiled module content.
  -> TCM GHCModule
ghcPostModule _cenv menv _isMain _moduleName ghcDefs = do
  builtinThings <- getsTC stBuiltinThings

  -- Accumulate all of the modules, definitions, declarations, etc.
  let (usedFloat, decls, defs, mainDefs, usedModules) = mconcat $
        (\(GHCDefinition useFloat' decls' def' md' imps')
         -> (useFloat', decls', [def'], maybeToList md', imps'))
        <$> ghcDefs

  let imps = mazRTEFloatImport usedFloat ++ imports builtinThings usedModules defs

  i <- curIF

  -- Get content of FOREIGN pragmas.
  let (headerPragmas, hsImps, code) = foreignHaskell i

  flip runReaderT menv $ do
    hsModuleName <- curHsMod
    writeModule $ HS.Module
      hsModuleName
      (map HS.OtherPragma headerPragmas)
      imps
      (map fakeDecl (hsImps ++ code) ++ decls)

  return $ GHCModule menv mainDefs

ghcCompileDef :: GHCCompileEnv -> GHCModuleEnv -> IsMain -> Definition -> TCM GHCDefinition
ghcCompileDef _cenv menv _isMain def = do
  ((usesFloat, decls, mainFuncDef), (HsCompileState imps)) <- definition def `runHsCompileT` ghcModHsModuleEnv menv
  return $ GHCDefinition usesFloat decls def (checkedMainDef <$> mainFuncDef) imps

-- | We do not erase types that have a 'HsData' pragma.
--   This is to ensure a stable interface to third-party code.
ghcMayEraseType :: QName -> TCM Bool
ghcMayEraseType q = getHaskellPragma q <&> \case
  -- Andreas, 2019-05-09, issue #3732.
  -- We restrict this to 'HsData' since types like @Size@, @Level@
  -- should be erased although they have a 'HsType' binding to the
  -- Haskell unit type.
  Just HsData{} -> False
  _ -> True

-- Compilation ------------------------------------------------------------

imports :: BuiltinThings PrimFun -> Set ModuleName -> [Definition] -> [HS.ImportDecl]
imports builtinThings usedModules defs = hsImps ++ imps where
  hsImps :: [HS.ImportDecl]
  hsImps = [unqualRTE, decl mazRTE]

  unqualRTE :: HS.ImportDecl
  unqualRTE = HS.ImportDecl mazRTE False $ Just $
              (False, [ HS.IVar $ HS.Ident x
                      | x <- [mazCoerceName, mazErasedName, mazAnyTypeName] ++
                             map treelessPrimName rtePrims ])

  rtePrims = [T.PAdd, T.PSub, T.PMul, T.PQuot, T.PRem, T.PGeq, T.PLt, T.PEqI,
              T.PAdd64, T.PSub64, T.PMul64, T.PQuot64, T.PRem64, T.PLt64, T.PEq64,
              T.PITo64, T.P64ToI] -- Excludes T.PEqF, which is defined in MAlonzo.RTE.Float

  imps :: [HS.ImportDecl]
  imps = map decl $ uniq $ importsForPrim builtinThings defs ++ map mazMod mnames

  decl :: HS.ModuleName -> HS.ImportDecl
  decl m = HS.ImportDecl m True Nothing

  mnames :: [ModuleName]
  mnames = Set.elems usedModules

  uniq :: [HS.ModuleName] -> [HS.ModuleName]
  uniq = List.map head . List.group . List.sort

-- Should we import MAlonzo.RTE.Float
newtype UsesFloat = UsesFloat Bool deriving (Eq, Show)

pattern YesFloat :: UsesFloat
pattern YesFloat = UsesFloat True

pattern NoFloat :: UsesFloat
pattern NoFloat = UsesFloat False

instance Semigroup UsesFloat where
  UsesFloat a <> UsesFloat b = UsesFloat (a || b)

instance Monoid UsesFloat where
  mempty  = NoFloat
  mappend = (<>)

mazRTEFloatImport :: UsesFloat -> [HS.ImportDecl]
mazRTEFloatImport (UsesFloat b) = [ HS.ImportDecl mazRTEFloat True Nothing | b ]

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

definition :: Definition -> HsCompileM (UsesFloat, [HS.Decl], Maybe CheckedMainFunctionDef)
-- ignore irrelevant definitions
{- Andreas, 2012-10-02: Invariant no longer holds
definition kit (Defn NonStrict _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
-}
definition Defn{defArgInfo = info, defName = q} | not $ usableModality info = do
  reportSDoc "compile.ghc.definition" 10 $
    ("Not compiling" <+> prettyTCM q) <> "."
  return (mempty, mempty, Nothing)
definition def@Defn{defName = q, defType = ty, theDef = d} = do
  reportSDoc "compile.ghc.definition" 10 $ vcat
    [ ("Compiling" <+> prettyTCM q) <> ":"
    , nest 2 $ text (prettyShow d)
    ]
  pragma <- liftTCM $ getHaskellPragma q
  mbool  <- getBuiltinName builtinBool
  mlist  <- getBuiltinName builtinList
  mmaybe <- getBuiltinName builtinMaybe
  minf   <- getBuiltinName builtinInf
  mflat  <- getBuiltinName builtinFlat
  typeCheckedMainDef <- checkTypeOfMain def
  let mainDecl = maybeToList $ checkedMainDecl <$> typeCheckedMainDef
  let retDecls ds = return (mempty, ds)
  (uncurry (,,typeCheckedMainDef)) . second ((mainDecl ++) . infodecl q) <$>
    case d of

      _ | Just (HsDefn r hs) <- pragma -> setCurrentRange r $
          if Just q == mflat
          then genericError
                "\"COMPILE GHC\" pragmas are not allowed for the FLAT builtin."
          else do
            -- Make sure we have imports for all names mentioned in the type.
            hsty <- haskellType q
            mapM_ (`xqual` HS.Ident "_") (namesIn ty :: Set QName)

          -- Check that the function isn't INLINE (since that will make this
          -- definition pointless).
            inline <- (^. funInline) . theDef <$> getConstInfo q
            when inline $ warning $ UselessInline q

            retDecls $ fbWithType hsty (fakeExp hs)

      -- Compiling Bool
      Datatype{} | Just q == mbool -> do
        _ <- sequence_ [primTrue, primFalse] -- Just to get the proper error for missing TRUE/FALSE
        let d = unqhname "d" q
        Just true  <- getBuiltinName builtinTrue
        Just false <- getBuiltinName builtinFalse
        cs <- mapM compiledcondecl [false, true]
        retDecls $ [ compiledTypeSynonym q "Bool" 0
                   , HS.FunBind [HS.Match d [] (HS.UnGuardedRhs HS.unit_con) emptyBinds] ] ++
                   cs

      -- Compiling List
      Datatype{ dataPars = np } | Just q == mlist -> do
        _ <- sequence_ [primNil, primCons] -- Just to get the proper error for missing NIL/CONS
        caseMaybe pragma (return ()) $ \ p -> setCurrentRange p $ warning . GenericWarning =<< do
          fsep $ pwords "Ignoring GHC pragma for builtin lists; they always compile to Haskell lists."
        let d = unqhname "d" q
            t = unqhname "T" q
        Just nil  <- getBuiltinName builtinNil
        Just cons <- getBuiltinName builtinCons
        let vars f n = map (f . ihname "a") [0 .. n - 1]
        cs <- mapM compiledcondecl [nil, cons]
        retDecls $ [ HS.TypeDecl t (vars HS.UnkindedVar (np - 1)) (HS.FakeType "[]")
                   , HS.FunBind [HS.Match d (vars HS.PVar np) (HS.UnGuardedRhs HS.unit_con) emptyBinds] ] ++
                   cs

      -- Compiling Maybe
      Datatype{ dataPars = np } | Just q == mmaybe -> do
        _ <- sequence_ [primNothing, primJust] -- Just to get the proper error for missing NOTHING/JUST
        caseMaybe pragma (return ()) $ \ p -> setCurrentRange p $ warning . GenericWarning =<< do
          fsep $ pwords "Ignoring GHC pragma for builtin maybe; they always compile to Haskell lists."
        let d = unqhname "d" q
            t = unqhname "T" q
        Just nothing <- getBuiltinName builtinNothing
        Just just    <- getBuiltinName builtinJust
        let vars f n = map (f . ihname "a") [0 .. n - 1]
        cs <- mapM compiledcondecl [nothing, just]
        retDecls $ [ HS.TypeDecl t (vars HS.UnkindedVar (np - 1)) (HS.FakeType "Maybe")
                   , HS.FunBind [HS.Match d (vars HS.PVar np) (HS.UnGuardedRhs HS.unit_con) emptyBinds] ] ++
                   cs

      -- Compiling Inf
      _ | Just q == minf -> do
        _ <- primSharp -- To get a proper error for missing SHARP.
        Just sharp <- getBuiltinName builtinSharp
        sharpC     <- compiledcondecl sharp
        let d   = unqhname "d" q
            err = "No term-level implementation of the INFINITY builtin."
        retDecls $ [ compiledTypeSynonym q "MAlonzo.RTE.Infinity" 2
                   , HS.FunBind [HS.Match d [HS.PVar (ihname "a" 0)]
                       (HS.UnGuardedRhs (HS.FakeExp ("error " ++ show err)))
                       emptyBinds]
                   , sharpC
                   ]

      DataOrRecSig{} -> __IMPOSSIBLE__

      Axiom{} -> do
        ar <- liftTCM $ typeArity ty
        retDecls $ [ compiledTypeSynonym q ty ar | Just (HsType r ty) <- [pragma] ] ++
                   fb axiomErr
      Primitive{ primName = s } -> (mempty,) . fb <$> (liftTCM . primBody) s

      PrimitiveSort{ primName = s } -> retDecls []

      Function{} -> function pragma $ functionViaTreeless q

      Datatype{ dataPathCons = _ : _ } -> do
        s <- render <$> prettyTCM q
        typeError $ NotImplemented $
          "Higher inductive types (" ++ s ++ ")"

      Datatype{ dataPars = np, dataIxs = ni, dataClause = cl }
        | Just hsdata@(HsData r ty hsCons) <- pragma -> setCurrentRange r $ do
        reportSDoc "compile.ghc.definition" 40 $ hsep $
          [ "Compiling data type with COMPILE pragma ...", pretty hsdata ]
        liftTCM $ computeErasedConstructorArgs q
        cs <- liftTCM $ getNotErasedConstructors q
        ccscov <- constructorCoverageCode q (np + ni) cs ty hsCons
        cds <- mapM compiledcondecl cs
        let result = concat $
              [ tvaldecl q Inductive (np + ni) [] (Just __IMPOSSIBLE__)
              , [ compiledTypeSynonym q ty np ]
              , cds
              , ccscov
              ]
        retDecls result
      Datatype{ dataPars = np, dataIxs = ni, dataClause = cl } -> do
        liftTCM $ computeErasedConstructorArgs q
        cs <- liftTCM $ getNotErasedConstructors q
        cds <- mapM (flip condecl Inductive) cs
        retDecls $ tvaldecl q Inductive (np + ni) cds cl
      Constructor{} -> retDecls []
      GeneralizableVar{} -> retDecls []
      Record{ recPars = np, recClause = cl, recConHead = con,
              recInduction = ind } ->
        let -- Non-recursive record types are treated as being
            -- inductive.
            inductionKind = fromMaybe Inductive ind
        in case pragma of
          Just (HsData r ty hsCons) -> setCurrentRange r $ do
            let cs = [conName con]
            liftTCM $ computeErasedConstructorArgs q
            ccscov <- constructorCoverageCode q np cs ty hsCons
            cds <- mapM compiledcondecl cs
            retDecls $
              tvaldecl q inductionKind np [] (Just __IMPOSSIBLE__) ++
              [compiledTypeSynonym q ty np] ++ cds ++ ccscov
          _ -> do
            liftTCM $ computeErasedConstructorArgs q
            cd <- condecl (conName con) inductionKind
            retDecls $ tvaldecl q inductionKind (I.arity ty) [cd] cl
      AbstractDefn{} -> __IMPOSSIBLE__
  where
  function :: Maybe HaskellPragma -> HsCompileM (UsesFloat, [HS.Decl]) -> HsCompileM (UsesFloat, [HS.Decl])
  function mhe fun = do
    (imp, defs) <- fun
    let ccls = mkwhere defs
    mflat <- getBuiltinName builtinFlat
    case mhe of
      Just (HsExport r name) -> setCurrentRange r $
        if Just q == mflat
        then genericError
              "\"COMPILE GHC as\" pragmas are not allowed for the FLAT builtin."
        else do
          t <- setCurrentRange r $ haskellType q
          let tsig :: HS.Decl
              tsig = HS.TypeSig [HS.Ident name] t

              def :: HS.Decl
              def = HS.FunBind [HS.Match (HS.Ident name) [] (HS.UnGuardedRhs (hsCoerce $ hsVarUQ $ dname q)) emptyBinds]
          return (imp, [tsig,def] ++ ccls)
      _ -> return (imp, ccls)

  functionViaTreeless :: QName -> HsCompileM (UsesFloat, [HS.Decl])
  functionViaTreeless q = caseMaybeM (liftTCM $ toTreeless LazyEvaluation q) (pure mempty) $ \ treeless -> do

    used <- fromMaybe [] <$> getCompiledArgUse q
    let dostrip = any (== ArgUnused) used

    -- Compute the type approximation
    def <- getConstInfo q
    (argTypes0, resType) <- hsTelApproximation $ defType def
    let pars = case theDef def of
                 Function{ funProjection = Just Projection{ projIndex = i } } | i > 0 -> i - 1
                 _ -> 0
        argTypes  = drop pars argTypes0
        argTypesS = filterUsed used argTypes

    (e, useFloat) <- if dostrip then closedTerm (stripUnusedArguments used treeless)
                                else closedTerm treeless
    let (ps, b) = lamView e
        lamView e =
          case e of
            HS.Lambda ps b -> (ps, b)
            b              -> ([], b)

        tydecl  f ts t = HS.TypeSig [f] (foldr HS.TyFun t ts)
        funbind f ps b = HS.FunBind [HS.Match f ps (HS.UnGuardedRhs b) emptyBinds]
        tyfunbind f ts t ps b =
          let ts' = ts ++ (replicate (length ps - length ts) mazAnyType)
          in [tydecl f ts' t, funbind f ps b]

    -- The definition of the non-stripped function
    (ps0, _) <- lamView <$> closedTerm_ (foldr ($) T.TErased $ replicate (length used) T.TLam)
    let b0 = foldl HS.App (hsVarUQ $ duname q) [ hsVarUQ x | (~(HS.PVar x), ArgUsed) <- zip ps0 used ]

    return (useFloat,
            if dostrip
              then tyfunbind (dname q) argTypes resType ps0 b0 ++
                   tyfunbind (duname q) argTypesS resType ps b
              else tyfunbind (dname q) argTypes resType ps b)

  mkwhere :: [HS.Decl] -> [HS.Decl]
  mkwhere (HS.FunBind [m0, HS.Match dn ps rhs emptyBinds] : fbs@(_:_)) =
          [HS.FunBind [m0, HS.Match dn ps rhs bindsAux]]
    where
    bindsAux :: Maybe HS.Binds
    bindsAux = Just $ HS.BDecls fbs

  mkwhere fbs = fbs

  fbWithType :: HS.Type -> HS.Exp -> [HS.Decl]
  fbWithType ty e =
    HS.TypeSig [unqhname "d" q] ty : fb e

  fb :: HS.Exp -> [HS.Decl]
  fb e  = [HS.FunBind [HS.Match (unqhname "d" q) []
                                (HS.UnGuardedRhs e) emptyBinds]]

  axiomErr :: HS.Exp
  axiomErr = rtmError $ Text.pack $ "postulate evaluated: " ++ prettyShow q

constructorCoverageCode :: QName -> Int -> [QName] -> HaskellType -> [HaskellCode] -> HsCompileM [HS.Decl]
constructorCoverageCode q np cs hsTy hsCons = do
  liftTCM $ checkConstructorCount q cs hsCons
  ifM (liftTCM $ noCheckCover q) (return []) $ do
    ccs <- List.concat <$> zipWithM checkConstructorType cs hsCons
    cov <- liftTCM $ checkCover q hsTy np cs hsCons
    return $ ccs ++ cov

-- | Environment for naming of local variables.
--   Invariant: @reverse ccCxt ++ ccNameSupply@
data CCEnv = CCEnv
  { _ccNameSupply :: NameSupply  -- ^ Supply of fresh names
  , _ccContext    :: CCContext   -- ^ Names currently in scope
  }

type NameSupply = [HS.Name]
type CCContext  = [HS.Name]

ccNameSupply :: Lens' NameSupply CCEnv
ccNameSupply f e =  (\ ns' -> e { _ccNameSupply = ns' }) <$> f (_ccNameSupply e)

ccContext :: Lens' CCContext CCEnv
ccContext f e = (\ cxt -> e { _ccContext = cxt }) <$> f (_ccContext e)

-- | Initial environment for expression generation.
initCCEnv :: CCEnv
initCCEnv = CCEnv
  { _ccNameSupply = map (ihname "v") [0..]  -- DON'T CHANGE THESE NAMES!
  , _ccContext    = []
  }

-- | Term variables are de Bruijn indices.
lookupIndex :: Int -> CCContext -> HS.Name
lookupIndex i xs = fromMaybe __IMPOSSIBLE__ $ xs !!! i

-- | Constructor coverage monad transformer
type CCT m = ReaderT CCEnv (WriterT UsesFloat (HsCompileT m))

-- | Constructor coverage monad
type CC = CCT TCM

liftCC :: Monad m => HsCompileT m a -> CCT m a
liftCC = lift . lift

freshNames :: Monad m => Int -> ([HS.Name] -> CCT m a) -> CCT m a
freshNames n _ | n < 0 = __IMPOSSIBLE__
freshNames n cont = do
  (xs, rest) <- splitAt n <$> view ccNameSupply
  local (over ccNameSupply (const rest)) $ cont xs

-- | Introduce n variables into the context.
intros :: Monad m => Int -> ([HS.Name] -> CCT m a) -> CCT m a
intros n cont = freshNames n $ \xs ->
  local (over ccContext (reverse xs ++)) $ cont xs

checkConstructorType :: QName -> HaskellCode -> HsCompileM [HS.Decl]
checkConstructorType q hs = do
  ty <- haskellType q
  return [ HS.TypeSig [unqhname "check" q] ty
         , HS.FunBind [HS.Match (unqhname "check" q) []
                                (HS.UnGuardedRhs $ fakeExp hs) emptyBinds]
         ]

checkCover :: HasConstInfo m => QName -> HaskellType -> Nat -> [QName] -> [HaskellCode] -> m [HS.Decl]
checkCover q ty n cs hsCons = do
  let tvs = [ "a" ++ show i | i <- [1..n] ]
      makeClause c hsc = do
        a <- erasedArity c
        let pat = HS.PApp (HS.UnQual $ HS.Ident hsc) $ replicate a HS.PWildCard
        return $ HS.Alt pat (HS.UnGuardedRhs $ HS.unit_con) emptyBinds

  cs <- zipWithM makeClause cs hsCons
  let rhs = HS.Case (HS.Var $ HS.UnQual $ HS.Ident "x") cs

  return [ HS.TypeSig [unqhname "cover" q] $ fakeType $ unwords (ty : tvs) ++ " -> ()"
         , HS.FunBind [HS.Match (unqhname "cover" q) [HS.PVar $ HS.Ident "x"]
                                (HS.UnGuardedRhs rhs) emptyBinds]
         ]

closedTerm_ :: T.TTerm -> HsCompileM HS.Exp
closedTerm_ t = fst <$> closedTerm t

closedTerm :: T.TTerm -> HsCompileM (HS.Exp, UsesFloat)
closedTerm v = do
  v <- liftTCM $ addCoercions v
  runWriterT (term v `runReaderT` initCCEnv)

-- Translate case on bool to if
mkIf :: T.TTerm -> CC T.TTerm
mkIf t@(TCase e _ d [TACon c1 0 b1, TACon c2 0 b2]) | T.isUnreachable d = do
  mTrue  <- liftCC $ getBuiltinName builtinTrue
  mFalse <- liftCC $ getBuiltinName builtinFalse
  let isTrue  c = Just c == mTrue
      isFalse c = Just c == mFalse
  if | isTrue c1, isFalse c2 -> return $ T.tIfThenElse (TCoerce $ TVar e) b1 b2
     | isTrue c2, isFalse c1 -> return $ T.tIfThenElse (TCoerce $ TVar e) b2 b1
     | otherwise             -> return t
mkIf t = return t

-- | Extract Agda term to Haskell expression.
--   Erased arguments are extracted as @()@.
--   Types are extracted as @()@.
term :: T.TTerm -> CC HS.Exp
term tm0 = mkIf tm0 >>= \ tm0 -> do
  let ((hasCoerce, t), ts) = coerceAppView tm0
  -- let (t0, ts)       = tAppView tm0
  -- let (hasCoerce, t) = coerceView t0
  let coe            = applyWhen hasCoerce hsCoerce
  case (t, ts) of
    (T.TPrim T.PIf, [c, x, y]) -> coe <$> do HS.If <$> term c <*> term x <*> term y

    (T.TDef f, ts) -> do
      used <- liftCC $ fromMaybe [] <$> getCompiledArgUse f
      -- #2248: no unused argument pruning for COMPILE'd functions
      isCompiled <- liftTCM $ isJust <$> getHaskellPragma f
      let given   = length ts
          needed  = length used
          missing = drop given used
      if not isCompiled && any (== ArgUnused) used
        then if any (== ArgUnused) missing then term (etaExpand (needed - given) tm0) else do
          f <- liftCC $ HS.Var <$> xhqn "du" f  -- use stripped function
          -- Andreas, 2019-11-07, issue #4169.
          -- Insert coercion unconditionally as erasure of arguments
          -- that are matched upon might remove the unfolding of codomain types.
          -- (Hard to explain, see test/Compiler/simple/Issue4169.)
          hsCoerce f `apps` filterUsed used ts
        else do
          f <- liftCC $ HS.Var <$> xhqn "d" f  -- use original (non-stripped) function
          coe f `apps` ts

    (T.TCon c, ts) -> do
      erased  <- liftCC $ getErasedConArgs c
      let missing = drop (length ts) erased
          notErased = not
      if all notErased missing
        then do
                f <- liftCC $ HS.Con <$> conhqn c
                hsCoerce f `apps` [ t | (t, False) <- zip ts erased ]
        else do
                let n = length missing
                unless (n >= 1) __IMPOSSIBLE__  -- We will add at least on TLam, not getting a busy loop here.
                term $ etaExpand (length missing) tm0

    -- Other kind of application: fall back to apps.
    (t, ts) -> noApplication t >>= \ t' -> coe t' `apps` ts
  where
  apps = foldM (\ h a -> HS.App h <$> term a)
  etaExpand n t = mkTLam n $ raise n t `T.mkTApp` map T.TVar (downFrom n)

-- | Translate a non-application, non-coercion, non-constructor, non-definition term.
noApplication :: T.TTerm -> CC HS.Exp
noApplication = \case
  T.TApp{}    -> __IMPOSSIBLE__
  T.TCoerce{} -> __IMPOSSIBLE__
  T.TCon{}    -> __IMPOSSIBLE__
  T.TDef{}    -> __IMPOSSIBLE__

  T.TVar i    -> hsVarUQ . lookupIndex i <$> view ccContext
  T.TLam t    -> intros 1 $ \ [x] -> hsLambda [HS.PVar x] <$> term t

  T.TLet t1 t2 -> do
    t1' <- term t1
    intros 1 $ \[x] -> do
      hsLet x t1' <$> term t2

  T.TCase sc ct def alts -> do
    sc'   <- term $ T.TVar sc
    alts' <- traverse (alt sc) alts
    def'  <- term def
    let defAlt = HS.Alt HS.PWildCard (HS.UnGuardedRhs def') emptyBinds
    return $ HS.Case (hsCoerce sc') (alts' ++ [defAlt])

  T.TLit l    -> literal l
  T.TPrim p   -> return $ compilePrim p
  T.TUnit     -> return $ HS.unit_con
  T.TSort     -> return $ HS.unit_con
  T.TErased   -> return $ hsVarUQ $ HS.Ident mazErasedName
  T.TError e  -> return $ case e of
    T.TUnreachable -> rtmUnreachableError
    T.TMeta s      -> rtmHole s

hsCoerce :: HS.Exp -> HS.Exp
hsCoerce t = HS.App mazCoerce t

compilePrim :: T.TPrim -> HS.Exp
compilePrim s = HS.Var $ hsName $ treelessPrimName s

alt :: Int -> T.TAlt -> CC HS.Alt
alt sc a = do
  case a of
    T.TACon {T.aCon = c} -> do
      intros (T.aArity a) $ \ xs -> do
        erased <- liftCC $ getErasedConArgs c
        nil  <- liftCC $ getBuiltinName builtinNil
        cons <- liftCC $ getBuiltinName builtinCons
        hConNm <-
          if | Just c == nil  -> return $ HS.UnQual $ HS.Ident "[]"
             | Just c == cons -> return $ HS.UnQual $ HS.Symbol ":"
             | otherwise      -> liftCC $ conhqn c
        mkAlt (HS.PApp hConNm $ [HS.PVar x | (x, False) <- zip xs erased])
    T.TAGuard g b -> do
      g <- term g
      b <- term b
      return $ HS.Alt HS.PWildCard
                      (HS.GuardedRhss [HS.GuardedRhs [HS.Qualifier g] b])
                      emptyBinds
    T.TALit { T.aLit = LitQName q } -> mkAlt (litqnamepat q)
    T.TALit { T.aLit = l@LitFloat{}, T.aBody = b } -> do
      tell YesFloat
      l <- literal l
      mkGuarded (treelessPrimName T.PEqF) l b
    T.TALit { T.aLit = LitString s , T.aBody = b } -> mkGuarded "(==)" (litString s) b
    T.TALit {} -> mkAlt (HS.PLit $ hslit $ T.aLit a)
  where
    mkGuarded eq lit b = do
      b  <- term b
      let varName = HS.Ident "l" -- only used locally in the guard
          pv = HS.PVar varName
          v  = hsVarUQ varName
          guard =
            HS.Var (HS.UnQual (HS.Ident eq)) `HS.App`
              v `HS.App` lit
      return $ HS.Alt pv
                      (HS.GuardedRhss [HS.GuardedRhs [HS.Qualifier guard] b])
                      emptyBinds

    mkAlt :: HS.Pat -> CC HS.Alt
    mkAlt pat = do
        body' <- term $ T.aBody a
        return $ HS.Alt pat (HS.UnGuardedRhs body') emptyBinds

literal :: forall m. Monad m => Literal -> CCT m HS.Exp
literal l = case l of
  LitNat    _   -> return $ typed "Integer"
  LitWord64 _   -> return $ typed "MAlonzo.RTE.Word64"
  LitFloat  x   -> floatExp x "Double"
  LitQName  x   -> return $ litqname x
  LitString s   -> return $ litString s
  _             -> return $ l'
  where
    l'    = HS.Lit $ hslit l
    typed = HS.ExpTypeSig l' . HS.TyCon . rtmQual

    -- ASR (2016-09-14): See Issue #2169.
    -- Ulf, 2016-09-28: and #2218.
    floatExp :: Double -> String -> CCT m HS.Exp
    floatExp x s
      | isPosInf  x = rte "positiveInfinity"
      | isNegInf  x = rte "negativeInfinity"
      | isNegZero x = rte "negativeZero"
      | isNaN     x = rte "nan"
      | otherwise   = return $ typed s
      where
        rte s = do tell YesFloat; return $ HS.Var $ HS.Qual mazRTEFloat $ HS.Ident s

hslit :: Literal -> HS.Literal
hslit = \case
  LitNat    x -> HS.Int    x
  LitWord64 x -> HS.Int    (fromIntegral x)
  LitFloat  x -> HS.Frac   (toRational x)
  LitChar   x -> HS.Char   x
  LitQName  x -> __IMPOSSIBLE__
  LitString _ -> __IMPOSSIBLE__
  LitMeta{}   -> __IMPOSSIBLE__

litString :: Text -> HS.Exp
litString s = HS.Ann (HS.Lit (HS.String s))
                     (HS.TyCon (HS.Qual (HS.ModuleName "Data.Text") (HS.Ident "Text")))

litqname :: QName -> HS.Exp
litqname x =
  rteCon "QName" `apps`
  [ hsTypedInt n
  , hsTypedInt m
  , HS.Lit $ HS.String $ Text.pack $ prettyShow x
  , rteCon "Fixity" `apps`
    [ litAssoc (fixityAssoc fx)
    , litPrec  (fixityLevel fx)
    ]
  ]
  where
    apps = foldl HS.App
    rteCon name = HS.Con $ HS.Qual mazRTE $ HS.Ident name
    NameId n m = nameId $ qnameName x
    fx = theFixity $ nameFixity $ qnameName x

    litAssoc NonAssoc   = rteCon "NonAssoc"
    litAssoc LeftAssoc  = rteCon "LeftAssoc"
    litAssoc RightAssoc = rteCon "RightAssoc"

    litPrec Unrelated   = rteCon "Unrelated"
    litPrec (Related l) = rteCon "Related" `HS.App` hsTypedDouble l

litqnamepat :: QName -> HS.Pat
litqnamepat x =
  HS.PApp (HS.Qual mazRTE $ HS.Ident "QName")
          [ HS.PLit (HS.Int $ fromIntegral n)
          , HS.PLit (HS.Int $ fromIntegral m)
          , HS.PWildCard, HS.PWildCard ]
  where
    NameId n m = nameId $ qnameName x

condecl :: QName -> Induction -> HsCompileM HS.ConDecl
condecl q _ind = do
  def <- getConstInfo q
  let Constructor{ conPars = np, conErased = erased } = theDef def
  (argTypes0, _) <- hsTelApproximation (defType def)
  let argTypes   = [ (Just HS.Lazy, t)
                     -- Currently all constructors are lazy.
                   | (t, False) <- zip (drop np argTypes0)
                                       (fromMaybe [] erased ++ repeat False)
                   ]
  return $ HS.ConDecl (unqhname "C" q) argTypes

compiledcondecl :: QName -> HsCompileM HS.Decl
compiledcondecl q = do
  ar <- liftTCM $ erasedArity q
  hsCon <- liftTCM $ fromMaybe __IMPOSSIBLE__ <$> getHaskellConstructor q
  let patVars = map (HS.PVar . ihname "a") [0 .. ar - 1]
  return $ HS.PatSyn (HS.PApp (HS.UnQual $ unqhname "C" q) patVars) (HS.PApp (hsName hsCon) patVars)

compiledTypeSynonym :: QName -> String -> Nat -> HS.Decl
compiledTypeSynonym q hsT arity =
  HS.TypeDecl (unqhname "T" q) (map HS.UnkindedVar vs)
              (foldl HS.TyApp (HS.FakeType hsT) $ map HS.TyVar vs)
  where
    vs = [ ihname "a" i | i <- [0 .. arity - 1]]

tvaldecl :: QName
         -> Induction
            -- ^ Is the type inductive or coinductive?
         -> Nat -> [HS.ConDecl] -> Maybe Clause -> [HS.Decl]
tvaldecl q ind npar cds cl =
  HS.FunBind [HS.Match vn pvs (HS.UnGuardedRhs HS.unit_con) emptyBinds] :
  maybe [HS.DataDecl kind tn [] cds' []]
        (const []) cl
  where
  (tn, vn) = (unqhname "T" q, unqhname "d" q)
  pvs = [ HS.PVar        $ ihname "a" i | i <- [0 .. npar - 1]]

  -- Inductive data types consisting of a single constructor with a
  -- single argument are translated into newtypes.
  (kind, cds') = case (ind, cds) of
    (Inductive, [HS.ConDecl c [(_, t)]]) ->
      (HS.NewType, [HS.ConDecl c [(Nothing, t)]])
      -- The strictness annotations are removed for newtype
      -- constructors.
    _ -> (HS.DataType, cds)

infodecl :: QName -> [HS.Decl] -> [HS.Decl]
infodecl _ [] = []
infodecl q ds =
  fakeD (unqhname "name" q) (haskellStringLiteral $ prettyShow q) : ds

--------------------------------------------------
-- Writing out a haskell module
--------------------------------------------------

type MonadGHCIO m = (MonadIO m, ReadGHCOpts m)

copyRTEModules :: MonadGHCIO m => m ()
copyRTEModules = do
  dataDir <- liftIO getDataDir
  let srcDir = dataDir </> "MAlonzo" </> "src"
  dstDir <- optGhcCompileDir <$> askGhcOpts
  liftIO $ copyDirContent srcDir dstDir

writeModule :: MonadGHCIO m => HS.Module -> m ()
writeModule (HS.Module m ps imp ds) = do
  -- Note that GHC assumes that sources use ASCII or UTF-8.
  out <- snd <$> outFileAndDir m
  liftIO $ UTF8.writeFile out $ (++ "\n") $ prettyPrint $
    HS.Module m (p : ps) imp ds
  where
  p = HS.LanguagePragma $ List.map HS.Ident $
        [ "EmptyDataDecls"
        , "EmptyCase"
        , "ExistentialQuantification"
        , "ScopedTypeVariables"
        , "NoMonomorphismRestriction"
        , "RankNTypes"
        , "PatternSynonyms"
        , "OverloadedStrings"
        ]

outFileAndDir :: MonadGHCIO m => HS.ModuleName -> m (FilePath, FilePath)
outFileAndDir m = do
  mdir <- optGhcCompileDir <$> askGhcOpts
  let (fdir, fn) = splitFileName $ repldot pathSeparator $
                   prettyPrint m
  let dir = mdir </> fdir
      fp  = dir </> replaceExtension fn "hs"
  liftIO $ createDirectoryIfMissing True dir
  return (mdir, fp)
  where
  repldot c = List.map $ \ c' -> if c' == '.' then c else c'

curOutFileAndDir :: (MonadGHCIO m, ReadHsModuleEnv m) => m (FilePath, FilePath)
curOutFileAndDir = outFileAndDir =<< curHsMod

curOutFile :: (MonadGHCIO m, ReadHsModuleEnv m) => m FilePath
curOutFile = snd <$> curOutFileAndDir

callGHC :: ReaderT GHCModule TCM ()
callGHC = do
  opts    <- askGhcOpts
  hsmod   <- prettyPrint <$> curHsMod
  agdaMod <- curAgdaMod
  let outputName = case mnameToList agdaMod of
        [] -> __IMPOSSIBLE__
        ms -> last ms
  (mdir, fp) <- curOutFileAndDir
  let ghcopts = optGhcFlags opts

  modIsMain <- curIsMainModule
  modHasMainFunc <- asks (not . null . ghcModMainFuncs)
  let isMain = modIsMain && modHasMainFunc  -- both need to be IsMain

  -- Warn if no main function and not --no-main
  when (modIsMain /= isMain) $
    genericWarning =<< fsep (pwords "No main function defined in" ++ [prettyTCM agdaMod <> "."] ++
                             pwords "Use --no-main to suppress this warning.")

  let overridableArgs =
        [ "-O"] ++
        (if isMain then ["-o", mdir </> prettyShow (nameConcrete outputName)] else []) ++
        [ "-Werror"]
      otherArgs       =
        [ "-i" ++ mdir] ++
        (if isMain then ["-main-is", hsmod] else []) ++
        [ fp
        , "--make"
        , "-fwarn-incomplete-patterns"
        , "-fno-warn-overlapping-patterns"
        ]
      args     = overridableArgs ++ ghcopts ++ otherArgs

  let ghcBin = optGhcBin opts

  -- Note: Some versions of GHC use stderr for progress reports. For
  -- those versions of GHC we don't print any progress information
  -- unless an error is encountered.
  let doCall = optGhcCallGhc opts
  liftTCM $ callCompiler doCall ghcBin args
