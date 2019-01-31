{-# LANGUAGE CPP #-}

module Agda.Compiler.MAlonzo.Compiler where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ((<>))
#endif

import Control.Monad.Reader hiding (mapM_, forM_, mapM, forM, sequence)
import Control.Monad.State  hiding (mapM_, forM_, mapM, forM, sequence)

import Data.Generics.Geniplate
import Data.Foldable hiding (any, all, foldr, sequence_)
import Data.Function
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable hiding (for)
import Data.Monoid hiding ((<>))

import Numeric.IEEE

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

import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Fixity
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Names (namesIn)
import qualified Agda.Syntax.Treeless as T
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Primitive (getBuiltinName)
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings

import Agda.TypeChecking.CompiledClause

import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.IO.Directory
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow, Pretty)
import qualified Agda.Utils.IO.UTF8 as UTF8
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.String
import Agda.Utils.Tuple

import Paths_Agda

#include "undefined.h"
import Agda.Utils.Impossible

-- The backend callbacks --------------------------------------------------

ghcBackend :: Backend
ghcBackend = Backend ghcBackend'

ghcBackend' :: Backend' GHCOptions GHCOptions GHCModuleEnv IsMain [HS.Decl]
ghcBackend' = Backend'
  { backendName           = "GHC"
  , backendVersion        = Nothing
  , options               = defaultGHCOptions
  , commandLineFlags      = ghcCommandLineFlags
  , isEnabled             = optGhcCompile
  , preCompile            = ghcPreCompile
  , postCompile           = ghcPostCompile
  , preModule             = ghcPreModule
  , postModule            = ghcPostModule
  , compileDef            = ghcCompileDef
  , scopeCheckingSuffices = False
  }

--- Options ---

data GHCOptions = GHCOptions
  { optGhcCompile :: Bool
  , optGhcCallGhc :: Bool
  , optGhcFlags   :: [String]
  }

defaultGHCOptions :: GHCOptions
defaultGHCOptions = GHCOptions
  { optGhcCompile = False
  , optGhcCallGhc = True
  , optGhcFlags   = []
  }

ghcCommandLineFlags :: [OptDescr (Flag GHCOptions)]
ghcCommandLineFlags =
    [ Option ['c']  ["compile", "ghc"] (NoArg enable)
                    "compile program using the GHC backend"
    , Option []     ["ghc-dont-call-ghc"] (NoArg dontCallGHC)
                    "don't call GHC, just write the GHC Haskell files."
    , Option []     ["ghc-flag"] (ReqArg ghcFlag "GHC-FLAG")
                    "give the flag GHC-FLAG to GHC"
    ]
  where
    enable      o = pure o{ optGhcCompile = True }
    dontCallGHC o = pure o{ optGhcCallGhc = False }
    ghcFlag f   o = pure o{ optGhcFlags   = optGhcFlags o ++ [f] }

--- Top-level compilation ---

ghcPreCompile :: GHCOptions -> TCM GHCOptions
ghcPreCompile ghcOpts = do
  allowUnsolved <- optAllowUnsolved <$> pragmaOptions
  when allowUnsolved $ genericError $ "Unsolved meta variables are not allowed when compiling."
  return ghcOpts

ghcPostCompile :: GHCOptions -> IsMain -> Map ModuleName IsMain -> TCM ()
ghcPostCompile opts isMain mods = copyRTEModules >> callGHC opts isMain mods

--- Module compilation ---

-- | This environment is no longer used for anything.

type GHCModuleEnv = ()

ghcPreModule :: GHCOptions -> ModuleName -> FilePath -> TCM (Recompile GHCModuleEnv IsMain)
ghcPreModule _ m ifile = ifM uptodate noComp yesComp
  where
    uptodate = liftIO =<< isNewerThan <$> outFile_ <*> pure ifile

    noComp = do
      reportSLn "compile.ghc" 2 . (++ " : no compilation is needed.") . show . A.mnameToConcrete =<< curMName
      Skip . hasMainFunction <$> curIF

    yesComp = do
      m   <- show . A.mnameToConcrete <$> curMName
      out <- outFile_
      reportSLn "compile.ghc" 1 $ repl [m, ifile, out] "Compiling <<0>> in <<1>> to <<2>>"
      stImportedModules `setTCLens` Set.empty  -- we use stImportedModules to accumulate the required Haskell imports
      return (Recompile ())

ghcPostModule :: GHCOptions -> GHCModuleEnv -> IsMain -> ModuleName -> [[HS.Decl]] -> TCM IsMain
ghcPostModule _ _ _ _ defs = do
  m      <- curHsMod
  imps   <- imports
  -- Get content of FOREIGN pragmas.
  (headerPragmas, hsImps, code) <- foreignHaskell
  writeModule $ HS.Module m
    (map HS.OtherPragma headerPragmas)
    imps
    (map fakeDecl (hsImps ++ code) ++ concat defs)
  hasMainFunction <$> curIF

ghcCompileDef :: GHCOptions -> GHCModuleEnv -> Definition -> TCM [HS.Decl]
ghcCompileDef _ = definition

-- Compilation ------------------------------------------------------------

--------------------------------------------------
-- imported modules
--   I use stImportedModules in a non-standard way,
--   accumulating in it what are acutally used in Misc.xqual
--------------------------------------------------

imports :: TCM [HS.ImportDecl]
imports = (hsImps ++) <$> imps where
  hsImps :: [HS.ImportDecl]
  hsImps = [unqualRTE, decl mazRTE]

  unqualRTE :: HS.ImportDecl
  unqualRTE = HS.ImportDecl mazRTE False $ Just $
              (False, [ HS.IVar $ HS.Ident x
                      | x <- [mazCoerceName, mazErasedName, mazAnyTypeName] ++
                             map treelessPrimName rtePrims ])

  rtePrims = [T.PAdd, T.PSub, T.PMul, T.PQuot, T.PRem, T.PGeq, T.PLt, T.PEqI, T.PEqF,
              T.PAdd64, T.PSub64, T.PMul64, T.PQuot64, T.PRem64, T.PLt64, T.PEq64,
              T.PITo64, T.P64ToI]

  imps :: TCM [HS.ImportDecl]
  imps = List.map decl . uniq <$>
           ((++) <$> importsForPrim <*> (List.map mazMod <$> mnames))

  decl :: HS.ModuleName -> HS.ImportDecl
  decl m = HS.ImportDecl m True Nothing

  mnames :: TCM [ModuleName]
  mnames = Set.elems <$> useTC stImportedModules

  uniq :: [HS.ModuleName] -> [HS.ModuleName]
  uniq = List.map head . List.group . List.sort

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

definition :: GHCModuleEnv -> Definition -> TCM [HS.Decl]
-- ignore irrelevant definitions
{- Andreas, 2012-10-02: Invariant no longer holds
definition kit (Defn NonStrict _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
-}
definition env Defn{defArgInfo = info, defName = q} | not $ usableModality info = do
  reportSDoc "compile.ghc.definition" 10 $
    "Not compiling" <+> prettyTCM q <> "."
  return []
definition env Defn{defName = q, defType = ty, theDef = d} = do
  reportSDoc "compile.ghc.definition" 10 $ vcat
    [ "Compiling" <+> prettyTCM q <> ":"
    , nest 2 $ text (show d)
    ]
  pragma <- getHaskellPragma q
  mbool  <- getBuiltinName builtinBool
  mlist  <- getBuiltinName builtinList
  minf   <- getBuiltinName builtinInf
  mflat  <- getBuiltinName builtinFlat
  checkTypeOfMain q ty $ do
    infodecl q <$> case d of

      _ | Just HsDefn{} <- pragma, Just q == mflat ->
        genericError
          "\"COMPILE GHC\" pragmas are not allowed for the FLAT builtin."

      _ | Just (HsDefn r hs) <- pragma -> setCurrentRange r $ do
        -- Make sure we have imports for all names mentioned in the type.
        hsty <- haskellType q
        ty   <- normalise ty
        sequence_ [ xqual x (HS.Ident "_") | x <- Set.toList (namesIn ty) ]

        -- Check that the function isn't INLINE (since that will make this
        -- definition pointless).
        inline <- (^. funInline) . theDef <$> getConstInfo q
        when inline $ warning $ UselessInline q

        return $ fbWithType hsty (fakeExp hs)

      -- Compiling Bool
      Datatype{} | Just q == mbool -> do
        _ <- sequence_ [primTrue, primFalse] -- Just to get the proper error for missing TRUE/FALSE
        let d = unqhname "d" q
        Just true  <- getBuiltinName builtinTrue
        Just false <- getBuiltinName builtinFalse
        cs <- mapM compiledcondecl [false, true]
        return $ [ compiledTypeSynonym q "Bool" 0
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
        return $ [ HS.TypeDecl t (vars HS.UnkindedVar (np - 1)) (HS.FakeType "[]")
                 , HS.FunBind [HS.Match d (vars HS.PVar np) (HS.UnGuardedRhs HS.unit_con) emptyBinds] ] ++
                 cs

      -- Compiling Inf
      _ | Just q == minf -> do
        _ <- primSharp -- To get a proper error for missing SHARP.
        Just sharp <- getBuiltinName builtinSharp
        sharpC     <- compiledcondecl sharp
        let d   = unqhname "d" q
            err = "No term-level implementation of the INFINITY builtin."
        return $ [ compiledTypeSynonym q "MAlonzo.RTE.Infinity" 2
                 , HS.FunBind [HS.Match d [HS.PVar (ihname "a" 0)]
                     (HS.UnGuardedRhs (HS.FakeExp ("error " ++ show err)))
                     emptyBinds]
                 , sharpC
                 ]

      DataOrRecSig{} -> __IMPOSSIBLE__

      Axiom{} -> do
        ar <- typeArity ty
        return $ [ compiledTypeSynonym q ty ar | Just (HsType r ty) <- [pragma] ] ++
                 fb axiomErr
      Primitive{ primName = s } -> fb <$> primBody s

      Function{} -> function pragma $ functionViaTreeless q

      Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs }
        | Just (HsData r ty hsCons) <- pragma -> setCurrentRange r $ do
        computeErasedConstructorArgs q
        ccscov <- constructorCoverageCode q (np + ni) cs ty hsCons
        cds <- mapM compiledcondecl cs
        return $ tvaldecl q (dataInduction d) (np + ni) [] (Just __IMPOSSIBLE__) ++
                 [compiledTypeSynonym q ty np] ++ cds ++ ccscov
      Datatype{ dataPars = np, dataIxs = ni, dataClause = cl,
                dataCons = cs, dataInduction = ind } -> do
        computeErasedConstructorArgs q
        cds <- mapM (flip condecl ind) cs
        return $ tvaldecl q ind (np + ni) cds cl
      Constructor{} -> return []
      GeneralizableVar{} -> return []
      Record{ recPars = np, recClause = cl, recConHead = con,
              recInduction = ind } ->
        let -- Non-recursive record types are treated as being
            -- inductive.
            inductionKind = fromMaybe Inductive ind
        in case pragma of
          Just (HsData r ty hsCons) -> setCurrentRange r $ do
            let cs = [conName con]
            computeErasedConstructorArgs q
            ccscov <- constructorCoverageCode q np cs ty hsCons
            cds <- mapM compiledcondecl cs
            return $
              tvaldecl q inductionKind np [] (Just __IMPOSSIBLE__) ++
              [compiledTypeSynonym q ty np] ++ cds ++ ccscov
          _ -> do
            computeErasedConstructorArgs q
            cd <- condecl (conName con) inductionKind
            return $ tvaldecl q inductionKind (I.arity ty) [cd] cl
      AbstractDefn{} -> __IMPOSSIBLE__
  where
  function :: Maybe HaskellPragma -> TCM [HS.Decl] -> TCM [HS.Decl]
  function mhe fun = do
    ccls  <- mkwhere <$> fun
    mflat <- getBuiltinName builtinFlat
    case mhe of
      Just HsExport{} | Just q == mflat ->
        genericError
          "\"COMPILE GHC as\" pragmas are not allowed for the FLAT builtin."
      Just (HsExport r name) -> do
        t <- setCurrentRange r $ haskellType q
        let tsig :: HS.Decl
            tsig = HS.TypeSig [HS.Ident name] t

            def :: HS.Decl
            def = HS.FunBind [HS.Match (HS.Ident name) [] (HS.UnGuardedRhs (hsCoerce $ hsVarUQ $ dname q)) emptyBinds]
        return ([tsig,def] ++ ccls)
      _ -> return ccls

  functionViaTreeless :: QName -> TCM [HS.Decl]
  functionViaTreeless q = caseMaybeM (toTreeless LazyEvaluation q) (pure []) $ \ treeless -> do

    used <- getCompiledArgUse q
    let dostrip = any not used

    -- Compute the type approximation
    def <- getConstInfo q
    (argTypes0, resType) <- hsTelApproximation $ defType def
    let pars = case theDef def of
                 Function{ funProjection = Just Projection{ projIndex = i } } | i > 0 -> i - 1
                 _ -> 0
        argTypes  = drop pars argTypes0
        argTypesS = [ t | (t, True) <- zip argTypes (used ++ repeat True) ]

    e <- if dostrip then closedTerm (stripUnusedArguments used treeless)
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
    (ps0, _) <- lamView <$> closedTerm (foldr ($) T.TErased $ replicate (length used) T.TLam)
    let b0 = foldl HS.App (hsVarUQ $ duname q) [ hsVarUQ x | (~(HS.PVar x), True) <- zip ps0 used ]

    return $ if dostrip
      then tyfunbind (dname q) argTypes resType ps0 b0 ++
           tyfunbind (duname q) argTypesS resType ps b
      else tyfunbind (dname q) argTypes resType ps b

  mkwhere :: [HS.Decl] -> [HS.Decl]
  mkwhere (HS.FunBind [m0, HS.Match dn ps rhs emptyBinds] : fbs@(_:_)) =
          [HS.FunBind [m0, HS.Match dn ps rhs bindsAux]]
    where
    bindsAux :: Maybe HS.Binds
    bindsAux = Just $ HS.BDecls fbs

  mkwhere fbs = fbs

  fbWithType :: HS.Type -> HS.Exp -> [HS.Decl]
  fbWithType ty e =
    [ HS.TypeSig [unqhname "d" q] ty ] ++ fb e

  fb :: HS.Exp -> [HS.Decl]
  fb e  = [HS.FunBind [HS.Match (unqhname "d" q) []
                                (HS.UnGuardedRhs $ e) emptyBinds]]

  axiomErr :: HS.Exp
  axiomErr = rtmError $ "postulate evaluated: " ++ prettyShow q

constructorCoverageCode :: QName -> Int -> [QName] -> HaskellType -> [HaskellCode] -> TCM [HS.Decl]
constructorCoverageCode q np cs hsTy hsCons = do
  checkConstructorCount q cs hsCons
  ifM (noCheckCover q) (return []) $ do
    ccs <- List.concat <$> zipWithM checkConstructorType cs hsCons
    cov <- checkCover q hsTy np cs hsCons
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

type CC = ReaderT CCEnv TCM

freshNames :: Int -> ([HS.Name] -> CC a) -> CC a
freshNames n _ | n < 0 = __IMPOSSIBLE__
freshNames n cont = do
  (xs, rest) <- splitAt n <$> view ccNameSupply
  local (over ccNameSupply (const rest)) $ cont xs

-- | Introduce n variables into the context.
intros :: Int -> ([HS.Name] -> CC a) -> CC a
intros n cont = freshNames n $ \xs ->
  local (over ccContext (reverse xs ++)) $ cont xs

checkConstructorType :: QName -> HaskellCode -> TCM [HS.Decl]
checkConstructorType q hs = do
  ty <- haskellType q
  return [ HS.TypeSig [unqhname "check" q] ty
         , HS.FunBind [HS.Match (unqhname "check" q) []
                                (HS.UnGuardedRhs $ fakeExp hs) emptyBinds]
         ]

checkCover :: QName -> HaskellType -> Nat -> [QName] -> [HaskellCode] -> TCM [HS.Decl]
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

closedTerm :: T.TTerm -> TCM HS.Exp
closedTerm v = do
  v <- addCoercions v
  term v `runReaderT` initCCEnv

-- Translate case on bool to if
mkIf :: T.TTerm -> CC T.TTerm
mkIf t@(TCase e _ d [TACon c1 0 b1, TACon c2 0 b2]) | T.isUnreachable d = do
  mTrue  <- lift $ getBuiltinName builtinTrue
  mFalse <- lift $ getBuiltinName builtinFalse
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
term tm0 = mkIf tm0 >>= \ tm0 -> case tm0 of
  T.TVar i -> do
    x <- lookupIndex i <$> view ccContext
    return $ hsVarUQ x
  T.TApp (T.TPrim T.PIf) [c, x, y] -> HS.If <$> term c
                                            <*> term x
                                            <*> term y
  T.TApp t ts | Just (coe, f) <- coerceView t -> do
    used <- lift $ getCompiledArgUse f
    isCompiled <- lift $ isJust <$> getHaskellPragma f  -- #2248: no unused argument pruning for COMPILE'd functions
    let given   = length ts
        needed  = length used
        missing = drop given used
    if not isCompiled && any not used
      then if any not missing then term (etaExpand (needed - given) tm0) else do
        f <- lift $ coe . HS.Var <$> xhqn "du" f  -- used stripped function
        f `apps` [ t | (t, True) <- zip ts $ used ++ repeat True ]
      else do
        t' <- term (T.TDef f)
        coe t' `apps` ts
    where coerceView (T.TCoerce (T.TDef f)) = Just (hsCoerce, f)
          coerceView (T.TDef f)             = Just (id, f)
          coerceView _                      = Nothing
  T.TApp (T.TCon c) ts -> do  -- Note that constructors are never coerced
    (ar, _) <- lift $ conArityAndPars c
    erased  <- lift $ getErasedConArgs c
    let missing = drop (length ts) erased
        notErased = not
    case all notErased missing of
      False -> term $ etaExpand (length missing) tm0
      True  -> do
        f <- lift $ HS.Con <$> conhqn c
        f `apps` [ t | (t, False) <- zip ts erased ]
  T.TApp t ts -> do
    t' <- term t
    t' `apps` ts
  T.TLam at -> do
    (nm:_) <- view ccNameSupply
    intros 1 $ \ [x] ->
      hsLambda [HS.PVar x] <$> term at
  T.TLet t1 t2 -> do
    t1' <- term t1
    intros 1 $ \[x] -> do
      t2' <- term t2
      return $ hsLet x t1' t2'

  T.TCase sc ct def alts -> do
    sc' <- term (T.TVar sc)
    alts' <- traverse (alt sc) alts
    def' <- term def
    let defAlt = HS.Alt HS.PWildCard (HS.UnGuardedRhs def') emptyBinds

    return $ HS.Case (hsCoerce sc') (alts' ++ [defAlt])

  T.TLit l -> return $ literal l
  T.TDef q -> do
    HS.Var <$> (lift $ xhqn "d" q)
  T.TCon q   -> term (T.TApp (T.TCon q) [])
  T.TPrim p  -> return $ compilePrim p
  T.TUnit    -> return HS.unit_con
  T.TSort    -> return HS.unit_con
  T.TCoerce e -> hsCoerce <$> term e
  T.TErased  -> return $ hsVarUQ $ HS.Ident mazErasedName
  T.TError e -> return $ case e of
    T.TUnreachable ->  rtmUnreachableError
  where apps =  foldM (\ h a -> HS.App h <$> term a)
        etaExpand n t =
          foldr (const T.TLam)
                (T.mkTApp (raise n t) [T.TVar i | i <- [n - 1, n - 2..0]])
                (replicate n ())

hsCoerce :: HS.Exp -> HS.Exp
hsCoerce t = HS.App mazCoerce t

compilePrim :: T.TPrim -> HS.Exp
compilePrim s = HS.Var $ hsName $ treelessPrimName s

alt :: Int -> T.TAlt -> CC HS.Alt
alt sc a = do
  case a of
    T.TACon {T.aCon = c} -> do
      intros (T.aArity a) $ \ xs -> do
        erased <- lift $ getErasedConArgs c
        nil  <- lift $ getBuiltinName builtinNil
        cons <- lift $ getBuiltinName builtinCons
        hConNm <-
          if | Just c == nil  -> return $ HS.UnQual $ HS.Ident "[]"
             | Just c == cons -> return $ HS.UnQual $ HS.Symbol ":"
             | otherwise      -> lift $ conhqn c
        mkAlt (HS.PApp hConNm $ map HS.PVar [ x | (x, False) <- zip xs erased ])
    T.TAGuard g b -> do
      g <- term g
      b <- term b
      return $ HS.Alt HS.PWildCard
                      (HS.GuardedRhss [HS.GuardedRhs [HS.Qualifier g] b])
                      emptyBinds
    T.TALit { T.aLit = LitQName _ q } -> mkAlt (litqnamepat q)
    T.TALit { T.aLit = l@LitFloat{},   T.aBody = b } -> mkGuarded (treelessPrimName T.PEqF) (literal l) b
    T.TALit { T.aLit = LitString _ s , T.aBody = b } -> mkGuarded "(==)" (litString s) b
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

literal :: Literal -> HS.Exp
literal l = case l of
  LitNat    _ _   -> typed "Integer"
  LitWord64 _ _   -> typed "MAlonzo.RTE.Word64"
  LitFloat  _ x   -> floatExp x "Double"
  LitQName  _ x   -> litqname x
  LitString _ s   -> litString s
  _               -> l'
  where
    l'    = HS.Lit $ hslit l
    typed = HS.ExpTypeSig l' . HS.TyCon . rtmQual

    -- ASR (2016-09-14): See Issue #2169.
    -- Ulf, 2016-09-28: and #2218.
    floatExp :: Double -> String -> HS.Exp
    floatExp x s
      | isNegativeZero x = rte "negativeZero"
      | isNegativeInf  x = rte "negativeInfinity"
      | isInfinite x     = rte "positiveInfinity"
      | isNegativeNaN x  = rte "negativeNaN"
      | isNaN x          = rte "positiveNaN"
      | otherwise        = typed s

    rte = HS.Var . HS.Qual mazRTE . HS.Ident

    isNegativeInf x = isInfinite x && x < 0.0
    isNegativeNaN x = isNaN x && not (identicalIEEE x (0.0 / 0.0))

hslit :: Literal -> HS.Literal
hslit l = case l of LitNat    _ x -> HS.Int    x
                    LitWord64 _ x -> HS.Int    (fromIntegral x)
                    LitFloat  _ x -> HS.Frac   (toRational x)
                    LitChar   _ x -> HS.Char   x
                    LitQName  _ x -> __IMPOSSIBLE__
                    LitString _ _ -> __IMPOSSIBLE__
                    LitMeta{}     -> __IMPOSSIBLE__

litString :: String -> HS.Exp
litString s =
  HS.Var (HS.Qual (HS.ModuleName "Data.Text") (HS.Ident "pack")) `HS.App`
    (HS.Lit $ HS.String s)

litqname :: QName -> HS.Exp
litqname x =
  rteCon "QName" `apps`
  [ hsTypedInt n
  , hsTypedInt m
  , HS.Lit $ HS.String $ prettyShow x
  , rteCon "Fixity" `apps`
    [ litAssoc (fixityAssoc fx)
    , litPrec  (fixityLevel fx) ] ]
  where
    apps = foldl HS.App
    rteCon name = HS.Con $ HS.Qual mazRTE $ HS.Ident name
    NameId n m = nameId $ qnameName x
    fx = theFixity $ nameFixity $ qnameName x

    litAssoc NonAssoc   = rteCon "NonAssoc"
    litAssoc LeftAssoc  = rteCon "LeftAssoc"
    litAssoc RightAssoc = rteCon "RightAssoc"

    litPrec Unrelated   = rteCon "Unrelated"
    litPrec (Related l) = rteCon "Related" `HS.App` hsTypedInt l

litqnamepat :: QName -> HS.Pat
litqnamepat x =
  HS.PApp (HS.Qual mazRTE $ HS.Ident "QName")
          [ HS.PLit (HS.Int $ fromIntegral n)
          , HS.PLit (HS.Int $ fromIntegral m)
          , HS.PWildCard, HS.PWildCard ]
  where
    NameId n m = nameId $ qnameName x

erasedArity :: QName -> TCM Nat
erasedArity q = do
  (ar, _) <- conArityAndPars q
  erased  <- length . filter id <$> getErasedConArgs q
  return (ar - erased)

condecl :: QName -> Induction -> TCM HS.ConDecl
condecl q _ind = do
  def <- getConstInfo q
  let Constructor{ conPars = np, conErased = erased } = theDef def
  (argTypes0, _) <- hsTelApproximation (defType def)
  let argTypes   = [ (Just HS.Lazy, t)
                     -- Currently all constructors are lazy.
                   | (t, False) <- zip (drop np argTypes0)
                                       (erased ++ repeat False)
                   ]
  return $ HS.ConDecl (unqhname "C" q) argTypes

compiledcondecl :: QName -> TCM HS.Decl
compiledcondecl q = do
  ar <- erasedArity q
  hsCon <- fromMaybe __IMPOSSIBLE__ <$> getHaskellConstructor q
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

copyRTEModules :: TCM ()
copyRTEModules = do
  dataDir <- lift getDataDir
  let srcDir = dataDir </> "MAlonzo" </> "src"
  (lift . copyDirContent srcDir) =<< compileDir

writeModule :: HS.Module -> TCM ()
writeModule (HS.Module m ps imp ds) = do
  -- Note that GHC assumes that sources use ASCII or UTF-8.
  out <- outFile m
  liftIO $ UTF8.writeFile out $ (++ "\n") $ prettyPrint $
    HS.Module m (p : ps) imp ds
  where
  p = HS.LanguagePragma $ List.map HS.Ident $
        [ "EmptyDataDecls"
        , "EmptyCase"
        , "ExistentialQuantification"
        , "ScopedTypeVariables"
        , "NoMonomorphismRestriction"
        , "Rank2Types"
        , "PatternSynonyms"
        ]


outFile' :: Pretty a => a -> TCM (FilePath, FilePath)
outFile' m = do
  mdir <- compileDir
  let (fdir, fn) = splitFileName $ repldot pathSeparator $
                   prettyPrint m
  let dir = mdir </> fdir
      fp  = dir </> replaceExtension fn "hs"
  liftIO $ createDirectoryIfMissing True dir
  return (mdir, fp)
  where
  repldot c = List.map $ \ c' -> if c' == '.' then c else c'

outFile :: HS.ModuleName -> TCM FilePath
outFile m = snd <$> outFile' m

outFile_ :: TCM FilePath
outFile_ = outFile =<< curHsMod

callGHC :: GHCOptions -> IsMain -> Map ModuleName IsMain -> TCM ()
callGHC opts modIsMain mods = do
  mdir    <- compileDir
  hsmod   <- prettyPrint <$> curHsMod
  agdaMod <- curMName
  let outputName = case mnameToList agdaMod of
        [] -> __IMPOSSIBLE__
        ms -> last ms
  (mdir, fp) <- outFile' =<< curHsMod
  let ghcopts = optGhcFlags opts

  let modIsReallyMain = fromMaybe __IMPOSSIBLE__ $ Map.lookup agdaMod mods
      isMain = mappend modIsMain modIsReallyMain  -- both need to be IsMain

  -- Warn if no main function and not --no-main
  when (modIsMain /= isMain) $
    genericWarning =<< fsep (pwords "No main function defined in" ++ [prettyTCM agdaMod <> "."] ++
                             pwords "Use --no-main to suppress this warning.")

  let overridableArgs =
        [ "-O"] ++
        (if isMain == IsMain then ["-o", mdir </> show (nameConcrete outputName)] else []) ++
        [ "-Werror"]
      otherArgs       =
        [ "-i" ++ mdir] ++
        (if isMain == IsMain then ["-main-is", hsmod] else []) ++
        [ fp
        , "--make"
        , "-fwarn-incomplete-patterns"
        , "-fno-warn-overlapping-patterns"
        ]
      args     = overridableArgs ++ ghcopts ++ otherArgs
      compiler = "ghc"

  -- Note: Some versions of GHC use stderr for progress reports. For
  -- those versions of GHC we don't print any progress information
  -- unless an error is encountered.
  let doCall = optGhcCallGhc opts
  callCompiler doCall compiler args
