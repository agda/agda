{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Agda.Compiler.MAlonzo.Compiler where

#if __GLASGOW_HASKELL__ <= 708
import Prelude hiding (foldl, mapM_, mapM, sequence, concat)
#endif

import Control.Applicative
import Control.Monad.Reader hiding (mapM_, forM_, mapM, forM, sequence)
import Control.Monad.State  hiding (mapM_, forM_, mapM, forM, sequence)

import Data.Generics.Geniplate
import Data.Foldable
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable hiding (for)

import qualified Language.Haskell.Exts.Extension as HS
import qualified Language.Haskell.Exts.Parser as HS
import qualified Language.Haskell.Exts.Pretty as HS
import qualified Language.Haskell.Exts.Syntax as HS

import System.Directory (createDirectoryIfMissing)
import System.FilePath hiding (normalise)

import Agda.Compiler.CallCompiler
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Compiler.MAlonzo.Primitives
import Agda.Compiler.ToTreeless

import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Options

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Treeless as T
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Level (reallyUnLevelView)

import Agda.TypeChecking.CompiledClause

import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.IO.UTF8 as UTF8
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Singleton
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

compilerMain :: Bool -> Interface -> TCM ()
compilerMain modIsMain mainI =
  -- Preserve the state (the compiler modifies the state).
  -- Andreas, 2014-03-23 But we might want to collect Benchmark info,
  -- so use localTCState.
  localTCState $ do

    -- Compute the output directory.
    opts <- commandLineOptions
    compileDir <- case optCompileDir opts of
      Just dir -> return dir
      Nothing  -> do
        -- The default output directory is the project root.
        let tm = toTopLevelModuleName $ iModuleName mainI
        f <- findFile tm
        return $ filePath $ C.projectRoot f tm
    setCommandLineOptions $
      opts { optCompileDir = Just compileDir }

    ignoreAbstractMode $ do
      mapM_ (compile . miInterface) =<< (Map.elems <$> getVisitedModules)
      writeModule rteModule
      callGHC modIsMain mainI

compile :: Interface -> TCM ()
compile i = do
  setInterface i
  ifM uptodate noComp $ {- else -} do
    yesComp
    writeModule =<< decl <$> curHsMod <*> (definitions =<< curDefs) <*> imports
  where
  decl mn ds imp = HS.Module dummy mn [] Nothing Nothing imp ds
  uptodate = liftIO =<< (isNewerThan <$> outFile_ <*> ifile)
  ifile    = maybe __IMPOSSIBLE__ filePath <$>
               (findInterfaceFile . toTopLevelModuleName =<< curMName)
  noComp   = reportSLn "" 1 . (++ " : no compilation is needed.") . show . A.mnameToConcrete =<< curMName
  yesComp  = reportSLn "" 1 . (`repl` "Compiling <<0>> in <<1>> to <<2>>") =<<
             sequence [show . A.mnameToConcrete <$> curMName, ifile, outFile_] :: TCM ()

--------------------------------------------------
-- imported modules
--   I use stImportedModules in a non-standard way,
--   accumulating in it what are acutally used in Misc.xqual
--------------------------------------------------

imports :: TCM [HS.ImportDecl]
imports = (++) <$> hsImps <*> imps where
  hsImps :: TCM [HS.ImportDecl]
  hsImps = (List.map decl . Set.toList .
            Set.insert mazRTE . Set.map HS.ModuleName) <$>
             getHaskellImports

  imps :: TCM [HS.ImportDecl]
  imps = List.map decl . uniq <$>
           ((++) <$> importsForPrim <*> (List.map mazMod <$> mnames))

  decl :: HS.ModuleName -> HS.ImportDecl
  decl m = HS.ImportDecl dummy m True False False Nothing Nothing Nothing

  mnames :: TCM [ModuleName]
  mnames = (++) <$> (Set.elems <$> use stImportedModules)
                <*> (List.map fst . iImportedModules <$> curIF)

  uniq :: [HS.ModuleName] -> [HS.ModuleName]
  uniq = List.map head . List.group . List.sort

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

definitions :: Definitions -> TCM [HS.Decl]
definitions defs = do
  kit <- coinductionKit
  HMap.foldr (liftM2 (++) . (definition kit <=< instantiateFull))
             declsForPrim defs

-- | Note that the INFINITY, SHARP and FLAT builtins are translated as
-- follows (if a 'CoinductionKit' is given):
--
-- @
--   type Infinity a b = b
--
--   sharp :: a -> a
--   sharp x = x
--
--   flat :: a -> a
--   flat x = x
-- @

definition :: Maybe CoinductionKit -> Definition -> TCM [HS.Decl]
-- ignore irrelevant definitions
{- Andreas, 2012-10-02: Invariant no longer holds
definition kit (Defn Forced{}  _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
definition kit (Defn UnusedArg _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
definition kit (Defn NonStrict _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
-}
definition kit Defn{defArgInfo = info, defName = q} | isIrrelevant info = do
  reportSDoc "malonzo.definition" 10 $
    text "Not compiling" <+> prettyTCM q <> text "."
  return []
definition kit Defn{defName = q, defType = ty, defCompiledRep = compiled, theDef = d} = do
  reportSDoc "malonzo.definition" 10 $ vcat
    [ text "Compiling" <+> prettyTCM q <> text ":"
    , nest 2 $ text (show d)
    ]
  checkTypeOfMain q ty $ do
    (infodecl q :) <$> case d of

      _ | Just (HsDefn ty hs) <- compiledHaskell compiled ->
        return $ fbWithType ty (fakeExp hs)

      -- Special treatment of coinductive builtins.
      Datatype{} | Just q == (nameOfInf <$> kit) -> do
        let infT = unqhname "T" q
            infV = unqhname "d" q
            a    = ihname "a" 0
            b    = ihname "a" 1
            vars = [a, b]
        return [ HS.TypeDecl dummy infT
                             (List.map HS.UnkindedVar vars)
                             (HS.TyVar b)
               , HS.FunBind [HS.Match dummy infV
                                      (List.map HS.PVar vars) Nothing
                                      (HS.UnGuardedRhs HS.unit_con)
                                      (HS.BDecls [])]
               ]
      Constructor{} | Just q == (nameOfSharp <$> kit) -> do
        let sharp = unqhname "d" q
            x     = ihname "x" 0
        return $
          [ HS.TypeSig dummy [sharp] $ fakeType $
              "forall a. a -> a"
          , HS.FunBind [HS.Match dummy sharp
                                 [HS.PVar x]
                                 Nothing
                                 (HS.UnGuardedRhs (HS.Var (HS.UnQual x)))
                                 (HS.BDecls [])]
          ]
      Function{} | Just q == (nameOfFlat <$> kit) -> do
        let flat = unqhname "d" q
            x    = ihname "x" 0
        return $
          [ HS.TypeSig dummy [flat] $ fakeType $
              "forall a. a -> a"
          , HS.FunBind [HS.Match dummy flat
                                 [HS.PVar x]
                                 Nothing
                                 (HS.UnGuardedRhs (HS.Var (HS.UnQual x)))
                                 (HS.BDecls [])]
          ]

      Axiom{} -> return $ fb axiomErr
      Primitive{ primCompiled = Nothing, primName = s } -> fb <$> primBody s
      Primitive{ primCompiled = Just cc } -> function Nothing $
        functionViaTreeless q cc

      Function{ funCompiled = Just cc } ->
        function (exportHaskell compiled) $ functionViaTreeless q cc
      Function { funCompiled = Nothing } -> __IMPOSSIBLE__

      Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs }
        | Just (HsType ty) <- compiledHaskell compiled -> do
        ccs <- List.concat <$> mapM checkConstructorType cs
        cov <- checkCover q ty np cs
        return $ tvaldecl q (dataInduction d) 0 (np + ni) [] (Just __IMPOSSIBLE__) ++ ccs ++ cov
      Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs } -> do
        (ars, cds) <- unzip <$> mapM condecl cs
        return $ tvaldecl q (dataInduction d) (List.maximum (np:ars) - np) (np + ni) cds cl
      Constructor{} -> return []
      Record{ recClause = cl, recConHead = con, recFields = flds } -> do
        let c = conName con
        let noFields = length flds
        let ar = I.arity ty
        cd <- snd <$> condecl c
  --       cd <- case c of
  --         Nothing -> return $ cdecl q noFields
  --         Just c  -> snd <$> condecl c
        return $ tvaldecl q Inductive noFields ar [cd] cl
  where
  function :: Maybe HaskellExport -> TCM [HS.Decl] -> TCM [HS.Decl]
  function mhe fun = do
    ccls <- mkwhere <$> fun
    case mhe of
      Nothing -> return ccls
      Just (HsExport t name) -> do
        let tsig :: HS.Decl
            tsig = HS.TypeSig dummy [HS.Ident name] (fakeType t)

            def :: HS.Decl
            def = HS.FunBind [HS.Match dummy (HS.Ident name) [] Nothing (HS.UnGuardedRhs (hsVarUQ $ dsubname q 0)) (HS.BDecls [])]
        return ([tsig,def] ++ ccls)

  functionViaTreeless :: QName -> CompiledClauses -> TCM [HS.Decl]
  functionViaTreeless q cc = do
    treeless <- ccToTreeless q cc
    e <- closedTerm treeless
    return $ [HS.FunBind [HS.Match dummy (dsubname q 0) [] Nothing (HS.UnGuardedRhs e) (HS.BDecls [])]]

  mkwhere :: [HS.Decl] -> [HS.Decl]
  mkwhere (HS.FunBind [m0, HS.Match _     dn ps mt rhs (HS.BDecls [])] :
           fbs@(_:_)) =
          [HS.FunBind [m0, HS.Match dummy dn ps mt rhs (HS.BDecls fbs)]]
  mkwhere fbs = fbs

  fbWithType :: HaskellType -> HS.Exp -> [HS.Decl]
  fbWithType ty e =
    [ HS.TypeSig dummy [unqhname "d" q] $ fakeType ty ] ++ fb e

  fb :: HS.Exp -> [HS.Decl]
  fb e  = [HS.FunBind [HS.Match dummy (unqhname "d" q) [] Nothing
                                (HS.UnGuardedRhs $ e) (HS.BDecls [])]]

  axiomErr :: HS.Exp
  axiomErr = rtmError $ "postulate evaluated: " ++ show (A.qnameToConcrete q)

-- | Environment for naming of local variables.
--   Invariant: @reverse ccCxt ++ ccNameSupply@
data CCEnv = CCEnv
  { ccNameSupply :: NameSupply  -- ^ Supply of fresh names
  , ccCxt        :: CCContext   -- ^ Names currently in scope
  }

type NameSupply = [HS.Name]
type CCContext  = [HS.Name]

mapNameSupply :: (NameSupply -> NameSupply) -> CCEnv -> CCEnv
mapNameSupply f e = e { ccNameSupply = f (ccNameSupply e) }

mapContext :: (CCContext -> CCContext) -> CCEnv -> CCEnv
mapContext f e = e { ccCxt = f (ccCxt e) }

-- | Initial environment for expression generation.
initCCEnv :: CCEnv
initCCEnv = CCEnv
  { ccNameSupply = map (ihname "v") [0..]  -- DON'T CHANGE THESE NAMES!
  , ccCxt        = []
  }

-- | Term variables are de Bruijn indices.
lookupIndex :: Int -> CCContext -> HS.Name
lookupIndex i xs = fromMaybe __IMPOSSIBLE__ $ xs !!! i

type CC = ReaderT CCEnv TCM

-- | Introduce n variables into the context.
intros :: Int -> ([HS.Name] -> CC a) -> CC a
intros n cont = do
  if n < 0 then __IMPOSSIBLE__ else do
    (xs, rest) <- splitAt n <$> asks ccNameSupply
    local (mapNameSupply (const rest) . mapContext (reverse xs ++)) $
      cont xs

checkConstructorType :: QName -> TCM [HS.Decl]
checkConstructorType q = do
  Just (HsDefn ty hs) <- compiledHaskell . defCompiledRep <$> getConstInfo q
  return [ HS.TypeSig dummy [unqhname "check" q] $ fakeType ty
         , HS.FunBind [HS.Match dummy (unqhname "check" q) [] Nothing
                                (HS.UnGuardedRhs $ fakeExp hs) (HS.BDecls [])]
         ]

checkCover :: QName -> HaskellType -> Nat -> [QName] -> TCM [HS.Decl]
checkCover q ty n cs = do
  let tvs = [ "a" ++ show i | i <- [1..n] ]
      makeClause c = do
        (a, _) <- conArityAndPars c
        Just (HsDefn _ hsc) <- compiledHaskell . defCompiledRep <$> getConstInfo c
        let pat = HS.PApp (HS.UnQual $ HS.Ident hsc) $ replicate a HS.PWildCard
        return $ HS.Alt dummy pat (HS.UnGuardedRhs $ HS.unit_con) (HS.BDecls [])

  cs <- mapM makeClause cs
  let rhs = case cs of
              [] -> fakeExp "()" -- There is no empty case statement in Haskell
              _  -> HS.Case (HS.Var $ HS.UnQual $ HS.Ident "x") cs

  return [ HS.TypeSig dummy [unqhname "cover" q] $ fakeType $ unwords (ty : tvs) ++ " -> ()"
         , HS.FunBind [HS.Match dummy (unqhname "cover" q) [HS.PVar $ HS.Ident "x"]
                                Nothing (HS.UnGuardedRhs rhs) (HS.BDecls [])]
         ]

-- | Move somewhere else!
conArityAndPars :: QName -> TCM (Nat, Nat)
conArityAndPars q = do
  def <- getConstInfo q
  TelV tel _ <- telView $ defType def
  let Constructor{ conPars = np } = theDef def
      n = length (telToList tel)
  return (n - np, np)


closedTerm :: T.TTerm -> TCM HS.Exp
closedTerm v = hsCast <$> term v `runReaderT` initCCEnv

-- | Extract Agda term to Haskell expression.
--   Erased arguments are extracted as @()@.
--   Types are extracted as @()@.
term :: T.TTerm -> CC HS.Exp
term tm0 = case tm0 of
  T.TVar i -> do
    x <- lookupIndex i <$> asks ccCxt
    return $ hsVarUQ x
  T.TApp t ts -> do
    t' <- term t
    t' `apps` ts
  T.TLam at -> do
    (nm:_) <- asks ccNameSupply
    intros 1 $ \ [x] ->
      hsLambda [HS.PVar x] <$> term at
  T.TLet t1 t2 -> do
    t1' <- term t1
    intros 1 $ \[x] -> do
      t2' <- term t2
      return $ HS.Let (HS.BDecls [HS.FunBind [HS.Match dummy x []
                Nothing (HS.UnGuardedRhs t1') (HS.BDecls [])]]) t2'
  T.TCase sc ct def alts -> do
    sc' <- term sc
    alts' <- traverse alt alts
    def' <- term def
    let defAlt = HS.Alt dummy HS.PWildCard (HS.UnGuardedRhs def') (HS.BDecls [])

    return $ HS.Case (hsCast sc') (alts' ++ [defAlt])

  T.TLit l -> lift $ literal l
  T.TDef q -> do
    HS.Var <$> (lift $ xhqn "d" q)
  T.TCon q -> do
    kit <- lift coinductionKit
    if Just q == (nameOfSharp <$> kit)
      then HS.Var <$> lift (xhqn "d" q)
      else HS.Con <$> lift (conhqn q)
  T.TPi _ _  -> return HS.unit_con
  T.TUnit    -> return HS.unit_con
  T.TSort    -> return HS.unit_con
  T.TErased  -> return HS.unit_con
  T.TError e -> return $ case e of
    T.TPatternMatchFailure funNm ->  rtmIncompleteMatch funNm
  where apps =  foldM (\ h a -> HS.App h <$> term a)

alt :: T.TAlt -> CC HS.Alt
alt a = do
  case a of
    (T.TACon {}) -> do
      intros (T.aArity a) $ \xs -> do
        hConNm <- lift $ conhqn $ T.aCon a
        mkAlt (HS.PApp hConNm $ map HS.PVar xs)
    (T.TALit { T.aLit = (LitQName _ q) }) -> mkAlt (litqnamepat q)
    (T.TALit {}) -> mkAlt (HS.PLit HS.Signless $ hslit $ T.aLit a)
  where
    mkAlt :: HS.Pat -> CC HS.Alt
    mkAlt pat = do
        body' <- term $ T.aBody a
        return $ HS.Alt dummy pat (HS.UnGuardedRhs $ hsCast body') (HS.BDecls [])

literal :: Literal -> TCM HS.Exp
literal l = case l of
  LitInt    _ _   -> do toN <- bltQual "NATURAL" mazIntegerToNat
                        return $ HS.Var toN `HS.App` typed "Integer"
  LitFloat  _ _   -> return $ typed "Double"
  LitQName  _ x   -> return $ litqname x
  _               -> return $ l'
  where l'    = HS.Lit $ hslit l
        typed = HS.ExpTypeSig dummy l' . HS.TyCon . rtmQual

hslit :: Literal -> HS.Literal
hslit l = case l of LitInt    _ x -> HS.Int    x
                    LitFloat  _ x -> HS.Frac   (toRational x)
                    LitString _ x -> HS.String x
                    LitChar   _ x -> HS.Char   x
                    LitQName  _ x -> __IMPOSSIBLE__

litqname :: QName -> HS.Exp
litqname x =
  HS.Con (HS.Qual mazRTE $ HS.Ident "QName") `HS.App`
  HS.Lit (HS.Int n) `HS.App`
  HS.Lit (HS.Int m) `HS.App`
  (rtmError "primQNameType: not implemented") `HS.App`
  (rtmError "primQNameDefinition: not implemented") `HS.App`
  HS.Lit (HS.String $ show x )
  where
    NameId n m = nameId $ qnameName x

litqnamepat :: QName -> HS.Pat
litqnamepat x =
  HS.PApp (HS.Qual mazRTE $ HS.Ident "QName")
          [ HS.PLit HS.Signless (HS.Int n)
          , HS.PLit HS.Signless (HS.Int m)
          , HS.PWildCard
          , HS.PWildCard
          , HS.PWildCard]
  where
    NameId n m = nameId $ qnameName x

condecl :: QName -> TCM (Nat, HS.ConDecl)
condecl q = do
  (ar, np) <- conArityAndPars q
  return $ (ar + np, cdecl q ar)

cdecl :: QName -> Nat -> HS.ConDecl
cdecl q n = HS.ConDecl (unqhname "C" q)
            [ HS.TyVar $ ihname "a" i | i <- [0 .. n - 1] ]

tvaldecl :: QName
         -> Induction
            -- ^ Is the type inductive or coinductive?
         -> Nat -> Nat -> [HS.ConDecl] -> Maybe Clause -> [HS.Decl]
tvaldecl q ind ntv npar cds cl =
  HS.FunBind [HS.Match dummy vn pvs Nothing
                       (HS.UnGuardedRhs HS.unit_con) (HS.BDecls [])] :
  maybe [HS.DataDecl dummy kind [] tn tvs
                     (List.map (HS.QualConDecl dummy [] []) cds) []]
        (const []) cl
  where
  (tn, vn) = (unqhname "T" q, unqhname "d" q)
  tvs = [ HS.UnkindedVar $ ihname "a" i | i <- [0 .. ntv  - 1]]
  pvs = [ HS.PVar        $ ihname "a" i | i <- [0 .. npar - 1]]

  -- Inductive data types consisting of a single constructor with a
  -- single argument are translated into newtypes.
  kind = case (ind, cds) of
    (Inductive, [HS.ConDecl _ [_]]) -> HS.NewType
    (Inductive, [HS.RecDecl _ [_]]) -> HS.NewType
    _                               -> HS.DataType

infodecl :: QName -> HS.Decl
infodecl q = fakeD (unqhname "name" q) $ show $ prettyShow q

--------------------------------------------------
-- Inserting unsafeCoerce
--------------------------------------------------

hsCast :: HS.Exp -> HS.Exp
{-
hsCast = addcast . go where
  addcast [e@(HS.Var(HS.UnQual(HS.Ident(c:ns))))] | c == 'v' && all isDigit ns = e
  addcast es = foldl HS.App mazCoerce es
  -- this need to be extended if you generate other kinds of exps.
  go (HS.App e1 e2    ) = go e1 ++ [hsCast e2]
  go (HS.Lambda _ ps e) = [ HS.Lambda dummy ps (hsCast e) ]
  go e = [e]
-}

hsCast e = hsCoerce (hsCast' e)

hsCast' :: HS.Exp -> HS.Exp
hsCast' (HS.App e1 e2)     = hsCast' e1 `HS.App` hsCastApp e2
hsCast' (HS.Lambda _ ps e) = HS.Lambda dummy ps $ hsCast' e
hsCast' e = hsCoerce e

-- We still have to coerce function applications in arguments to coerced
-- functions.
hsCastApp :: HS.Exp -> HS.Exp
hsCastApp (HS.Lambda i ps b) = HS.Lambda i ps (hsCastApp b)
hsCastApp (HS.Case sc bs) = HS.Case (hsCastApp sc) (map (hsMapAlt hsCastApp) bs)
hsCastApp e =
  case hsAppView e of
    f : es@(_:_) -> foldl HS.App (hsCoerce f) $ map hsCastApp es
    _ -> e

-- No coercion for literal integers
hsCoerce :: HS.Exp -> HS.Exp
hsCoerce e@(HS.ExpTypeSig _ (HS.Lit (HS.Int{})) _) = e
hsCoerce (HS.Case sc alts) = HS.Case sc (map (hsMapAlt hsCoerce) alts)
hsCoerce e =
  case hsAppView e of
    c : _ | c == mazCoerce || c == mazIncompleteMatch -> e
    _ -> mazCoerce `HS.App` e

--------------------------------------------------
-- Writing out a haskell module
--------------------------------------------------

writeModule :: HS.Module -> TCM ()
writeModule (HS.Module l m ps w ex imp ds) = do
  -- Note that GHC assumes that sources use ASCII or UTF-8.
  out <- outFile m
  liftIO $ UTF8.writeFile out $ prettyPrint $
    HS.Module l m (p : ps) w ex imp ds
  where
  p = HS.LanguagePragma dummy $ List.map HS.Ident $
        [ "EmptyDataDecls"
        , "ExistentialQuantification"
        , "ScopedTypeVariables"
        , "NoMonomorphismRestriction"
        , "Rank2Types"
        ]

rteModule :: HS.Module
rteModule = ok $ parse $ unlines
  [ "module " ++ prettyPrint mazRTE ++ " where"
  , "import Unsafe.Coerce"
  , ""
  , "-- Special version of coerce that plays well with rules."
  , "{-# INLINE [1] mazCoerce #-}"
  , "mazCoerce = Unsafe.Coerce.unsafeCoerce"
  , "{-# RULES \"coerce-id\" forall (x :: a) . mazCoerce x = x #-}"
  , ""
  , "-- Builtin QNames, the third field is for the type."
  , "data QName a b = QName { nameId, moduleId :: Integer, qnameType :: a, qnameDefinition :: b, qnameString :: String}"
  , "instance Eq (QName a b) where"
  , "  QName a b _ _ _ == QName c d _ _ _ = (a, b) == (c, d)"
  , "instance Ord (QName a b) where"
  , "  compare (QName a b _ _ _) (QName c d _ _ _) = compare (a, b) (c, d)"
  , ""
  , "mazIncompleteMatch :: String -> a"
  , "mazIncompleteMatch s = error (\"MAlonzo Runtime Error: incomplete pattern matching: \" ++ s)"
  ]
  where
    parse :: String -> HS.ParseResult HS.Module
    parse = HS.parseModuleWithMode
              HS.defaultParseMode
                { HS.extensions = [ HS.EnableExtension HS.ExplicitForAll ] }

    ok :: HS.ParseResult HS.Module -> HS.Module
    ok (HS.ParseOk d)   = d
    ok HS.ParseFailed{} = __IMPOSSIBLE__

compileDir :: TCM FilePath
compileDir = do
  mdir <- optCompileDir <$> commandLineOptions
  case mdir of
    Just dir -> return dir
    Nothing  -> __IMPOSSIBLE__

outFile' :: (HS.Pretty a, TransformBi HS.ModuleName (Wrap a)) =>
            a -> TCM (FilePath, FilePath)
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

callGHC :: Bool -> Interface -> TCM ()
callGHC modIsMain i = do
  setInterface i
  mdir          <- compileDir
  hsmod         <- prettyPrint <$> curHsMod
  MName agdaMod <- curMName
  let outputName = case agdaMod of
        [] -> __IMPOSSIBLE__
        ms -> last ms
  (mdir, fp) <- outFile' =<< curHsMod
  opts       <- optGhcFlags <$> commandLineOptions

  let overridableArgs =
        [ "-O"] ++
        (if modIsMain then ["-o", mdir </> show (nameConcrete outputName)] else []) ++
        [ "-Werror"]
      otherArgs       =
        [ "-i" ++ mdir] ++
        (if modIsMain then ["-main-is", hsmod] else []) ++
        [ fp
        , "--make"
        , "-fwarn-incomplete-patterns"
        , "-fno-warn-overlapping-patterns"
        ]
      args     = overridableArgs ++ opts ++ otherArgs
      compiler = "ghc"

  -- Note: Some versions of GHC use stderr for progress reports. For
  -- those versions of GHC we don't print any progress information
  -- unless an error is encountered.
  callCompiler compiler args
