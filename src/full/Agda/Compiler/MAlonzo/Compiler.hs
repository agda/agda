{-# LANGUAGE CPP, PatternGuards #-}

module Agda.Compiler.MAlonzo.Compiler where

import Control.Applicative
import Control.Monad ((<=<))
import Control.Monad.Reader
import Control.Monad.State
import Data.Char
import Data.List as L
import Data.Map as M
import Data.Set as S
import qualified Language.Haskell.Exts.Extension as HS
import qualified Language.Haskell.Exts.Parser as HS
import qualified Language.Haskell.Exts.Syntax as HS
import System.Cmd
import System.Directory (createDirectoryIfMissing)
import System.FilePath hiding (normalise)

import Agda.Compiler.CallCompiler
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Compiler.MAlonzo.Primitives
import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Options
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Reduce
-- import Agda.TypeChecking.Rules.Builtin.Coinduction
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.Utils.FileName
import Agda.Utils.Monad
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.Impossible
import qualified Agda.Utils.HashMap as HMap

#include "../../undefined.h"

compilerMain :: Interface -> TCM ()
compilerMain mainI =
  -- Preserve the state (the compiler modifies the state).
  localState $ do

    -- Compute the output directory.
    opts <- commandLineOptions
    compileDir <- case optCompileDir opts of
      Just dir -> return dir
      Nothing  -> do
        -- The default output directory is the project root.
        let tm = toTopLevelModuleName $ iModuleName mainI
        f <- findFile tm
        return $ filePath $ CN.projectRoot f tm
    setCommandLineOptions $
      opts { optCompileDir = Just compileDir }

    ignoreAbstractMode $ do
      mapM_ (compile . miInterface) =<< (M.elems <$> getVisitedModules)
      writeModule rteModule
      callGHC mainI

compile :: Interface -> TCM ()
compile i = do
  setInterface i
  ifM uptodate noComp $ (yesComp >>) $ do
    writeModule =<< decl <$> curHsMod <*> (definitions =<< curDefs) <*> imports
  where
  decl mn ds imp = HS.Module dummy mn [] Nothing Nothing imp ds
  uptodate = liftIO =<< (isNewerThan <$> outFile_ <*> ifile)
  ifile    = maybe __IMPOSSIBLE__ filePath <$>
               (findInterfaceFile . toTopLevelModuleName =<< curMName)
  noComp   = reportSLn "" 1 . (++ " : no compilation is needed.").show =<< curMName
  yesComp  = reportSLn "" 1 . (`repl` "Compiling <<0>> in <<1>> to <<2>>") =<<
             sequence [show <$> curMName, ifile, outFile_] :: TCM ()

--------------------------------------------------
-- imported modules
--   I use stImportedModules in a non-standard way,
--   accumulating in it what are acutally used in Misc.xqual
--------------------------------------------------

imports :: TCM [HS.ImportDecl]
imports = (++) <$> hsImps <*> imps where
  hsImps = (L.map decl . S.toList .
            S.insert mazRTE . S.map HS.ModuleName) <$>
             getHaskellImports
  imps   = L.map decl . uniq <$>
             ((++) <$> importsForPrim <*> (L.map mazMod <$> mnames))
  decl m = HS.ImportDecl dummy m True False Nothing Nothing Nothing
  mnames = (++) <$> (S.elems <$> gets stImportedModules)
                <*> (iImportedModules <$> curIF)
  uniq   = L.map head . group . L.sort

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
definition kit (Defn Forced     _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
definition kit (Defn UnusedArg  _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
definition kit (Defn NonStrict  _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
-}
definition kit (Defn Irrelevant _ _  _ _ _ _ _ _) = return []
definition kit (Defn _          q ty _ _ _ _ compiled d) = do
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
                           (L.map HS.UnkindedVar vars)
                           (HS.TyVar b)
             , HS.FunBind [HS.Match dummy infV
                                    (L.map HS.PVar vars) Nothing
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

    Axiom{}                                -> return $ fb axiomErr
    Function{ funClauses =        cls } -> function cls
    Primitive{ primClauses = Just cls } -> function cls
    Primitive{ primClauses = Nothing, primName = s } -> fb <$> primBody s
    Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs }
      | Just (HsType ty) <- compiledHaskell compiled -> do
      ccs <- concat <$> mapM checkConstructorType cs
      cov <- checkCover q ty np cs
      return $ tvaldecl q (dataInduction d) 0 (np + ni) [] (Just __IMPOSSIBLE__) ++ ccs ++ cov
    Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs } -> do
      (ars, cds) <- unzip <$> mapM condecl cs
      return $ tvaldecl q (dataInduction d) (maximum (np:ars) - np) (np + ni) cds cl
    Constructor{} -> return []
    Record{ recClause = cl, recCon = c, recFields = flds } -> do
      let noFields = genericLength flds
      let ar = arity ty
      cd <- snd <$> condecl c
--       cd <- case c of
--         Nothing -> return $ cdecl q noFields
--         Just c  -> snd <$> condecl c
      return $ tvaldecl q Inductive noFields ar [cd] cl
  where
  function cls = mkwhere <$> mapM (clause q) (tag 0 cls)
  tag _ []       = []
  tag i [cl]     = (i, True , cl): []
  tag i (cl:cls) = (i, False, cl): tag (i + 1) cls
  mkwhere (HS.FunBind [m0, HS.Match _     dn ps mt rhs (HS.BDecls [])] :
           fbs@(_:_)) =
          [HS.FunBind [m0, HS.Match dummy dn ps mt rhs (HS.BDecls fbs)]]
  mkwhere fbs = fbs
  fbWithType ty e =
    [ HS.TypeSig dummy [unqhname "d" q] $ fakeType ty ] ++ fb e
  fb e  = [HS.FunBind [HS.Match dummy (unqhname "d" q) [] Nothing
                                (HS.UnGuardedRhs $ e) (HS.BDecls [])]]
  axiomErr = rtmError $ "postulate evaluated: " ++ show q

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
        let pat = HS.PApp (HS.UnQual $ HS.Ident hsc) $ genericReplicate a HS.PWildCard
        return $ HS.Alt dummy pat (HS.UnGuardedAlt $ HS.Tuple []) (HS.BDecls [])
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
      n = genericLength (telToList tel)
  return (n - np, np)

clause :: QName -> (Nat, Bool, Clause) -> TCM HS.Decl
clause q (i, isLast, Clause{ clausePats = ps, clauseBody = b }) =
  HS.FunBind . (: cont) <$> main where
  main = match <$> argpatts ps (bvars b (0::Nat)) <*> clausebody b
  cont | isLast && any isCon ps = [match (L.map HS.PVar cvs) failrhs]
       | isLast                 = []
       | otherwise              = [match (L.map HS.PVar cvs) crhs]
  cvs  = L.map (ihname "v") [0 .. genericLength ps - 1]
  crhs = hsCast$ L.foldl HS.App (hsVarUQ $ dsubname q (i + 1)) (L.map hsVarUQ cvs)
  failrhs = rtmIncompleteMatch q  -- Andreas, 2011-11-16 call to RTE instead of inlined error
--  failrhs = rtmError $ "incomplete pattern matching: " ++ show q
  match hps rhs = HS.Match dummy (dsubname q i) hps Nothing
                           (HS.UnGuardedRhs rhs) (HS.BDecls [])
  bvars (Body _)           _ = []
  bvars (Bind (Abs _ b'))  n = HS.PVar (ihname "v" n) : bvars b' (n + 1)
  bvars (Bind (NoAbs _ b)) n = HS.PWildCard : bvars b n
  bvars NoBody             _ = repeat HS.PWildCard -- ?

  isCon (Arg _ _ ConP{}) = True
  isCon _                = False

-- argpatts aps xs = hps
-- xs is alist of haskell *variables* in form of patterns (because of wildcard)
argpatts :: [Arg Pattern] -> [HS.Pat] -> TCM [HS.Pat]
argpatts ps0 bvs = evalStateT (mapM pat' ps0) bvs
  where
  pat   (VarP _   ) = do v <- gets head; modify tail; return v
  pat   (DotP _   ) = pat (VarP dummy) -- WHY NOT: return HS.PWildCard -- SEE ABOVE
  pat   (LitP l   ) = return $ HS.PLit $ hslit l
  pat p@(ConP q _ ps) = do
    -- Note that irr is applied once for every subpattern, so in the
    -- worst case it is quadratic in the size of the pattern. I
    -- suspect that this will not be a problem in practice, though.
    irrefutable <- lift $ irr p
    let tilde = if   tildesEnabled && irrefutable
                then HS.PParen . HS.PIrrPat
                else id
    (tilde . HS.PParen) <$>
      (HS.PApp <$> lift (conhqn q) <*> mapM pat' ps)

  -- Andreas, 2010-09-29
  -- do not match against irrelevant stuff
  pat' (Arg _ Irrelevant _) = return $ HS.PWildCard
  pat' (Arg _ _          p) = pat p

  tildesEnabled = False

  -- | Is the pattern irrefutable?
  irr :: Pattern -> TCM Bool
  irr (VarP {})   = return True
  irr (DotP {})   = return True
  irr (LitP {})   = return False
  irr (ConP q _ ps) =
    (&&) <$> singleConstructorType q
         <*> (andM $ L.map irr' ps)

  -- | Irrelevant patterns are naturally irrefutable.
  irr' (Arg _ Irrelevant _) = return $ True
  irr' (Arg _ _          p) = irr p

clausebody :: ClauseBody -> TCM HS.Exp
clausebody b0 = runReaderT (go b0) 0 where
  go (Body tm       )   = hsCast <$> term tm
  go (Bind (Abs _ b))   = local (1+) $ go b
  go (Bind (NoAbs _ b)) = go b
  go NoBody             = return $ rtmError $ "Impossible Clause Body"

-- | Extract Agda term to Haskell expression.
--   Irrelevant arguments are extracted as @()@.
--   Types are extracted as @()@.
--   @DontCare@ outside of irrelevant arguments is extracted as @error@.
term :: Term -> ReaderT Nat TCM HS.Exp
term tm0 = case ignoreSharing tm0 of
  Var   i as -> do n <- ask; apps (hsVarUQ $ ihname "v" (n - i - 1)) as
  Lam   _ at -> do n <- ask; HS.Lambda dummy [HS.PVar $ ihname "v" n] <$>
                              local (1+) (term $ absBody at)
  Lit   l    -> lift $ literal l
  Def   q as -> (`apps` as) . HS.Var =<< lift (xhqn "d" q)
  Con   q as -> do
    kit <- lift coinductionKit
    if Just q == (nameOfSharp <$> kit)
      then (`apps` as) . HS.Var =<< lift (xhqn "d" q)
      else (`apps` as) . HS.Con =<< lift (conhqn q)
  Level l    -> term =<< lift (reallyUnLevelView l)
  Pi    _ _  -> return HS.unit_con
  Sort  _    -> return HS.unit_con
  MetaV _ _  -> mazerror "hit MetaV"
  DontCare _ -> return $ rtmError $ "hit DontCare"
  Shared{}   -> __IMPOSSIBLE__
  where apps =  foldM (\h a -> HS.App h <$> term' a)

-- | Irrelevant arguments are replaced by Haskells' ().
term' :: Arg Term -> ReaderT Nat TCM HS.Exp
term' (Arg _ Irrelevant _) = return HS.unit_con
term' (Arg _ _          t) = term t

literal :: Literal -> TCM HS.Exp
literal l = case l of
  LitInt    _ _   -> do toN <- bltQual "NATURAL" mazIntegerToNat
                        return $ HS.Var toN `HS.App` typed "Integer"
  LitFloat  _ _   -> return $ typed "Double"
  LitQName  _ x   -> litqname x
  _               -> return $ l'
  where l'    = HS.Lit $ hslit l
        typed = HS.ExpTypeSig dummy l' . HS.TyCon . rtmQual

hslit :: Literal -> HS.Literal
hslit l = case l of LitInt    _ x -> HS.Int    x
                    LitFloat  _ x -> HS.Frac   (toRational x)
                    LitString _ x -> HS.String x
                    LitChar   _ x -> HS.Char   x
                    LitQName  _ x -> __IMPOSSIBLE__

litqname :: QName -> TCM HS.Exp
litqname x = return $
  HS.Con (HS.Qual mazRTE $ HS.Ident "QName") `HS.App`
  HS.Lit (HS.Int n) `HS.App`
  HS.Lit (HS.Int m) `HS.App`
  (rtmError "primQNameType: not implemented") `HS.App`
  (rtmError "primQNameDefinition: not implemented")
  where
    NameId n m = nameId $ qnameName x

condecl :: QName -> TCM (Nat, HS.ConDecl)
condecl q = do
  (ar, np) <- conArityAndPars q
  return $ (ar + np, cdecl q ar)

cdecl :: QName -> Nat -> HS.ConDecl
cdecl q n = HS.ConDecl (unqhname "C" q)
            [ HS.UnBangedTy $ HS.TyVar $ ihname "a" i | i <- [0 .. n - 1]]

tvaldecl :: QName
         -> Induction
            -- ^ Is the type inductive or coinductive?
         -> Nat -> Nat -> [HS.ConDecl] -> Maybe Clause -> [HS.Decl]
tvaldecl q ind ntv npar cds cl =
  HS.FunBind [HS.Match dummy vn pvs Nothing
                       (HS.UnGuardedRhs HS.unit_con) (HS.BDecls [])] :
  maybe [HS.DataDecl dummy kind [] tn tvs
                     (L.map (HS.QualConDecl dummy [] []) cds) []]
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
infodecl q = fakeD (unqhname "name" q) $ show (show q)

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

hsCast e = mazCoerce `HS.App` hsCast' e
hsCast' (HS.App e1 e2)     = hsCast' e1 `HS.App` (hsCoerce $ hsCast' e2)
hsCast' (HS.Lambda _ ps e) = HS.Lambda dummy ps $ hsCast' e
hsCast' e = e

-- No coercion for literal integers
hsCoerce e@(HS.ExpTypeSig _ (HS.Lit (HS.Int{})) _) = e
hsCoerce e = HS.App mazCoerce e


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
  p = HS.LanguagePragma dummy $ L.map HS.Ident $
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
  , "data QName a b = QName { nameId, moduleId :: Integer, qnameType :: a, qnameDefinition :: b }"
  , "instance Eq (QName a b) where"
  , "  QName a b _ _ == QName c d _ _ = (a, b) == (c, d)"
  , ""
  , "mazIncompleteMatch :: String -> a"
  , "mazIncompleteMatch s = error (\"MAlonzo Runtime Error: incomplete pattern matching: \" ++ s)"
  ]
  where
    parse = HS.parseWithMode
              HS.defaultParseMode{HS.extensions = [explicitForAll]}
    ok (HS.ParseOk d)   = d
    ok HS.ParseFailed{} = __IMPOSSIBLE__

explicitForAll :: HS.Extension
explicitForAll =
-- GHC 7.0.1 cannot parse the following CPP conditional
-- error: missing binary operator before token "("
#if MIN_VERSION_haskell_src_exts(1,12,0)
  HS.ExplicitForAll
#else
  HS.ExplicitForall
#endif

compileDir :: TCM FilePath
compileDir = do
  mdir <- optCompileDir <$> commandLineOptions
  case mdir of
    Just dir -> return dir
    Nothing  -> __IMPOSSIBLE__

outFile' m = do
  mdir <- compileDir
  let (fdir, fn) = splitFileName $ repldot pathSeparator $
                   prettyPrint m
  let dir = mdir </> fdir
      fp  = dir </> replaceExtension fn "hs"
  liftIO $ createDirectoryIfMissing True dir
  return (mdir, fp)
  where
  repldot c = L.map (\c' -> if c' == '.' then c else c')

outFile :: HS.ModuleName -> TCM FilePath
outFile m = snd <$> outFile' m

outFile_ :: TCM FilePath
outFile_ = outFile =<< curHsMod

callGHC :: Interface -> TCM ()
callGHC i = do
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
        [ "-O"
        , "-o", mdir </> show outputName
        , "-Werror"
        ]
      otherArgs       =
        [ "-i" ++ mdir
        , "-main-is", hsmod
        , fp
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
