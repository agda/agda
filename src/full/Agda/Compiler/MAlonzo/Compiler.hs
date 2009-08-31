{-# LANGUAGE CPP #-}

module Agda.Compiler.MAlonzo.Compiler where

import Control.Applicative
import qualified Control.Exception as E
import Control.Monad.Reader
import Control.Monad.State
import Data.Char
import Data.List as L
import Data.Map as M
import Data.Set as S
import Language.Haskell.Syntax
import System.Cmd
import System.Directory
import System.Exit
import System.IO
import qualified System.IO.UTF8 as UTF8
import System.Time
import System.Process
import System.FilePath hiding (normalise, (<.>))

import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Compiler.MAlonzo.Primitives
import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Monad
import Agda.Interaction.Options
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.Impossible

#include "../../undefined.h"

compilerMain :: Interface -> TCM ()
compilerMain mainI =
  -- Preserve the state (the compiler modifies the state).
  bracket get put $ \_ -> do

    -- Compute the output directory.
    opts <- commandLineOptions
    malonzoDir <- case optMAlonzoDir opts of
      Just dir -> return dir
      Nothing  -> do
        -- The default output directory is the project root.
        let tm = toTopLevelModuleName $ iModuleName mainI
        f <- findFile tm
        return $ filePath $ CN.projectRoot f tm
    setCommandLineOptions PersistentOptions $
      opts { optMAlonzoDir = Just malonzoDir }

    ignoreAbstractMode $ do
      mapM_ (compile . miInterface) =<< (M.elems <$> getVisitedModules)
      callGHC mainI

compile :: Interface -> TCM ()
compile i = do
  setInterface i
  ifM uptodate noComp $ (yesComp >>) $ do
    writeModule =<< decl <$> curHsMod <*> (definitions =<< curDefs) <*> imports
  where
  decl mn ds imp = HsModule dummy mn Nothing imp ds
  uptodate = liftIO =<< (isNewerThan <$> outFile <*> ifile)
  ifile    = maybe __IMPOSSIBLE__ filePath <$>
               (findInterfaceFile . toTopLevelModuleName =<< curMName)
  noComp   = reportSLn "" 1 . (++ " : no compilation is needed.").show =<< curMName
  yesComp  = reportSLn "" 1 . (`repl` "Compiling <<0>> in <<1>> to <<2>>") =<<
             sequence [show <$> curMName, ifile, outFile] :: TCM ()

--------------------------------------------------
-- imported modules
--   I use stImportedModules in a non-standard way,
--   accumulating in it what are acutally used in Misc.xqual
--------------------------------------------------

imports :: TCM [HsImportDecl]
imports = (++) <$> unqualImps <*> qualImps where
  unqualImps = (L.map (decl False) . (unsafeCoerceMod :) . L.map Module) <$>
               getHaskellImports
  qualImps   = L.map (decl True) . uniq <$>
               ((++) <$> importsForPrim <*> (L.map mazMod <$> mnames))
  decl qual m = HsImportDecl dummy m qual Nothing Nothing
  mnames      = (++) <$> (S.elems <$> gets stImportedModules)
                     <*> (iImportedModules <$> curIF)
  uniq        = L.map head . group . L.sort

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

definitions :: Definitions -> TCM [HsDecl]
definitions = M.fold (liftM2(++).(definition<.>instantiateFull)) declsForPrim

definition :: Definition -> TCM [HsDecl]
definition (Defn q ty _ _ d) = do
  checkTypeOfMain q ty
  (infodecl q :) <$> case d of
    Axiom{ axHsDef = Just (HsDefn ty hs) } -> return $ fbWithType ty (fakeExp hs)
    Axiom{}                                -> return $ fb axiomErr
    Function{ funClauses = cls } -> mkwhere <$> mapM (clause q) (tag 0 cls)
    Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs, dataHsType = Just ty } -> do
      ccs <- concat <$> mapM checkConstructorType cs
      cov <- checkCover q ty np cs
      return $ tvaldecl q (dataInduction d) 0 (np + ni) [] (Just __IMPOSSIBLE__) ++ ccs ++ cov
    Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs, dataHsType = Nothing } -> do
      (ars, cds) <- unzip <$> mapM condecl cs
      return $ tvaldecl q (dataInduction d) (maximum (np:ars) - np) (np + ni) cds cl
    Constructor{} -> return []
    Record{ recClause = cl, recFields = flds } -> do
      ar <- arity <$> normalise ty
      return $ tvaldecl q Inductive (genericLength flds) ar [cdecl q (genericLength flds)] cl
    Primitive{ primName = s } -> fb <$> primBody s
  where
  tag _ []       = []
  tag i [cl]     = (i, True , cl): []
  tag i (cl:cls) = (i, False, cl): tag (i + 1) cls
  mkwhere (HsFunBind [m0, HsMatch _     dn ps rhs [] ] : fbs@(_:_)) =
          [HsFunBind [m0, HsMatch dummy dn ps rhs fbs]]
  mkwhere fbs = fbs
  fbWithType ty e =
    [ HsTypeSig dummy [unqhname "d" q] $ fakeType ty ] ++ fb e
  fb e  =[HsFunBind[HsMatch dummy (unqhname "d" q)[] (HsUnGuardedRhs $ e) []]]
  axiomErr = rtmError $ "postulate evaluated: " ++ show q

checkConstructorType :: QName -> TCM [HsDecl]
checkConstructorType q = do
  Constructor{ conHsCode = Just (ty, hs) } <- theDef <$> getConstInfo q
  return [ HsTypeSig dummy [unqhname "check" q] $ fakeType ty
         , HsFunBind [HsMatch dummy (unqhname "check" q) [] (HsUnGuardedRhs $ fakeExp hs) []]
         ]

checkCover :: QName -> HaskellType -> Nat -> [QName] -> TCM [HsDecl]
checkCover q ty n cs = do
  let tvs = [ "a" ++ show i | i <- [1..n] ]
      makeClause c = do
        a <- constructorArity c
        Just (_, hsc) <- conHsCode . theDef <$> getConstInfo c
        let pat = HsPApp (UnQual $ HsIdent hsc) $ genericReplicate a HsPWildCard
        return $ HsAlt dummy pat (HsUnGuardedAlt $ HsTuple []) []
  cs <- mapM makeClause cs
  let rhs = case cs of
              [] -> fakeExp "()" -- There is no empty case statement in Haskell
              _  -> HsCase (HsVar $ UnQual $ HsIdent "x") cs

  return [ HsTypeSig dummy [unqhname "cover" q] $ fakeType $ unwords (ty : tvs) ++ " -> ()"
         , HsFunBind [HsMatch dummy (unqhname "cover" q) [HsPVar $ HsIdent "x"]
            (HsUnGuardedRhs rhs) []]
         ]

-- | Move somewhere else!
constructorArity :: MonadTCM tcm => QName -> tcm Nat
constructorArity q = do
  def <- getConstInfo q
  a <- normalise $ defType def
  case theDef def of
    Constructor{ conPars = np } -> return $ arity a - np
    _ -> fail $ "constructorArity: non constructor: " ++ show q

clause :: QName -> (Nat, Bool, Clause) -> TCM HsDecl
clause q (i, isLast, Clause{ clausePats = ps, clauseBody = b }) =
  HsFunBind . (: cont) <$> main where
  main = match <$> argpatts ps (bvars b (0::Nat)) <*> clausebody b
  cont | isLast && any isCon ps = [match (L.map HsPVar cvs) failrhs]
       | isLast                 = []
       | otherwise              = [match (L.map HsPVar cvs) crhs]
  cvs  = L.map (ihname "v") [0 .. genericLength ps - 1]
  crhs = hsCast$ foldl HsApp (hsVarUQ $ dsubname q (i + 1)) (L.map hsVarUQ cvs)
  failrhs = rtmError $ "incomplete pattern matching: " ++ show q
  match hps rhs = HsMatch dummy (dsubname q i) hps (HsUnGuardedRhs rhs) []
  bvars (Body _)          _ = []
  bvars (Bind (Abs _ b')) n = HsPVar (ihname "v" n) : bvars b' (n + 1)
  bvars (NoBind      b' ) n = HsPWildCard           : bvars b' n
  bvars NoBody            _ = repeat HsPWildCard -- ?

  isCon (Arg _ ConP{}) = True
  isCon _              = False

argpatts :: [Arg Pattern] -> [HsPat] -> TCM [HsPat]
argpatts ps0 bvs = evalStateT (mapM pat' ps0) bvs
  where
  pat   (VarP _   ) = do v <- gets head; modify tail; return v
  pat   (DotP _   ) = pat (VarP dummy)
  pat   (LitP l   ) = return $ HsPLit $ hslit l
  pat p@(ConP q ps) = do
    -- Note that irr is applied once for every subpattern, so in the
    -- worst case it is quadratic in the size of the pattern. I
    -- suspect that this will not be a problem in practice, though.
    irrefutable <- lift $ irr p
    let tilde = if irrefutable then HsPParen . HsPIrrPat else id
    (tilde . HsPParen) <$>
      (HsPApp <$> lift (conhqn q) <*> mapM pat' ps)

  pat' = pat . unArg

  -- | Is the pattern irrefutable?
  irr :: Pattern -> TCM Bool
  irr (VarP {})   = return True
  irr (DotP {})   = return True
  irr (LitP {})   = return False
  irr (ConP q ps) =
    (&&) <$> singleConstructorType q
         <*> (and <$> mapM (irr . unArg) ps)

clausebody :: ClauseBody -> TCM HsExp
clausebody b0 = runReaderT (go b0) 0 where
  go (Body   tm       ) = hsCast <$> term tm
  go (Bind   (Abs _ b)) = local (1+) $ go b
  go (NoBind b        ) = go b
  go NoBody             = return$ rtmError$ "Impossible Clause Body"

term :: Term -> ReaderT Nat TCM HsExp
term tm0 = case tm0 of
  Var   i as -> do n <- ask; apps (hsVarUQ $ ihname "v" (n - i - 1)) as
  Lam   _ at -> do n <- ask; HsLambda dummy [HsPVar $ ihname "v" n] <$>
                              local (1+) (term $ absBody at)
  Lit   l    -> lift $ literal l
  Def   q as -> (`apps` as) . HsVar =<< lift (xhqn "d" q)
  Con   q as -> (`apps` as) . HsCon =<< lift (conhqn q)
  Pi    _ _  -> return unit_con
  Fun   _ _  -> return unit_con
  Sort  _    -> return unit_con
  MetaV _ _  -> mazerror "hit MetaV"
  where apps =  foldM (\h a -> HsApp h <$> term (unArg a))

literal :: Literal -> TCM HsExp
literal l = case l of
  LitInt    _ _   -> do toN <- bltQual "NATURAL" mazIntegerToNat
                        return $ HsVar toN `HsApp` typed "Integer"
  LitFloat  _ _   -> return $ typed "Double"
  _               -> return $ l'
  where l'    = HsLit $ hslit l
        typed = HsExpTypeSig dummy l' . HsQualType [] . HsTyCon . rtmQual

hslit :: Literal -> HsLiteral
hslit l = case l of LitInt    _ x -> HsInt    x
                    LitFloat  _ x -> HsFrac   (toRational x)
                    LitString _ x -> HsString x
                    LitChar   _ x -> HsChar   x

condecl :: QName -> TCM (Nat, HsConDecl)
condecl q = getConstInfo q >>= \d -> case d of
  Defn _ ty _ _ (Constructor {conPars = np}) -> do ar <- arity <$> normalise ty
                                                   return $ (ar, cdecl q (ar - np))
  _ -> mazerror $ "condecl:" ++ gshow' (q, d)

cdecl :: QName -> Nat -> HsConDecl
cdecl q n = HsConDecl dummy (unqhname "C" q)
            [ HsUnBangedTy $ HsTyVar $ ihname "a" i | i <- [0 .. n - 1]]

tvaldecl :: QName
         -> Induction
            -- ^ Is the type inductive or coinductive?
         -> Nat -> Nat -> [HsConDecl] -> Maybe Clause -> [HsDecl]
tvaldecl q ind ntv npar cds cl =
  HsFunBind [HsMatch dummy vn pvs (HsUnGuardedRhs unit_con) []] :
  maybe [datatype] (const []) cl
  where
  (tn, vn) = (unqhname "T" q, unqhname "d" q)
  tvs = [          ihname "a" i | i <- [0 .. ntv  - 1]]
  pvs = [ HsPVar $ ihname "a" i | i <- [0 .. npar - 1]]

  -- Inductive data types consisting of a single constructor with a
  -- single argument are translated into newtypes.
  datatype = case (ind, cds) of
    (Inductive, [c@(HsConDecl _ _ [_])]) -> newtyp c
    (Inductive, [c@(HsRecDecl _ _ [_])]) -> newtyp c
    _                                    -> datatyp

  newtyp c = HsNewTypeDecl dummy [] tn tvs c   []
  datatyp  = HsDataDecl    dummy [] tn tvs cds []

infodecl :: QName -> HsDecl
infodecl q = fakeD (unqhname "name" q) $ show (show q)

--------------------------------------------------
-- Inserting unsafeCoerce
--------------------------------------------------

hsCast :: HsExp -> HsExp
{-
hsCast = addcast . go where
  addcast [e@(HsVar(UnQual(HsIdent(c:ns))))] | c == 'v' && all isDigit ns = e
  addcast es = foldl HsApp mazCoerce es
  -- this need to be extended if you generate other kinds of exps.
  go (HsApp e1 e2    ) = go e1 ++ [hsCast e2]
  go (HsLambda _ ps e) = [ HsLambda dummy ps (hsCast e) ]
  go e = [e]
-}

hsCast e = mazCoerce `HsApp` hsCast' e
hsCast' (HsApp e1 e2)     = hsCast' e1 `HsApp` (mazCoerce `HsApp` hsCast' e2)
hsCast' (HsLambda _ ps e) = HsLambda dummy ps $ hsCast' e
hsCast' e = e

--------------------------------------------------
-- Writing out a haskell module
--------------------------------------------------

writeModule :: HsModule -> TCM ()
writeModule m =
  liftIO . (`UTF8.writeFile` (preamble ++ prettyPrint m)) =<< outFile
  where
  preamble = unlines $ [ "{-# LANGUAGE EmptyDataDecls"
                       , "           , ExistentialQuantification"
                       , "           , ScopedTypeVariables"
                       , "           , UnicodeSyntax"
                       , "           , NoMonomorphismRestriction"
                       , "  #-}"
                       ]

malonzoDir :: TCM FilePath
malonzoDir = do
  mdir <- optMAlonzoDir <$> commandLineOptions
  case mdir of
    Just dir -> return dir
    Nothing  -> __IMPOSSIBLE__

outFile' = do
  mdir <- malonzoDir
  (fdir, fn) <- splitFileName . repldot pathSeparator .
                prettyPrint <$> curHsMod
  let dir = mdir </> fdir
      fp  = dir </> replaceExtension fn "hs"
  liftIO $ createDirectoryIfMissing True dir
  return (mdir, fp)
  where
  repldot c = L.map (\c' -> if c' == '.' then c else c')

outFile :: TCM FilePath
outFile = snd <$> outFile'

callGHC :: Interface -> TCM ()
callGHC i = do
  setInterface i
  mdir          <- malonzoDir
  hsmod         <- prettyPrint <$> curHsMod
  MName agdaMod <- curMName
  let outputName = case agdaMod of
        [] -> __IMPOSSIBLE__
        ms -> last ms
  (mdir, fp) <- outFile'
  opts       <- optGhcFlags <$> commandLineOptions

  let overridableArgs =
        [ "-O"
        , "-o", mdir </> show outputName
        ]
      otherArgs       =
        [ "-i" ++ mdir
        , "-main-is", hsmod
        , fp
        , "--make"
        , "-fwarn-incomplete-patterns"
        , "-fno-warn-overlapping-patterns"
        , "-Werror"
        ]
      args     = overridableArgs ++ opts ++ otherArgs
      compiler = "ghc"

  reportSLn "" 1 $ "calling: " ++ L.intercalate " " (compiler : args)
  (inn, out, err, p) <-
    liftIO $ runInteractiveProcess compiler args Nothing Nothing

  liftIO $ do
    hClose inn
    -- The handles should be in text mode.
    hSetBinaryMode out False
    hSetBinaryMode err False

  -- GHC seems to use stderr for progress reports.
  s <- liftIO $ join <$> hGetContents err <*> hGetContents out
  reportSLn "" 1 s

  exitcode <- liftIO $ do
    -- Ensure that the output has been read before waiting for the
    -- process.
    E.evaluate (length s)
    waitForProcess p
  case exitcode of
    ExitFailure _ -> typeError (CompilationError s)
    _             -> return ()

  where
  -- Note that this function returns s1 before inspecting its input.
  join s1 s2 =
    s1 ++ (if L.null s1 || last s1 == '\n' then "" else "\n") ++ s2
