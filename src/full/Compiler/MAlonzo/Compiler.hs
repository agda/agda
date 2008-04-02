module Compiler.MAlonzo.Compiler where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Data.Char
import Data.List as L
import Data.Map as M
import Data.Set as S
import Language.Haskell.Syntax
import System.Directory
import System.IO
import System.Time

import Compiler.MAlonzo.Misc
import Compiler.MAlonzo.Pretty
import Compiler.MAlonzo.Primitives
import Interaction.Imports
import Interaction.Monad
import Interaction.Options
import Syntax.Common
import Syntax.Internal
import Syntax.Literal
import TypeChecking.Monad
import TypeChecking.Monad.Options
import TypeChecking.Reduce
import Utils.FileName
import Utils.Monad
import Utils.Unicode

compilerMain :: IM () -> IM ()
compilerMain typecheck = (typecheck >>) $ liftTCM $ do
  mapM_ compile =<< ((:) <$> ((,) <$> buildInterface <*> liftIO getClockTime)
                         <*> (M.elems <$> getVisitedModules))

compile :: (Interface, ClockTime) -> TCM ()
compile ict = do
  setInterface ict
  ifM uptodate noComp $ (yesComp >>) $ do
    writeModule =<< decl <$> curHsMod <*> (definitions =<< curDefs) <*> imports
  where
  decl mn ds imp = HsModule dummy mn Nothing imp ds
  uptodate = liftIO =<< (isNewerThan <$> outFile <*> ifile)
  ifile    = findFile InterfaceFile =<< curMName
  noComp   = reportLn 1.(++ " : no compilation is needed.").show =<< curMName
  yesComp  = reportLn 1.(`repl` "Compiling <<0>> in <<1>> to <<2>>") =<<
             sequence [show <$> curMName, ifile, outFile] :: TCM ()

--------------------------------------------------
-- imported modules
--   I use stImportedModules in a non-standard way,
--   accumulating in it what are acutally used in Misc.xqual
--------------------------------------------------

imports :: TCM [HsImportDecl]
imports = (decl False unsafeCoerceMod :) . L.map (decl True) . uniq <$>
          ((++) <$> importsForPrim <*> (L.map mazMod <$> mnames))
  where decl qual m = HsImportDecl dummy m qual Nothing Nothing
        mnames      = (++) <$> (S.elems <$> gets stImportedModules)
                           <*> (iImportedModules <$> curIF)
        uniq        = L.map head . group . L.sort

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

definitions :: Definitions -> TCM [HsDecl]
definitions = M.fold (liftM2(++).(definition<.>instantiateFull)) declsForPrim

definition :: Definition -> TCM [HsDecl]
definition (Defn q ty _ _ d) = (infodecl q :) <$> case d of
  Axiom _                  -> return $ fb axiom
  Function cls _ _         -> mkwhere <$> mapM (clause q) (tag 0 cls)
  Datatype np ni cl cs _ _ -> do
    (ars, cds) <- unzip <$> mapM condecl cs
    return $ tvaldecl q (maximum (np:ars) - np) (np + ni) cds cl
  Constructor _ _ _ _ _    -> return []
  Record _ cl flds _ _ _   -> do
    ar <- arity <$> normalise ty
    return $ tvaldecl q (length flds) ar [cdecl q (length flds)] cl  
  Primitive _ s _          -> fb <$> primBody s
  where
  tag _ []       = []
  tag i [cl]     = (i, True , cl): []
  tag i (cl:cls) = (i, False, cl): tag (i + 1) cls
  mkwhere (HsFunBind [m0, HsMatch _     dn ps rhs [] ] : fbs@(_:_)) =
          [HsFunBind [m0, HsMatch dummy dn ps rhs fbs]]
  mkwhere fbs = fbs
  fb e  =[HsFunBind[HsMatch dummy (unqhname "d" q)[] (HsUnGuardedRhs $ e) []]]
  axiom = rtmError $ "postulate evaluated: " ++ show q

clause :: QName -> (Int, Bool, Clause) -> TCM HsDecl
clause q (i, isLast, Clause _ _ ps b) = HsFunBind . (: cont) <$> main where
  main = match <$> argpatts ps (bvars b (0::Int)) <*> clausebody b
  cont | isLast    = []
       | otherwise = [match (L.map HsPVar cvs) crhs]
  cvs  = L.map (ihname "v") [0 .. length ps - 1]
  crhs = hsCast$ foldl HsApp (hsVarUQ $ dsubname q (i + 1)) (L.map hsVarUQ cvs)
  match hps rhs = HsMatch dummy (dsubname q i) hps (HsUnGuardedRhs rhs) []
  bvars (Body _)          _ = []
  bvars (Bind (Abs _ b')) n = HsPVar (ihname "v" n) : bvars b' (n + 1)
  bvars (NoBind      b' ) n = HsPWildCard           : bvars b' n
  bvars NoBody            _ = repeat HsPWildCard -- ?

argpatts :: [Arg Pattern] -> [HsPat] -> TCM [HsPat]
argpatts ps0 bvs = evalStateT (mapM pat' ps0) bvs where
  pat (VarP _   ) = do v <- gets head; modify tail; return v
  pat (DotP _   ) = pat (VarP dummy)
  pat (ConP q ps) = (HsPParen .).HsPApp <$> lift (conhqn q) <*> mapM pat' ps
  pat (LitP l   ) = return $ HsPLit $ hslit l
  pat' = pat . unArg

clausebody :: ClauseBody -> TCM HsExp
clausebody b0 = runReaderT (go b0) 0 where
  go (Body   tm       ) = hsCast <$> term tm
  go (Bind   (Abs _ b)) = local (1+) $ go b
  go (NoBind b        ) = go b
  go NoBody             = return$ rtmError$ "Impossible Clause Body"

term :: Term -> ReaderT Int TCM HsExp
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
  BlockedV _ -> mazerror "hit BlockedV"
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

condecl :: QName -> TCM (Int, HsConDecl)
condecl q = ignoreAbstractMode (getConstInfo q) >>= \d -> case d of
  Defn _ ty _ _ (Constructor np _ _ _ _) -> do ar <- arity <$> normalise ty
                                               return $ (ar, cdecl q (ar - np))
  _ -> mazerror $ "condecl:" ++ gshow' (q, d)

cdecl :: QName -> Nat -> HsConDecl
cdecl q n = HsConDecl dummy (unqhname "C" q)
            [ HsUnBangedTy $ HsTyVar $ ihname "a" i | i <- [0 .. n - 1]]

tvaldecl :: QName -> Nat -> Nat -> [HsConDecl] -> Maybe Clause -> [HsDecl]
tvaldecl q ntv npar cds cl = let
    (tn, vn) = (unqhname "T" q, unqhname "d" q)
    tvs = [          ihname "a" i | i <- [0 .. ntv  - 1]]
    pvs = [ HsPVar $ ihname "a" i | i <- [0 .. npar - 1]]
  in HsFunBind [HsMatch dummy vn pvs (HsUnGuardedRhs unit_con) []] :
     maybe [HsDataDecl dummy [] tn tvs cds []] (const []) cl

infodecl :: QName -> HsDecl
infodecl q = fakeD (unqhname "name" q)  $ "\"\" -- " ++ show q

--------------------------------------------------
-- Inserting unsafeCoerce
--------------------------------------------------

hsCast :: HsExp -> HsExp
hsCast = addcast . go where
  addcast [e@(HsVar(UnQual(HsIdent(c:ns))))] | c == 'v' && all isDigit ns = e
  addcast es = foldl HsApp mazCoerce es
  -- this need to be extended if you generate other kinds of exps.
  go (HsApp e1 e2    ) = go e1 ++ [hsCast e2]
  go (HsLambda _ ps e) = [ HsLambda dummy ps (hsCast e) ]
  go e = [e]

{-
hsCast (HsApp e1 e2)     = hsCast e1 `HsApp` (mazCoerce `HsApp` hsCast e2)
hsCast (HsLambda _ ps e) = HsLambda dummy ps $ hsCast e
hsCast e = e
-}

--------------------------------------------------
-- Writing out a haskell module
--------------------------------------------------

writeModule :: HsModule -> TCM ()
writeModule m = liftIO .(`writeFileUTF8`(preamble ++ prettyPrint m))=<< outFile
  where
  preamble = unlines $ [ "{-# LANGUAGE EmptyDataDecls"
                       , "           , ExistentialQuantification"
                       , "           , PatternSignatures"
                       , "           , UnicodeSyntax"
                       , "  #-}"
                       ]
outFile = do
  mdir <- maybe (liftIO getCurrentDirectory) return =<<
          gets (optMAlonzoDir . stOptions)
  (fdir, fn, _) <- splitFilePath . repldot slash . prettyPrint <$> curHsMod
  let (dir, fp) = (addSlash mdir ++ fdir, addSlash dir ++ fn ++ ".hs")
  liftIO $ createDirectoryIfMissing True dir
  return fp
  where
  repldot c = L.map (\c' -> if c' == '.' then c else c')
           
