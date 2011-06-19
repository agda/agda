{-# LANGUAGE CPP #-}

module Agda.Compiler.JS.Compiler where

import Prelude hiding ( null, writeFile )
import Control.Monad.Reader ( liftIO )
import Control.Monad.State ( get, put )
import Data.List ( intercalate, map, filter, isPrefixOf, concat, genericDrop, genericLength )
import Data.Map
  ( Map, null, empty, fold, singleton, fromList, toList, toAscList, insertWith, elems  )
import System.Directory ( createDirectoryIfMissing )
import System.FilePath ( pathSeparator, splitFileName, (</>) )

import Agda.Interaction.FindFile ( findFile, findInterfaceFile )
import Agda.Interaction.Imports ( isNewerThan )
import Agda.Interaction.Options ( optCompileDir )
import Agda.Syntax.Common ( Nat, Arg, unArg )
import Agda.Syntax.Concrete.Name ( projectRoot )
import Agda.Syntax.Internal
  ( Name, Args, Type, ModuleName(MName), QName(QName),
    Clauses(Clauses), Clause(Clause),
    Pattern(VarP,DotP,LitP,ConP), Abs(Abs),
    ClauseBody(Body,NoBody,Bind,NoBind),
    Term(Var,Lam,Lit,Level,Def,Con,Pi,Fun,Sort,MetaV,DontCare),
    toTopLevelModuleName, mnameToList, qnameName, absBody,
    translatedClause, clausePats, clauseBody, arity, unEl )
import Agda.Syntax.Literal ( Literal(LitInt,LitFloat,LitString,LitChar,LitQName) )
import Agda.TypeChecking.Level ( reallyUnLevelView )
import Agda.TypeChecking.Monad
  ( TCM, Definition(Defn), Definitions, Interface,
    JSCode, Defn(Record,Datatype,Constructor,Primitive,Function,Axiom),
    iModuleName, iImportedModules, theDef, getConstInfo, typeOfConst,
    ignoreAbstractMode, miInterface, getVisitedModules,
    defType, funClauses, funProjection,
    dataPars, dataIxs, dataClause, dataCons,
    conPars, conData, conSrcCon,
    recClause, recCon, recFields, recPars, recNamedCon,
    primClauses, defJSDef )
import Agda.TypeChecking.Monad.Options ( setCommandLineOptions, commandLineOptions, reportSLn )
import Agda.TypeChecking.Reduce ( instantiateFull, normalise )
import Agda.Utils.FileName ( filePath )
import Agda.Utils.Monad ( (<$>), (<*>), bracket, ifM )
import Agda.Utils.IO.UTF8 ( writeFile )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import Agda.Compiler.MAlonzo.Misc ( curDefs, curIF, curMName, setInterface )
import Agda.Compiler.MAlonzo.Primitives ( repl )

import Agda.Compiler.JS.Syntax
  ( Exp(Self,Local,Global,Undefined,String,Char,Integer,Double,Lambda,Object,Apply,Lookup),
    LocalId(LocalId), GlobalId(GlobalId), MemberId(MemberId), Module(Module),
    modName )
import Agda.Compiler.JS.Substitution
  ( curriedLambda, curriedApply, fix, emp, object, subst, apply )
import Agda.Compiler.JS.Case ( Tag(Tag), Case(Case), Patt(VarPatt,Tagged), lambda )
import Agda.Compiler.JS.Pretty ( pretty )

#include "../../undefined.h"

--------------------------------------------------
-- Entry point into the compiler
--------------------------------------------------

compilerMain :: Interface -> TCM ()
compilerMain mainI =
  -- Preserve the state (the compiler modifies the state).
  bracket get put $ \_ -> do

    -- Compute the output directory.
    opts <- commandLineOptions
    compileDir <- case optCompileDir opts of
      Just dir -> return dir
      Nothing  -> do
        -- The default output directory is the project root.
        let tm = toTopLevelModuleName $ iModuleName mainI
        f <- findFile tm
        return $ filePath $ projectRoot f tm
    setCommandLineOptions $
      opts { optCompileDir = Just compileDir }

    ignoreAbstractMode $ do
      mapM_ (compile . miInterface) =<< (elems <$> getVisitedModules)

compile :: Interface -> TCM ()
compile i = do
  setInterface i
  ifM uptodate noComp $ (yesComp >>) $ do
    writeModule =<< curModule
  where
  uptodate = liftIO =<< (isNewerThan <$> outFile_ <*> ifile)
  ifile    = maybe __IMPOSSIBLE__ filePath <$>
               (findInterfaceFile . toTopLevelModuleName =<< curMName)
  noComp   = reportSLn "" 1 . (++ " : no compilation is needed.").show =<< curMName
  yesComp  = reportSLn "" 1 . (`repl` "Compiling <<0>> in <<1>> to <<2>>") =<<
             sequence [show <$> curMName, ifile, outFile_] :: TCM ()

--------------------------------------------------
-- Naming
--------------------------------------------------

prefix  = "jAgda"

jsMod :: ModuleName -> GlobalId
jsMod m = GlobalId (prefix : map show (mnameToList m))

jsFileName :: GlobalId -> String
jsFileName (GlobalId ms) = intercalate [pathSeparator] ms ++ ".js"

jsMember :: Name -> MemberId
jsMember n = MemberId (show n)

-- Rather annoyingly, the anonymous construtor of a record R in module M
-- is given the name M.recCon, but a named constructor C
-- is given the name M.R.C, sigh. This causes a lot of hoop-jumping
-- in the map from Agda names to JS names, which we patch by renaming
-- anonymous constructors to M.R.record.

global' :: QName -> TCM (Exp,[MemberId])
global' (QName (MName ms) n) = do
  i <- iModuleName <$> curIF
  is <- iImportedModules <$> curIF
  seg <- return (maximum (map length (filter (`isPrefixOf` ms) (map mnameToList (i : is)))))
  m <- return (MName (take seg ms))
  ls <- return (map jsMember (drop seg ms ++ [n]))
  case (m == i) of
    True -> return (Self, ls)
    False -> return (Global (jsMod m), ls)

global :: QName -> TCM (Exp,[MemberId])
global q = do
  d <- getConstInfo q
  case d of
    Defn { theDef = Constructor { conData = p } } -> do
      d <- getConstInfo p
      case d of
        Defn { theDef = Record { recNamedCon = False } } -> do
          (m,ls) <- global' p
          return (m, ls ++ [MemberId "record"])
        _ -> global' q
    _ -> global' q

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

curModule :: TCM Module
curModule = do
  m <- (jsMod <$> curMName)
  is <- map jsMod <$> (iImportedModules <$> curIF)
  es <- mapM definition =<< (toList <$> curDefs)
  return (Module m is (fix (object es)))

definition :: (QName,Definition) -> TCM ([MemberId],Exp)
definition (q,d) = do
  (_,ls) <- global q
  d <- instantiateFull d
  e <- defn ls (defType d) (defJSDef d) (theDef d)
  return (ls, e)

defn :: [MemberId] -> Type -> Maybe JSCode -> Defn -> TCM Exp
defn ls t (Just e) Axiom =
  return e
defn ls t Nothing Axiom =
  return Undefined
defn ls t (Just e) (Function {}) =
  return e
defn ls t _ (Function { funProjection = Just i, funClauses = cls }) =
  return (curriedLambda (numPars cls)
    (Lookup (Local (LocalId 0)) (last ls)))
defn ls t _ (Function { funClauses = cls }) = do
  s <- isSingleton t
  case s of
    -- Inline and eta-expand expressions of singleton type
    Just e ->
      return (curriedLambda (arity t) e)
    -- Everything else we translate
    Nothing -> do
      cs <- mapM clause cls
      return (lambda cs)
defn ls t (Just e) (Primitive {}) =
  return e
defn ls t _ (Primitive {}) =
  return Undefined
defn ls t _ (Datatype {}) =
  return emp
defn ls t (Just e) (Constructor {}) =
  return e
defn ls t _ (Constructor { conData = p, conPars = nc }) = do
  np <- return (arity t - nc)
  d <- getConstInfo p
  case theDef d of
    Record { recFields = flds } ->
      return (curriedLambda np (Object (fromList
        (zip [ jsMember (qnameName (unArg fld)) | fld <- flds ]
             [ Local (LocalId (np - i)) | i <- [1 .. np] ]))))
    _ ->
      return (curriedLambda (np + 1)
        (Apply (Lookup (Local (LocalId 0)) (last ls))
          [ Local (LocalId (np - i)) | i <- [0 .. np-1] ]))
defn ls t _ (Record {}) =
  return emp

-- Number of params in a function declaration

numPars :: [Clauses] -> Nat
numPars []                  = 0
numPars (Clauses _ c : _) = genericLength (clausePats c)

-- One clause in a function definition

clause :: Clauses -> TCM Case
clause (Clauses _ c) = do
  ps <- mapM (pattern . unArg) (clausePats c)
  (av,bv,es) <- return (mapping (map unArg (clausePats c)))
  e <- body (clauseBody c)
  return (Case ps (subst av es e))

-- Mapping from Agda variables to JS variables in a pattern.
-- If mapping ps = (av,bv,es) then av is the number of Agda variables,
-- bv is the number of JS variables, and es is a list of expressions,
-- where es[i] is the JS variable corresponding to Agda variable i.

mapping :: [Pattern] -> (Nat,Nat,[Exp])
mapping = foldr mapping' (0,0,[])

mapping' :: Pattern -> (Nat,Nat,[Exp]) -> (Nat,Nat,[Exp])
mapping' (VarP _)      (av,bv,es) = (av+1, bv+1, Local (LocalId bv) : es)
mapping' (DotP _)      (av,bv,es) = (av+1, bv+1, Local (LocalId bv) : es)
mapping' (ConP _ _ ps) (av,bv,es) = (av',bv'+1,es') where
  (av',bv',es') = foldr mapping' (av,bv,es) (map unArg ps)
mapping' (LitP _)      (av,bv,es) = (av, bv+1, es)

-- Not doing literal patterns yet

pattern :: Pattern -> TCM Patt
pattern (ConP q _ ps) = do
  l <- tag q
  ps <- mapM (pattern . unArg) ps
  return (Tagged l ps)
pattern _             = return VarPatt

tag :: QName -> TCM Tag
tag q = do
  l <- visitorName q
  c <- getConstInfo q
  case theDef c of
    (Constructor { conData = p }) -> do
      d <- getConstInfo p
      case (defJSDef d, theDef d) of
        (Just e, Datatype { dataCons = qs }) -> do
          ls <- mapM visitorName qs
          return (Tag l ls (\ x xs -> apply e (x:xs)))
        (Nothing, Datatype { dataCons = qs }) -> do
          ls <- mapM visitorName qs
          return (Tag l ls Apply)
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

visitorName :: QName -> TCM MemberId
visitorName q = do (m,ls) <- global q; return (last ls)

body :: ClauseBody -> TCM Exp
body (Body e)         = term e
body (Bind (Abs _ e)) = body e
body (NoBind e)       = body e
body (NoBody)         = return Undefined

term :: Term -> TCM Exp
term (Var   i as)         = do
  e <- return (Local (LocalId i))
  es <- args as
  return (curriedApply e es)
term (Lam   _ at)         = Lambda 1 <$> term (absBody at)
term (Lit   l)            = return (literal l)
term (Level l)            = term =<< reallyUnLevelView l
term (Def q as) = do
  d <- getConstInfo q
  case defJSDef d of
    -- Inline functions with an FFI definition
    Just e -> do
      es <- args as
      return (curriedApply e es)
    Nothing -> do
      s <- isSingleton (defType d)
      case s of
        -- Inline and eta-expand singleton types
        Just e ->
          return (curriedLambda (arity (defType d)) e)
        -- Everything else we leave non-inline
        Nothing -> do
          e <- qname q
          es <- args as
          return (curriedApply e es)
term (Con q as) = do
  d <- getConstInfo q
  case defJSDef d of
    -- Inline functions with an FFI definition
    Just e -> do
      es <- args as
      return (curriedApply e es)
    -- Everything else we leave non-inline
    Nothing -> do
      e <- qname q
      es <- args as
      return (curriedApply e es)
term (Pi    _ _)          = return (String "*")
term (Fun   _ _)          = return (String "*")
term (Sort  _)            = return (String "*")
term (MetaV _ _)          = return (Undefined)
term (DontCare)           = return (Undefined)

-- Check to see if a type is a singleton, and if so, return its only
-- member.  Singleton types are of the form T1 -> ... -> Tn -> T where
-- T is either a record with no fields, a datatype with one
-- no-argument constructor, a datatype with no constructors,
-- or (since this is a type-erasing translation) Set.

isSingleton :: Type -> TCM (Maybe Exp)
isSingleton t = case unEl t of
  Pi _ (Abs _ b) -> isSingleton b
  Fun _       b  -> isSingleton b
  Sort _         -> return (Just (String "*"))
  Def q as       -> do
    d <- getConstInfo q
    case (theDef d) of
      Datatype { dataPars = np, dataCons = [] } ->
        return (Just Undefined)
      Datatype { dataPars = np, dataCons = [p] } -> do
        c <- getConstInfo p
        case (arity (defType c) == np) of
          True -> Just <$> qname p
          False -> return (Nothing)
      Record { recCon = p, recFields = [] } ->
        Just <$> qname p
      _ -> return (Nothing)
  _              -> return (Nothing)

args :: Args -> TCM [Exp]
args = mapM (term . unArg)

qname :: QName -> TCM Exp
qname q = do
  (e,ls) <- global q
  return (foldl Lookup e ls)

literal :: Literal -> Exp
literal (LitInt    _ x) = Integer x
literal (LitFloat  _ x) = Double  x
literal (LitString _ x) = String  x
literal (LitChar   _ x) = Char    x
literal (LitQName  _ x) = String  (show x)

--------------------------------------------------
-- Writing out an ECMAScript module
--------------------------------------------------

writeModule :: Module -> TCM ()
writeModule m = do
  out <- outFile (modName m)
  liftIO (writeFile out (pretty 0 0 m))

compileDir :: TCM FilePath
compileDir = do
  mdir <- optCompileDir <$> commandLineOptions
  case mdir of
    Just dir -> return dir
    Nothing  -> __IMPOSSIBLE__

outFile :: GlobalId -> TCM FilePath
outFile m = do
  mdir <- compileDir
  let (fdir, fn) = splitFileName (jsFileName m)
  let dir = mdir </> fdir
      fp  = dir </> fn
  liftIO $ createDirectoryIfMissing True dir
  return fp

outFile_ :: TCM FilePath
outFile_ = do
  m <- curMName
  outFile (jsMod m)
