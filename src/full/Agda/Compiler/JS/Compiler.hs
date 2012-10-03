{-# LANGUAGE CPP #-}

module Agda.Compiler.JS.Compiler where

import Prelude hiding ( null, writeFile )
import Control.Monad.Reader ( liftIO )
import Control.Monad.State ( get, put )
import Data.List ( intercalate, map, filter, isPrefixOf, concat, genericDrop, genericLength, partition )
import Data.Set ( Set, empty, null, insert, difference, delete )
import Data.Map ( Map, fold, singleton, fromList, toList, toAscList, insertWith, elems )
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Directory ( createDirectoryIfMissing )
import System.FilePath ( pathSeparator, splitFileName, (</>) )

import Agda.Interaction.FindFile ( findFile, findInterfaceFile )
import Agda.Interaction.Imports ( isNewerThan )
import Agda.Interaction.Options ( optCompileDir )
import Agda.Syntax.Common ( Nat, Arg, unArg )
import Agda.Syntax.Concrete.Name ( projectRoot )
import Agda.Syntax.Abstract.Name
  ( ModuleName(MName), QName(QName),
    mnameToList, qnameName, qnameModule, isInModule, nameId )
import Agda.Syntax.Internal
  ( Name, Args, Type,
    Clause(Clause), Pattern(VarP,DotP,LitP,ConP), Abs(Abs),
    ClauseBody(Body,NoBody,Bind),
    Term(Var,Lam,Lit,Level,Def,Con,Pi,Sort,MetaV,DontCare,Shared),
    derefPtr,
    toTopLevelModuleName, clausePats, clauseBody, arity, unEl, unAbs )
import Agda.TypeChecking.Substitute ( absBody )
import Agda.Syntax.Literal ( Literal(LitInt,LitFloat,LitString,LitChar,LitQName) )
import Agda.TypeChecking.Level ( reallyUnLevelView )
import Agda.TypeChecking.Monad
  ( TCM, Definition(Defn), Definitions, Interface,
    JSCode, Defn(Record,Datatype,Constructor,Primitive,Function,Axiom),
    iModuleName, iImportedModules, theDef, getConstInfo, typeOfConst,
    ignoreAbstractMode, miInterface, getVisitedModules,
    defName, defType, funClauses, funProjection,
    dataPars, dataIxs, dataClause, dataCons,
    conPars, conData, conSrcCon,
    recClause, recCon, recFields, recPars, recNamedCon,
    primClauses, defJSDef )
import Agda.TypeChecking.Monad.Options ( setCommandLineOptions, commandLineOptions, reportSLn )
import Agda.TypeChecking.Reduce ( instantiateFull, normalise )
import Agda.Utils.FileName ( filePath )
import Agda.Utils.Function ( iterate' )
import Agda.Utils.Monad ( (<$>), (<*>), localState, ifM )
import Agda.Utils.IO.UTF8 ( writeFile )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import qualified Agda.Utils.HashMap as HMap
import Agda.Compiler.MAlonzo.Misc ( curDefs, curIF, curMName, setInterface )
import Agda.Compiler.MAlonzo.Primitives ( repl )

import Agda.Compiler.JS.Syntax
  ( Exp(Self,Local,Global,Undefined,String,Char,Integer,Double,Lambda,Object,Apply,Lookup),
    LocalId(LocalId), GlobalId(GlobalId), MemberId(MemberId), Export(Export), Module(Module),
    modName, expName, uses )
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
  localState $ do

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
jsFileName (GlobalId ms) = intercalate "." ms ++ ".js"

jsMember :: Name -> MemberId
jsMember n =
  -- Anonymous fields are used for where clauses,
  -- and they're all given the concrete name "_",
  -- so we disambiguate them using their name id.
  case show n of
    "_" -> MemberId ("_" ++ show (nameId n))
    l   -> MemberId l

-- Rather annoyingly, the anonymous construtor of a record R in module M
-- is given the name M.recCon, but a named constructor C
-- is given the name M.R.C, sigh. This causes a lot of hoop-jumping
-- in the map from Agda names to JS names, which we patch by renaming
-- anonymous constructors to M.R.record.

global' :: QName -> TCM (Exp,[MemberId])
global' q = do
  i <- iModuleName <$> curIF
  is <- filter (isInModule q) <$> map (iModuleName . miInterface) <$> elems <$> getVisitedModules
  case is of
    [] -> __IMPOSSIBLE__
    _ -> let
        seg = maximum (map (length . mnameToList) is)
        ms = mnameToList (qnameModule q)
        m = MName (take seg ms)
        ls = map jsMember (drop seg ms ++ [qnameName q])
      in case (m == i) of
        True -> return (Self, ls)
        False -> return (Global (jsMod m), ls)

global :: QName -> TCM (Exp,[MemberId])
global q = do
  d <- getConstInfo q
  case d of
    Defn { theDef = Constructor { conData = p } } -> do
      e <- getConstInfo p
      case e of
        Defn { theDef = Record { recNamedCon = False } } -> do
          (m,ls) <- global' p
          return (m, ls ++ [MemberId "record"])
        _ -> global' (defName d)
    _ -> global' (defName d)

-- Reorder a list of exports to ensure def-before-use.
-- Note that this can diverge in the case when there is no such reordering.

-- Only top-level values are evaluated before definitions are added to the
-- module, so we put those last, ordered in dependency order. There can't be
-- any recursion between top-level values (unless termination checking has been
-- disabled and someone's written a non-sensical program), so reordering will
-- terminate.

reorder :: [Export] -> [Export]
reorder es = datas ++ funs ++ reorder' (Set.fromList $ map expName $ datas ++ funs) vals
  where
    (vs, funs)    = partition isTopLevelValue es
    (datas, vals) = partition isEmptyObject vs

reorder' :: Set [MemberId] -> [Export] -> [Export]
reorder' defs [] = []
reorder' defs (e : es) =
  let us = uses e `difference` defs in
  case null us of
    True -> e : (reorder' (insert (expName e) defs) es)
    False -> reorder' defs (insertAfter us e es)

isTopLevelValue :: Export -> Bool
isTopLevelValue (Export _ e) = case e of
  Lambda{} -> False
  _        -> True

isEmptyObject :: Export -> Bool
isEmptyObject (Export _ e) = case e of
  Object m -> Map.null m
  _        -> False

insertAfter :: Set [MemberId] -> Export -> [Export] -> [Export]
insertAfter us e []                 = [e]
insertAfter us e (f:fs) | null us   = e : f : fs
insertAfter us e (f:fs) | otherwise = f : insertAfter (delete (expName f) us) e fs

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

curModule :: TCM Module
curModule = do
  m <- (jsMod <$> curMName)
  is <- map jsMod <$> (iImportedModules <$> curIF)
  es <- mapM definition =<< (HMap.toList <$> curDefs)
  return (Module m (reorder es))

definition :: (QName,Definition) -> TCM Export
definition (q,d) = do
  (_,ls) <- global q
  d <- instantiateFull d
  e <- defn q ls (defType d) (defJSDef d) (theDef d)
  return (Export ls e)

defn :: QName -> [MemberId] -> Type -> Maybe JSCode -> Defn -> TCM Exp
defn q ls t (Just e) Axiom =
  return e
defn q ls t Nothing Axiom = do
  t <- normalise t
  s <- isSingleton t
  case s of
    -- Inline and eta-expand postulates of singleton type
    Just e ->
      return (curriedLambda (arity t) e)
    -- Everything else we leave undefined
    Nothing ->
      return Undefined
defn q ls t (Just e) (Function {}) =
  return e
defn q ls t Nothing (Function { funProjection = proj, funClauses = cls }) = do
  t <- normalise t
  s <- isSingleton t
  cs <- mapM clause cls
  case s of
    -- Inline and eta-expand expressions of singleton type
    Just e ->
      return (curriedLambda (arity t) e)
    Nothing -> case proj of
      Just (p,i) -> do
        d <- getConstInfo p
        case theDef d of
          -- For projections from records we use a field lookup
          Record { recFields = flds } | q `elem` map unArg flds ->
            return (curriedLambda (numPars cls)
              (Lookup (Local (LocalId 0)) (last ls)))
          _ ->
            -- For anything else we generate code, after adding (i-1) dummy lambdas
            return (dummyLambda (i-1) (lambda cs))
      Nothing ->
        return (lambda cs)
defn q ls t (Just e) (Primitive {}) =
  return e
defn q ls t _ (Primitive {}) =
  return Undefined
defn q ls t _ (Datatype {}) =
  return emp
defn q ls t (Just e) (Constructor {}) =
  return e
defn q ls t _ (Constructor { conData = p, conPars = nc }) = do
  np <- return (arity t - nc)
  d <- getConstInfo p
  case theDef d of
    Record { recFields = flds } ->
      return (curriedLambda np (Object (fromList
        ( (last ls , Lambda 1
             (Apply (Lookup (Local (LocalId 0)) (last ls))
               [ Local (LocalId (np - i)) | i <- [0 .. np-1] ]))
        : (zip [ jsMember (qnameName (unArg fld)) | fld <- flds ]
             [ Local (LocalId (np - i)) | i <- [1 .. np] ])))))
    _ ->
      return (curriedLambda (np + 1)
        (Apply (Lookup (Local (LocalId 0)) (last ls))
          [ Local (LocalId (np - i)) | i <- [0 .. np-1] ]))
defn q ls t _ (Record {}) =
  return emp

-- Number of params in a function declaration

numPars :: [Clause] -> Nat
numPars []      = 0
numPars (c : _) = genericLength (clausePats c)

-- One clause in a function definition

clause :: Clause -> TCM Case
clause c = do
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
        (Just e, Record {}) -> do
          return (Tag l [l] (\ x xs -> apply e (x:xs)))
        (Nothing, Record {}) -> do
          return (Tag l [l] Apply)
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

visitorName :: QName -> TCM MemberId
visitorName q = do (m,ls) <- global q; return (last ls)

body :: ClauseBody -> TCM Exp
body (Body e) = term e
body (Bind b) = body (unAbs b)
body (NoBody) = return Undefined

term :: Term -> TCM Exp
term (Var   i as)         = do
  e <- return (Local (LocalId i))
  es <- args Nothing as
  return (curriedApply e es)
term (Lam   _ at)         = Lambda 1 <$> term (absBody at)
term (Lit   l)            = return (literal l)
term (Level l)            = term =<< reallyUnLevelView l
term (Shared p)           = term $ derefPtr p
term (Def q as) = do
  d <- getConstInfo q
  case theDef d of
    -- Datatypes and records are erased
    Datatype {} -> return (String "*")
    Record {} -> return (String "*")
    _ -> case defJSDef d of
      -- Inline functions with an FFI definition
      Just e -> do
        es <- args (defProjection d) as
        return (curriedApply e es)
      Nothing -> do
        t <- normalise (defType d)
        s <- isSingleton t
        case s of
          -- Inline and eta-expand singleton types
          Just e ->
            return (curriedLambda (arity t) e)
          -- Everything else we leave non-inline
          Nothing -> do
            e <- qname q
            es <- args (defProjection d) as
            return (curriedApply e es)
term (Con q as) = do
  d <- getConstInfo q
  case defJSDef d of
    -- Inline functions with an FFI definition
    Just e -> do
      es <- args Nothing as
      return (curriedApply e es)
    -- Everything else we leave non-inline
    Nothing -> do
      e <- qname q
      es <- args Nothing as
      return (curriedApply e es)
term (Pi    _ _)          = return (String "*")
term (Sort  _)            = return (String "*")
term (MetaV _ _)          = return (Undefined)
term (DontCare _)         = return (Undefined)

-- Check to see if a type is a singleton, and if so, return its only
-- member.  Singleton types are of the form T1 -> ... -> Tn -> T where
-- T is either a record with no fields, a datatype with one
-- no-argument constructor, a datatype with no constructors,
-- or (since this is a type-erasing translation) Set.

isSingleton :: Type -> TCM (Maybe Exp)
isSingleton t = case unEl t of
  Pi _ b         -> isSingleton (unAbs b)
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

defProjection :: Definition -> Maybe (QName, Int)
defProjection Defn { theDef = Function { funProjection = p } } = p
defProjection _                                                = Nothing

args :: Maybe(QName, Int) -> Args -> TCM [Exp]
args Nothing as =
  mapM (term . unArg) as
args (Just (q,i)) as = do
  es <- mapM (term . unArg) as
  return (replicate (i-1) Undefined ++ es)

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

dummyLambda :: Int -> Exp -> Exp
dummyLambda n = iterate' n (Lambda 0)

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
