{-# LANGUAGE CPP            #-}

module Agda.Compiler.JS.Compiler where

import Prelude hiding ( null, writeFile )
import Control.Monad.Reader ( liftIO )
import Control.Monad.Trans
import Data.List ( intercalate, genericLength, partition )
import Data.Maybe ( isJust )
import Data.Set ( Set, null, insert, difference, delete )
import Data.Map ( fromList, elems )
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Directory ( createDirectoryIfMissing )
import System.FilePath ( splitFileName, (</>) )

import Agda.Interaction.FindFile ( findFile, findInterfaceFile )
import Agda.Interaction.Imports ( isNewerThan )
import Agda.Interaction.Options ( optCompileDir )
import Agda.Syntax.Common ( Nat, unArg, namedArg )
import Agda.Syntax.Concrete.Name ( projectRoot )
import Agda.Syntax.Abstract.Name
  ( ModuleName(MName), QName,
    mnameToConcrete,
    mnameToList, qnameName, qnameModule, isInModule, nameId )
import Agda.Syntax.Internal
  ( Name, Args, Type,
    Clause, Pattern, Pattern'(VarP,DotP,LitP,ConP,ProjP),
    Term(Var,Lam,Lit,Level,Def,Con,Pi,Sort,MetaV,DontCare,Shared),
    unSpine, allApplyElims,
    conName,
    derefPtr,
    toTopLevelModuleName, clausePats, arity, unEl, unAbs )
import Agda.Syntax.Internal.Pattern ( unnumberPatVars )
import qualified Agda.Syntax.Treeless as T
import Agda.TypeChecking.Substitute ( absBody )
import Agda.Syntax.Literal ( Literal(LitNat,LitFloat,LitString,LitChar,LitQName,LitMeta) )
import Agda.TypeChecking.Level ( reallyUnLevelView )
import Agda.TypeChecking.Monad hiding (Global, Local)
import Agda.TypeChecking.Monad.Options ( setCommandLineOptions, commandLineOptions, reportSLn )
import Agda.TypeChecking.Reduce ( instantiateFull, normalise )
import Agda.TypeChecking.Pretty
import Agda.Utils.FileName ( filePath )
import Agda.Utils.Function ( iterate' )
import Agda.Utils.Maybe
import Agda.Utils.Monad ( (<$>), (<*>), ifM )
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.IO.UTF8 ( writeFile )
import qualified Agda.Utils.HashMap as HMap

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.EliminateLiteralPatterns
import Agda.Compiler.Treeless.GuardsToPrims

import Agda.Compiler.JS.Syntax
  ( Exp(Self,Local,Global,Undefined,String,Char,Integer,Double,Lambda,Object,Apply,Lookup,If,BinOp),
    LocalId(LocalId), GlobalId(GlobalId), MemberId(MemberId), Export(Export), Module(Module),
    modName, expName, uses )
import Agda.Compiler.JS.Substitution
  ( curriedLambda, curriedApply, emp, subst, apply )
import qualified Agda.Compiler.JS.Pretty as JSPretty

#include "undefined.h"
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

--------------------------------------------------
-- Entry point into the compiler
--------------------------------------------------

compilerMain :: Interface -> TCM ()
compilerMain mainI = inCompilerEnv mainI $ do
  doCompile IsMain mainI $ \_ -> compile

compile :: Interface -> TCM ()
compile i = do
  ifM uptodate noComp $ do
    yesComp
    writeModule =<< curModule
  where
  uptodate = liftIO =<< (isNewerThan <$> outFile_ <*> ifile)
  ifile    = maybe __IMPOSSIBLE__ filePath <$>
               (findInterfaceFile . toTopLevelModuleName =<< curMName)
  noComp   = reportSLn "" 1 . (++ " : no compilation is needed.") . prettyShow =<< curMName
  yesComp  = reportSLn "" 1 . (`repl` "Compiling <<0>> in <<1>> to <<2>>") =<<
             sequence [prettyShow <$> curMName, ifile, outFile_] :: TCM ()

--------------------------------------------------
-- Naming
--------------------------------------------------

prefix :: [Char]
prefix = "jAgda"

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
  is <- map jsMod <$> (map fst . iImportedModules <$> curIF)
  es <- catMaybes <$> (mapM definition =<< (HMap.toList <$> curDefs))
  return (Module m (reorder es))

definition :: (QName,Definition) -> TCM (Maybe Export)
definition (q,d) = do
  (_,ls) <- global q
  d <- instantiateFull d
  fmap (Export ls) <$> defn q ls (defType d) (defJSDef d) (theDef d)

defn :: QName -> [MemberId] -> Type -> Maybe JSCode -> Defn -> TCM (Maybe Exp)
defn q ls t (Just e) Axiom =
  return $ Just e
defn q ls t Nothing Axiom =
  return $ Just Undefined
defn q ls t (Just e) (Function {}) =
  return $ Just e
defn q ls t Nothing (Function {}) = do
  reportSDoc "js.compile" 5 $ text "compiling fun:" <+> prettyTCM q
  caseMaybeM (toTreeless q) (pure Nothing) $ \ treeless -> do
    let funBody = eliminateLiteralPatterns $ convertGuards $ treeless
    reportSDoc "js.compile" 30 $ text " compiled treeless fun:" <+> (text . show) funBody
    funBody' <- compileTerm funBody
    reportSDoc "js.compile" 30 $ text " compiled JS fun:" <+> (text . show) funBody'
    return $ Just funBody'
defn q ls t (Just e) (Primitive {}) =
  return $ Just e
defn q ls t _ (Primitive {}) =
  return $ Just Undefined
defn q ls t _ (Datatype {}) =
  return $ Just emp
defn q ls t (Just e) (Constructor {}) =
  return $ Just e
defn q ls t _ (Constructor { conData = p, conPars = nc }) = do
  np <- return (arity t - nc)
  d <- getConstInfo p
  case theDef d of
    Record { recFields = flds } ->
      return $ Just (curriedLambda np (Object (fromList
        ( (last ls , Lambda 1
             (Apply (Lookup (Local (LocalId 0)) (last ls))
               [ Local (LocalId (np - i)) | i <- [0 .. np-1] ]))
        : (zip [ jsMember (qnameName (unArg fld)) | fld <- flds ]
             [ Local (LocalId (np - i)) | i <- [1 .. np] ])))))
    _ ->
      return $ Just (curriedLambda (np + 1)
        (Apply (Lookup (Local (LocalId 0)) (last ls))
          [ Local (LocalId (np - i)) | i <- [0 .. np-1] ]))
defn q ls t _ (Record {}) =
  return $ Just emp


compileTerm :: T.TTerm -> TCM Exp
compileTerm term = do
  case term of
    T.TVar x -> return $ Local $ LocalId x
    T.TDef q -> do
      d <- getConstInfo q
      case theDef d of
        -- Datatypes and records are erased
        Datatype {} -> return (String "*")
        Record {} -> return (String "*")
        _ -> qname q
    T.TApp t xs -> curriedApply <$> compileTerm t <*> mapM compileTerm xs
    T.TLam t -> Lambda 1 <$> compileTerm t
    T.TLit l -> return $ literal l
    T.TCon q -> do
      d <- getConstInfo q
      qname q
    T.TCase sc (T.CTData dt) def alts -> do
      dt <- getConstInfo dt
      alts' <- traverse compileAlt alts
      let obj = Object $ Map.fromList alts'
      case defJSDef dt of
        Just e -> do
          return $ apply e [Local (LocalId sc), obj]
        Nothing -> do
          return $ curriedApply (Local (LocalId sc)) [obj]

    T.TPrim p -> return $ compilePrim p
    T.TUnit -> unit
    T.TSort -> unit
    T.TErased -> unit
    _ -> error $ show term --__IMPOSSIBLE__

  where
    unit = return $ Integer 0

compilePrim :: T.TPrim -> Exp
compilePrim p =
  case p of
    T.PIf -> curriedLambda 3 $ If (local 2) (local 1) (local 0)
    T.PEq -> curriedLambda 2 $ BinOp (local 1) "===" (local 0)
    _ -> __IMPOSSIBLE__


compileAlt :: T.TAlt -> TCM (MemberId, Exp)
compileAlt a = case a of
  T.TACon con ar body -> do
    memId <- visitorName con
    body <- Lambda ar <$> compileTerm body
    return (memId, body)
  _ -> error (show a) --__IMPOSSIBLE__

visitorName :: QName -> TCM MemberId
visitorName q = do (m,ls) <- global q; return (last ls)

local :: Nat -> Exp
local = Local . LocalId

qname :: QName -> TCM Exp
qname q = do
  (e,ls) <- global q
  return (foldl Lookup e ls)

literal :: Literal -> Exp
literal (LitNat    _ x) = Integer x
literal (LitFloat  _ x) = Double  x
literal (LitString _ x) = String  x
literal (LitChar   _ x) = Char    x
literal (LitQName  _ x) = String  (show x)
literal LitMeta{}       = __IMPOSSIBLE__

--------------------------------------------------
-- Writing out an ECMAScript module
--------------------------------------------------

writeModule :: Module -> TCM ()
writeModule m = do
  out <- outFile (modName m)
  liftIO (writeFile out (JSPretty.pretty 0 0 m))

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
