{-# LANGUAGE CPP            #-}

module Agda.Compiler.JS.Compiler where

import Prelude hiding ( null, writeFile )
import Control.Applicative
import Control.Monad.Reader ( liftIO )
import Control.Monad.Trans
import Data.List ( intercalate, genericLength, partition )
import Data.Maybe ( isJust )
import Data.Set ( Set, null, insert, difference, delete )
import Data.Traversable (traverse)
import Data.Map ( fromList, elems )
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Directory ( createDirectoryIfMissing )
import System.FilePath ( splitFileName, (</>) )

import Agda.Interaction.FindFile ( findFile, findInterfaceFile )
import Agda.Interaction.Imports ( isNewerThan )
import Agda.Interaction.Options ( optCompileDir )
import Agda.Syntax.Common ( Nat, unArg, namedArg, NameId(..) )
import Agda.Syntax.Concrete.Name ( projectRoot )
import Agda.Syntax.Abstract.Name
  ( ModuleName(MName), QName,
    mnameToConcrete,
    mnameToList, qnameName, qnameModule, isInModule, nameId )
import Agda.Syntax.Internal
  ( Name, Args, Type,
    conName,
    toTopLevelModuleName, arity, unEl, unAbs, nameFixity )
import Agda.Syntax.Literal ( Literal(LitNat,LitFloat,LitString,LitChar,LitQName,LitMeta) )
import Agda.Syntax.Fixity
import qualified Agda.Syntax.Treeless as T
import Agda.TypeChecking.Substitute ( absBody )
import Agda.TypeChecking.Level ( reallyUnLevelView )
import Agda.TypeChecking.Monad hiding (Global, Local)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Options ( setCommandLineOptions, commandLineOptions, reportSLn )
import Agda.TypeChecking.Reduce ( instantiateFull, normalise )
import Agda.TypeChecking.Substitute (TelV(..))
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Pretty
import Agda.Utils.FileName ( filePath )
import Agda.Utils.Function ( iterate' )
import Agda.Utils.Maybe
import Agda.Utils.Monad ( (<$>), (<*>), ifM )
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.IO.Directory
import Agda.Utils.IO.UTF8 ( writeFile )
import qualified Agda.Utils.HashMap as HMap

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.EliminateLiteralPatterns
import Agda.Compiler.Treeless.GuardsToPrims

import Agda.Compiler.JS.Syntax
  ( Exp(Self,Local,Global,Undefined,String,Char,Integer,Double,Lambda,Object,Apply,Lookup,If,BinOp,PlainJS),
    LocalId(LocalId), GlobalId(GlobalId), MemberId(MemberId), Export(Export), Module(Module),
    modName, expName, uses )
import Agda.Compiler.JS.Substitution
  ( curriedLambda, curriedApply, emp, subst, apply )
import qualified Agda.Compiler.JS.Pretty as JSPretty

import Paths_Agda

#include "undefined.h"
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

--------------------------------------------------
-- Entry point into the compiler
--------------------------------------------------

compilerMain :: Interface -> TCM ()
compilerMain mainI = inCompilerEnv mainI $ do
  doCompile IsMain mainI $ do
    compile
  copyRTEModules

compile :: IsMain -> Interface -> TCM ()
compile isMain i = do
  ifM uptodate noComp $ do
    yesComp
    writeModule =<< curModule isMain
  where
  uptodate = liftIO =<< (isNewerThan <$> outFile_ <*> ifile)
  ifile    = maybe __IMPOSSIBLE__ filePath <$>
               (findInterfaceFile . toTopLevelModuleName =<< curMName)
  noComp   = reportSLn "compile.js" 2 . (++ " : no compilation is needed.") . prettyShow =<< curMName
  yesComp  = reportSLn "compile.js" 1 . (`repl` "Compiling <<0>> in <<1>> to <<2>>") =<<
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
  modNm <- topLevelModuleName (qnameModule q)
  let
    qms = mnameToList $ qnameModule q
    nm = map jsMember (drop (length $ mnameToList modNm) qms ++ [qnameName q])
  if modNm == i
    then return (Self, nm)
    else return (Global (jsMod modNm), nm)

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
  Object m | flatName `Map.member` m -> False
  Lambda{} -> False
  _        -> True

isEmptyObject :: Export -> Bool
isEmptyObject (Export _ e) = case e of
  Object m -> Map.null m
  Lambda{} -> True
  _        -> False

insertAfter :: Set [MemberId] -> Export -> [Export] -> [Export]
insertAfter us e []                 = [e]
insertAfter us e (f:fs) | null us   = e : f : fs
insertAfter us e (f:fs) | otherwise = f : insertAfter (delete (expName f) us) e fs

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

curModule :: IsMain -> TCM Module
curModule isMain = do
  kit <- coinductionKit
  m <- (jsMod <$> curMName)
  is <- map jsMod <$> (map fst . iImportedModules <$> curIF)
  es <- catMaybes <$> (mapM (definition kit) =<< (sortDefs <$> curDefs))
  return $ Module m (reorder es) main
  where
    main = case isMain of
      IsMain -> Just $ Apply (Lookup Self $ MemberId "main") [Lambda 1 emp]
      NotMain -> Nothing

definition :: Maybe CoinductionKit -> (QName,Definition) -> TCM (Maybe Export)
definition kit (q,d) = do
  reportSDoc "compile.js" 10 $ text "compiling def:" <+> prettyTCM q
  (_,ls) <- global q
  d <- instantiateFull d

  definition' kit q d (defType d) ls

definition' :: Maybe CoinductionKit -> QName -> Definition -> Type -> [MemberId] -> TCM (Maybe Export)
definition' kit q d t ls =
  case theDef d of
    -- coinduction
    Constructor{} | Just q == (nameOfSharp <$> kit) -> do
      return Nothing
    Function{} | Just q == (nameOfFlat <$> kit) -> do
      ret $ Lambda 1 $ Apply (Lookup (local 0) flatName) []

    Axiom | Just e <- defJSDef d -> plainJS e
    Axiom | otherwise -> ret Undefined

    Function{} | Just e <- defJSDef d -> plainJS e
    Function{} | otherwise -> do

      reportSDoc "compile.js" 5 $ text "compiling fun:" <+> prettyTCM q
      caseMaybeM (toTreeless q) (pure Nothing) $ \ treeless -> do
        funBody <- eliminateLiteralPatterns $ convertGuards $ treeless
        reportSDoc "compile.js" 30 $ text " compiled treeless fun:" <+> pretty funBody
        funBody' <- compileTerm funBody
        reportSDoc "compile.js" 30 $ text " compiled JS fun:" <+> (text . show) funBody'
        return $ Just $ Export ls funBody'

    Primitive{primName = p} | p `Set.member` primitives ->
      plainJS $ "agdaRTS." ++ p
    Primitive{} | Just e <- defJSDef d -> plainJS e
    Primitive{} | otherwise -> ret Undefined

    Datatype{} -> ret emp
    Record{} -> return Nothing

    Constructor{} | Just e <- defJSDef d -> plainJS e
    Constructor{conData = p, conPars = nc} | otherwise -> do
      np <- return (arity t - nc)
      d <- getConstInfo p
      case theDef d of
        Record { recFields = flds } ->
          ret (curriedLambda np (Object (fromList
            ( (last ls , Lambda 1
                 (Apply (Lookup (Local (LocalId 0)) (last ls))
                   [ Local (LocalId (np - i)) | i <- [0 .. np-1] ]))
            : (zip [ jsMember (qnameName (unArg fld)) | fld <- flds ]
                 [ Local (LocalId (np - i)) | i <- [1 .. np] ])))))
        _ ->
          ret (curriedLambda (np + 1)
            (Apply (Lookup (Local (LocalId 0)) (last ls))
              [ Local (LocalId (np - i)) | i <- [0 .. np-1] ]))

    AbstractDefn -> __IMPOSSIBLE__
  where
    ret = return . Just . Export ls
    plainJS = return . Just . Export ls . PlainJS

compileTerm :: T.TTerm -> TCM Exp
compileTerm t = do
  kit <- coinductionKit
  compileTerm' kit t

compileTerm' :: Maybe CoinductionKit -> T.TTerm -> TCM Exp
compileTerm' kit t = go t
  where
    go :: T.TTerm -> TCM Exp
    go t = case t of
      T.TVar x -> return $ Local $ LocalId x
      T.TDef q -> do
        d <- getConstInfo q
        case theDef d of
          -- Datatypes and records are erased
          Datatype {} -> return (String "*")
          Record {} -> return (String "*")
          _ -> qname q
      T.TApp (T.TCon q) [x] | Just q == (nameOfSharp <$> kit) -> do
        x <- go x
        return $ Object $ Map.fromList [(flatName, Lambda 0 x)]
      T.TApp t xs -> curriedApply <$> go t <*> mapM go xs
      T.TLam t -> Lambda 1 <$> go t
      -- TODO This is not a lazy let, but it should be...
      T.TLet t e -> apply <$> (Lambda 1 <$> go e) <*> traverse go [t]
      T.TLit l -> return $ literal l
      T.TCon q -> do
        d <- getConstInfo q
        qname q
      T.TCase sc (T.CTData dt) def alts -> do
        dt <- getConstInfo dt
        alts' <- traverse compileAlt alts
        let obj = Object $ Map.fromList alts'
        case (theDef dt, defJSDef dt) of
          (_, Just e) -> do
            return $ apply (PlainJS e) [Local (LocalId sc), obj]
          (Record{}, _) -> do
            memId <- visitorName $ recCon $ theDef dt
            return $ apply (Lookup (Local $ LocalId sc) memId) [obj]
          (Datatype{}, _) -> do
            return $ curriedApply (Local (LocalId sc)) [obj]
          _ -> __IMPOSSIBLE__
      T.TCase _ _ _ _ -> __IMPOSSIBLE__

      T.TPrim p -> return $ compilePrim p
      T.TUnit -> unit
      T.TSort -> unit
      T.TErased -> unit
      T.TError T.TUnreachable -> return Undefined

    unit = return $ Integer 0

compilePrim :: T.TPrim -> Exp
compilePrim p =
  case p of
    T.PIf -> curriedLambda 3 $ If (local 2) (local 1) (local 0)
    T.PEqI -> binOp "agdaRTS.uprimIntegerEqual"
    T.PEqF -> binOp "agdaRTS.uprimFloatEquality"
    T.PEqQ -> binOp "agdaRTS.uprimQNameEquality"
    p | T.isPrimEq p -> curriedLambda 2 $ BinOp (local 1) "===" (local 0)
    T.PGeq -> binOp "agdaRTS.uprimIntegerGreaterOrEqualThan"
    T.PLt -> binOp "agdaRTS.uprimIntegerLessThan"
    T.PAdd -> binOp "agdaRTS.uprimIntegerPlus"
    T.PSub -> binOp "agdaRTS.uprimIntegerMinus"
    T.PMul -> binOp "agdaRTS.uprimIntegerMultiply"
    T.PSeq -> binOp "agdaRTS.primSeq"
    _ -> __IMPOSSIBLE__
  where binOp js = curriedLambda 2 $ apply (PlainJS js) [local 1, local 0]


compileAlt :: T.TAlt -> TCM (MemberId, Exp)
compileAlt a = case a of
  T.TACon con ar body -> do
    memId <- visitorName con
    body <- Lambda ar <$> compileTerm body
    return (memId, body)
  _ -> __IMPOSSIBLE__

visitorName :: QName -> TCM MemberId
visitorName q = do (m,ls) <- global q; return (last ls)

flatName :: MemberId
flatName = MemberId "flat"

local :: Nat -> Exp
local = Local . LocalId

qname :: QName -> TCM Exp
qname q = do
  (e,ls) <- global q
  return (foldl Lookup e ls)

literal :: Literal -> Exp
literal l = case l of
  (LitNat    _ x) -> Integer x
  (LitFloat  _ x) -> Double  x
  (LitString _ x) -> String  x
  (LitChar   _ x) -> Char    x
  (LitQName  _ x) -> litqname x
  LitMeta{}       -> __IMPOSSIBLE__

litqname :: QName -> Exp
litqname q =
  Object $ Map.fromList
    [ (mem "id", Integer $ fromIntegral n)
    , (mem "moduleId", Integer $ fromIntegral m)
    , (mem "name", String $ show q)
    , (mem "fixity", litfixity fx)]
  where
    mem = MemberId
    NameId n m = nameId $ qnameName q
    fx = theFixity $ nameFixity $ qnameName q

    litfixity :: Fixity -> Exp
    litfixity fx = Object $ Map.fromList
      [ (mem "assoc", litAssoc $ fixityAssoc fx)
      , (mem "prec", litPrec $ fixityLevel fx)]

    -- TODO this will probably not work well together with the necessary FFI bindings
    litAssoc NonAssoc   = String "NonAssoc"
    litAssoc LeftAssoc  = String "LeftAssoc"
    litAssoc RightAssoc = String "RightAssoc"

    litPrec Unrelated   = String "Unrelated"
    litPrec (Related l) = Integer l

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


copyRTEModules :: TCM ()
copyRTEModules = do
  dataDir <- lift getDataDir
  let srcDir = dataDir </> "JS"
  (lift . copyDirContent srcDir) =<< compileDir

-- | Primitives implemented in the JS Agda RTS.
primitives :: Set String
primitives = Set.fromList
  [ "primExp"
  , "primFloatDiv"
  , "primFloatEquality"
  , "primFloatNumericalEquality"
  , "primFloatNumericalLess"
  , "primFloatNegate"
  , "primFloatMinus"
  , "primFloatPlus"
  , "primFloatSqrt"
  , "primFloatTimes"
  , "primNatMinus"
  , "primShowFloat"
  , "primShowInteger"
  , "primSin"
  , "primCos"
  , "primTan"
  , "primASin"
  , "primACos"
  , "primATan"
  , "primATan2"
  , "primShowQName"
  , "primQNameEquality"
  ]
