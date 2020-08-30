module Agda.Compiler.JS.Compiler where

import Prelude hiding ( null, writeFile )
import Control.Monad.Trans

import Data.Char ( isSpace )
import Data.List ( intercalate, partition )
import Data.Set ( Set, null, insert, difference, delete )
import Data.Map ( fromList )
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Text as T

import System.Directory ( createDirectoryIfMissing )
import System.FilePath ( splitFileName, (</>) )

import Paths_Agda

import Agda.Interaction.Options
import Agda.Interaction.Imports ( isNewerThan )

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name ( isNoName )
import Agda.Syntax.Abstract.Name
  ( ModuleName, QName,
    mnameToList, qnameName, qnameModule, nameId )
import Agda.Syntax.Internal
  ( Name, Type
  , arity, nameFixity, unDom )
import Agda.Syntax.Literal ( Literal(..) )
import qualified Agda.Syntax.Treeless as T

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce ( instantiateFull )
import Agda.TypeChecking.Substitute as TC ( TelV(..), raise, subst )
import Agda.TypeChecking.Pretty
import Agda.Utils.Function ( iterate' )
import Agda.Utils.List ( headWithDefault )
import Agda.Utils.Maybe
import Agda.Utils.Monad ( ifM, when )
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.IO.Directory
import Agda.Utils.IO.UTF8 ( writeFile )

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.EliminateDefaults
import Agda.Compiler.Treeless.EliminateLiteralPatterns
import Agda.Compiler.Treeless.GuardsToPrims
import Agda.Compiler.Treeless.Erase ( computeErasedConstructorArgs )
import Agda.Compiler.Treeless.Subst ()
import Agda.Compiler.Backend (Backend(..), Backend'(..), Recompile(..))

import Agda.Compiler.JS.Syntax
  ( Exp(Self,Local,Global,Undefined,Null,String,Char,Integer,Double,Lambda,Object,Array,Apply,Lookup,If,BinOp,PlainJS),
    LocalId(LocalId), GlobalId(GlobalId), MemberId(MemberId,MemberIndex), Export(Export), Module(Module), Comment(Comment),
    modName, expName, uses )
import Agda.Compiler.JS.Substitution
  ( curriedLambda, curriedApply, emp, apply )
import qualified Agda.Compiler.JS.Pretty as JSPretty

import Agda.Utils.Impossible (__IMPOSSIBLE__)

--------------------------------------------------
-- Entry point into the compiler
--------------------------------------------------

jsBackend :: Backend
jsBackend = Backend jsBackend'

jsBackend' :: Backend' JSOptions JSOptions JSModuleEnv Module (Maybe Export)
jsBackend' = Backend'
  { backendName           = jsBackendName
  , backendVersion        = Nothing
  , options               = defaultJSOptions
  , commandLineFlags      = jsCommandLineFlags
  , isEnabled             = optJSCompile
  , preCompile            = jsPreCompile
  , postCompile           = jsPostCompile
  , preModule             = jsPreModule
  , postModule            = jsPostModule
  , compileDef            = jsCompileDef
  , scopeCheckingSuffices = False
  , mayEraseType          = const $ return True
      -- Andreas, 2019-05-09, see issue #3732.
      -- If you want to use JS data structures generated from Agda
      -- @data@/@record@, you might want to tell the treeless compiler
      -- not to erase these types even if they have no content,
      -- to get a stable interface.
  }

--- Options ---

data JSOptions = JSOptions
  { optJSCompile :: Bool
  , optJSOptimize :: Bool
  , optJSMinify :: Bool
  }

defaultJSOptions :: JSOptions
defaultJSOptions = JSOptions
  { optJSCompile = False
  , optJSOptimize = False
  , optJSMinify = False
  }

jsCommandLineFlags :: [OptDescr (Flag JSOptions)]
jsCommandLineFlags =
    [ Option [] ["js"] (NoArg enable) "compile program using the JS backend"
    , Option [] ["js-optimize"] (NoArg enableOpt) "turn on optimizations during JS code generation"
    -- Minification is described at https://en.wikipedia.org/wiki/Minification_(programming)
    , Option [] ["js-minify"] (NoArg enableMin) "minify generated JS code"
    ]
  where
    enable o = pure o{ optJSCompile = True }
    enableOpt o = pure o{ optJSOptimize = True }
    enableMin o = pure o{ optJSMinify = True }

--- Top-level compilation ---

jsPreCompile :: JSOptions -> TCM JSOptions
jsPreCompile opts = return opts

jsPostCompile :: JSOptions -> IsMain -> Map.Map ModuleName Module -> TCM ()
jsPostCompile _opts _ _ms = copyRTEModules

mergeModules :: Map.Map ModuleName Module -> [(GlobalId, Export)]
mergeModules ms
    = [ (jsMod n, e)
      | (n, Module _ _ es _) <- Map.toList ms
      , e <- es
      ]

--- Module compilation ---

type JSModuleEnv = Maybe CoinductionKit

jsPreModule :: JSOptions -> IsMain -> ModuleName -> FilePath -> TCM (Recompile JSModuleEnv Module)
jsPreModule _opts _ m ifile = ifM uptodate noComp yesComp
  where
    uptodate = liftIO =<< isNewerThan <$> outFile_ <*> pure ifile

    noComp = do
      reportSLn "compile.js" 2 . (++ " : no compilation is needed.") . prettyShow =<< curMName
      return $ Skip __IMPOSSIBLE__

    yesComp = do
      m   <- prettyShow <$> curMName
      out <- outFile_
      reportSLn "compile.js" 1 $ repl [m, ifile, out] "Compiling <<0>> in <<1>> to <<2>>"
      Recompile <$> coinductionKit

jsPostModule :: JSOptions -> JSModuleEnv -> IsMain -> ModuleName -> [Maybe Export] -> TCM Module
jsPostModule opts _ isMain _ defs = do
  m             <- jsMod <$> curMName
  is            <- map (jsMod . fst) . iImportedModules <$> curIF
  let es = catMaybes defs
      mod = Module m is (reorder es) main
  writeModule (optJSMinify opts) mod
  return mod
  where
    main = case isMain of
      IsMain  -> Just $ Apply (Lookup Self $ MemberId "main") [Lambda 1 emp]
      NotMain -> Nothing

jsCompileDef :: JSOptions -> JSModuleEnv -> IsMain -> Definition -> TCM (Maybe Export)
jsCompileDef opts kit _isMain def = definition (opts, kit) (defName def, def)

--------------------------------------------------
-- Naming
--------------------------------------------------

prefix :: [Char]
prefix = "jAgda"

jsMod :: ModuleName -> GlobalId
jsMod m = GlobalId (prefix : map prettyShow (mnameToList m))

jsFileName :: GlobalId -> String
jsFileName (GlobalId ms) = intercalate "." ms ++ ".js"

jsMember :: Name -> MemberId
jsMember n
  -- Anonymous fields are used for where clauses,
  -- and they're all given the concrete name "_",
  -- so we disambiguate them using their name id.
  | isNoName n = MemberId ("_" ++ show (nameId n))
  | otherwise  = MemberId $ prettyShow n

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
  let us = uses e `difference` defs
  in  if null us
        then e : (reorder' (insert (expName e) defs) es)
        else reorder' defs (insertAfter us e es)

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
insertAfter us e []                   = [e]
insertAfter us e (f : fs) | null us   = e : f : fs
insertAfter us e (f : fs) | otherwise =
  f : insertAfter (delete (expName f) us) e fs

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

{- dead code
curModule :: IsMain -> TCM Module
curModule isMain = do
  kit <- coinductionKit
  m <- (jsMod <$> curMName)
  is <- map jsMod <$> (map fst . iImportedModules <$> curIF)
  es <- catMaybes <$> (mapM (definition kit) =<< (sortDefs <$> curDefs))
  return $ Module m is (reorder es) main
  where
    main = case isMain of
      IsMain -> Just $ Apply (Lookup Self $ MemberId "main") [Lambda 1 emp]
      NotMain -> Nothing
-}
type EnvWithOpts = (JSOptions, JSModuleEnv)

definition :: EnvWithOpts -> (QName,Definition) -> TCM (Maybe Export)
definition kit (q,d) = do
  reportSDoc "compile.js" 10 $ "compiling def:" <+> prettyTCM q
  (_,ls) <- global q
  d <- instantiateFull d

  definition' kit q d (defType d) ls

-- | Ensure that there is at most one pragma for a name.
checkCompilerPragmas :: QName -> TCM ()
checkCompilerPragmas q =
  caseMaybeM (getUniqueCompilerPragma jsBackendName q) (return ()) $ \ (CompilerPragma r s) ->
  setCurrentRange r $ case words s of
    "=" : _ -> return ()
    _       -> genericDocError $ P.sep [ "Badly formed COMPILE JS pragma. Expected",
                                         "{-# COMPILE JS <name> = <js> #-}" ]

defJSDef :: Definition -> Maybe String
defJSDef def =
  case defCompilerPragmas jsBackendName def of
    [CompilerPragma _ s] -> Just (dropEquals s)
    []                   -> Nothing
    _:_:_                -> __IMPOSSIBLE__
  where
    dropEquals = dropWhile $ \ c -> isSpace c || c == '='

definition' :: EnvWithOpts -> QName -> Definition -> Type -> [MemberId] -> TCM (Maybe Export)
definition' kit q d t ls = do
  checkCompilerPragmas q
  case theDef d of
    -- coinduction
    Constructor{} | Just q == (nameOfSharp <$> snd kit) -> do
      return Nothing
    Function{} | Just q == (nameOfFlat <$> snd kit) -> do
      ret $ Lambda 1 $ Apply (Lookup (local 0) flatName) []

    DataOrRecSig{} -> __IMPOSSIBLE__

    Axiom | Just e <- defJSDef d -> plainJS e
    Axiom | otherwise -> ret Undefined

    GeneralizableVar{} -> return Nothing

    Function{} | Just e <- defJSDef d -> plainJS e
    Function{} | otherwise -> do

      reportSDoc "compile.js" 5 $ "compiling fun:" <+> prettyTCM q
      caseMaybeM (toTreeless T.EagerEvaluation q) (pure Nothing) $ \ treeless -> do
        used <- getCompiledArgUse q
        funBody <- eliminateCaseDefaults =<<
          eliminateLiteralPatterns
          (convertGuards treeless)
        reportSDoc "compile.js" 30 $ " compiled treeless fun:" <+> pretty funBody

        let (body, given) = lamView funBody
              where
                lamView :: T.TTerm -> (T.TTerm, Int)
                lamView (T.TLam t) = (+1) <$> lamView t
                lamView t = (t, 0)

            -- number of eta expanded args
            etaN = length $ dropWhile id $ reverse $ drop given used

        funBody' <- compileTerm kit
                  $ iterate' (given + etaN - length (filter not used)) T.TLam
                  $ eraseLocalVars (map not used)
                  $ T.mkTApp (raise etaN body) (T.TVar <$> [etaN-1, etaN-2 .. 0])

        reportSDoc "compile.js" 30 $ " compiled JS fun:" <+> (text . show) funBody'
        return $ Just $ Export ls funBody'

    Primitive{primName = p} | p `Set.member` primitives ->
      plainJS $ "agdaRTS." ++ p
    Primitive{} | Just e <- defJSDef d -> plainJS e
    Primitive{} | otherwise -> ret Undefined
    PrimitiveSort{} -> return Nothing

    Datatype{} -> do
        computeErasedConstructorArgs q
        ret emp
    Record{} -> do
        computeErasedConstructorArgs q
        return Nothing

    Constructor{} | Just e <- defJSDef d -> plainJS e
    Constructor{conData = p, conPars = nc} -> do
      let np = arity t - nc
      erased <- getErasedConArgs q
      let nargs = np - length (filter id erased)
          args = [ Local $ LocalId $ nargs - i | i <- [0 .. nargs-1] ]
      d <- getConstInfo p
      case theDef d of
        Record { recFields = flds } -> ret $ curriedLambda nargs $
          if optJSOptimize (fst kit)
            then Lambda 1 $ Apply (Local (LocalId 0)) args
            else Object $ fromList [ (last ls, Lambda 1 $ Apply (Lookup (Local (LocalId 0)) $ last ls) args) ]
        dt ->
          ret $ curriedLambda (nargs + 1) $ Apply (Lookup (Local (LocalId 0)) index) args
          where
            index | Datatype{} <- dt
                  , optJSOptimize (fst kit)
                  , cs <- defConstructors dt
                  = headWithDefault __IMPOSSIBLE__
                      [MemberIndex i (mkComment $ last ls) | (i, x) <- zip [0..] cs, x == q]
                  | otherwise = last ls
            mkComment (MemberId s) = Comment s
            mkComment _ = mempty

    AbstractDefn{} -> __IMPOSSIBLE__
  where
    ret = return . Just . Export ls
    plainJS = return . Just . Export ls . PlainJS

compileTerm :: EnvWithOpts -> T.TTerm -> TCM Exp
compileTerm kit t = go t
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
      T.TApp (T.TCon q) [x] | Just q == (nameOfSharp <$> snd kit) -> do
        x <- go x
        let evalThunk = unlines
              [ "function() {"
              , "  delete this.flat;"
              , "  var result = this.__flat_helper();"
              , "  delete this.__flat_helper;"
              , "  this.flat = function() { return result; };"
              , "  return result;"
              , "}"
              ]
        return $ Object $ Map.fromList
          [(flatName, PlainJS evalThunk)
          ,(MemberId "__flat_helper", Lambda 0 x)]
      T.TApp t' xs | Just f <- getDef t' -> do
        used <- either getCompiledArgUse (\x -> fmap (map not) $ getErasedConArgs x) f
        let given = length xs

            -- number of eta expanded args
            etaN = length $ dropWhile id $ reverse $ drop given used

            xs' = xs ++ (T.TVar <$> [etaN-1, etaN-2 .. 0])
            args = [ t | (t, True) <- zip xs' $ used ++ repeat True ]

        curriedLambda etaN <$> (curriedApply <$> go (raise etaN t') <*> mapM go args)

      T.TApp t xs -> do
            curriedApply <$> go t <*> mapM go xs
      T.TLam t -> Lambda 1 <$> go t
      -- TODO This is not a lazy let, but it should be...
      T.TLet t e -> apply <$> (Lambda 1 <$> go e) <*> traverse go [t]
      T.TLit l -> return $ literal l
      T.TCon q -> do
        d <- getConstInfo q
        qname q
      T.TCase sc ct def alts | T.CTData dt <- T.caseType ct -> do
        dt <- getConstInfo dt
        alts' <- traverse (compileAlt kit) alts
        let cs  = defConstructors $ theDef dt
            obj = Object $ Map.fromList [(snd x, y) | (x, y) <- alts']
            arr = mkArray [headWithDefault (mempty, Null) [(Comment s, y) | ((c', MemberId s), y) <- alts', c' == c] | c <- cs]
        case (theDef dt, defJSDef dt) of
          (_, Just e) -> do
            return $ apply (PlainJS e) [Local (LocalId sc), obj]
          (Record{}, _) | optJSOptimize (fst kit) -> do
            return $ apply (Local $ LocalId sc) [snd $ headWithDefault __IMPOSSIBLE__ alts']
          (Record{}, _) -> do
            memId <- visitorName $ recCon $ theDef dt
            return $ apply (Lookup (Local $ LocalId sc) memId) [obj]
          (Datatype{}, _) | optJSOptimize (fst kit) -> do
            return $ curriedApply (Local (LocalId sc)) [arr]
          (Datatype{}, _) -> do
            return $ curriedApply (Local (LocalId sc)) [obj]
          _ -> __IMPOSSIBLE__
      T.TCase _ _ _ _ -> __IMPOSSIBLE__

      T.TPrim p -> return $ compilePrim p
      T.TUnit -> unit
      T.TSort -> unit
      T.TErased -> unit
      T.TError T.TUnreachable -> return Undefined
      T.TCoerce t -> go t

    getDef (T.TDef f) = Just (Left f)
    getDef (T.TCon c) = Just (Right c)
    getDef (T.TCoerce x) = getDef x
    getDef _ = Nothing

    unit = return Null

    mkArray xs
        | 2 * length (filter ((==Null) . snd) xs) <= length xs = Array xs
        | otherwise = Object $ Map.fromList [(MemberIndex i c, x) | (i, (c, x)) <- zip [0..] xs, x /= Null]

compilePrim :: T.TPrim -> Exp
compilePrim p =
  case p of
    T.PIf -> curriedLambda 3 $ If (local 2) (local 1) (local 0)
    T.PEqI -> binOp "agdaRTS.uprimIntegerEqual"
    T.PEqF -> binOp "agdaRTS.uprimFloatEquality"
    T.PEqQ -> binOp "agdaRTS.uprimQNameEquality"
    T.PEqS -> primEq
    T.PEqC -> primEq
    T.PGeq -> binOp "agdaRTS.uprimIntegerGreaterOrEqualThan"
    T.PLt -> binOp "agdaRTS.uprimIntegerLessThan"
    T.PAdd -> binOp "agdaRTS.uprimIntegerPlus"
    T.PSub -> binOp "agdaRTS.uprimIntegerMinus"
    T.PMul -> binOp "agdaRTS.uprimIntegerMultiply"
    T.PRem -> binOp "agdaRTS.uprimIntegerRem"
    T.PQuot -> binOp "agdaRTS.uprimIntegerQuot"
    T.PAdd64 -> binOp "agdaRTS.uprimWord64Plus"
    T.PSub64 -> binOp "agdaRTS.uprimWord64Minus"
    T.PMul64 -> binOp "agdaRTS.uprimWord64Multiply"
    T.PRem64 -> binOp "agdaRTS.uprimIntegerRem"     -- -|
    T.PQuot64 -> binOp "agdaRTS.uprimIntegerQuot"   --  > These can use the integer functions
    T.PEq64 -> binOp "agdaRTS.uprimIntegerEqual"    --  |
    T.PLt64 -> binOp "agdaRTS.uprimIntegerLessThan" -- -|
    T.PITo64 -> unOp "agdaRTS.primWord64FromNat"
    T.P64ToI -> unOp "agdaRTS.primWord64ToNat"
    T.PSeq -> binOp "agdaRTS.primSeq"
  where binOp js = curriedLambda 2 $ apply (PlainJS js) [local 1, local 0]
        unOp js  = curriedLambda 1 $ apply (PlainJS js) [local 0]
        primEq   = curriedLambda 2 $ BinOp (local 1) "===" (local 0)


compileAlt :: EnvWithOpts -> T.TAlt -> TCM ((QName, MemberId), Exp)
compileAlt kit a = case a of
  T.TACon con ar body -> do
    erased <- getErasedConArgs con
    let nargs = ar - length (filter id erased)
    memId <- visitorName con
    body <- Lambda nargs <$> compileTerm kit (eraseLocalVars erased body)
    return ((con, memId), body)
  _ -> __IMPOSSIBLE__

eraseLocalVars :: [Bool] -> T.TTerm -> T.TTerm
eraseLocalVars [] x = x
eraseLocalVars (False: es) x = eraseLocalVars es x
eraseLocalVars (True: es) x = eraseLocalVars es (TC.subst (length es) T.TErased x)

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
literal = \case
  (LitNat    x) -> Integer x
  (LitWord64 x) -> Integer (fromIntegral x)
  (LitFloat  x) -> Double  x
  (LitString x) -> String  x
  (LitChar   x) -> Char    x
  (LitQName  x) -> litqname x
  LitMeta{}     -> __IMPOSSIBLE__

litqname :: QName -> Exp
litqname q =
  Object $ Map.fromList
    [ (mem "id", Integer $ fromIntegral n)
    , (mem "moduleId", Integer $ fromIntegral m)
    , (mem "name", String $ T.pack $ prettyShow q)
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
    litAssoc NonAssoc   = String "non-assoc"
    litAssoc LeftAssoc  = String "left-assoc"
    litAssoc RightAssoc = String "right-assoc"

    litPrec Unrelated   = String "unrelated"
    litPrec (Related l) = Double l

--------------------------------------------------
-- Writing out an ECMAScript module
--------------------------------------------------

writeModule :: Bool -> Module -> TCM ()
writeModule minify m = do
  out <- outFile (modName m)
  liftIO (writeFile out (JSPretty.prettyShow minify m))

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
  [  "primShowInteger"

  -- Natural number functions
  -- , "primNatPlus"                 -- missing
  , "primNatMinus"
  -- , "primNatTimes"                -- missing
  -- , "primNatDivSucAux"            -- missing
  -- , "primNatModSucAux"            -- missing
  -- , "primNatEquality"             -- missing
  -- , "primNatLess"                 -- missing
  -- , "primShowNat"                 -- missing

  -- Machine words
  , "primWord64ToNat"
  , "primWord64FromNat"
  -- , "primWord64ToNatInjective"    -- missing

  -- Level functions
  -- , "primLevelZero"               -- missing
  -- , "primLevelSuc"                -- missing
  -- , "primLevelMax"                -- missing

  -- Sorts
  -- , "primSetOmega"                -- missing
  -- , "primStrictSetOmega"          -- missing

  -- Floating point functions
  , "primFloatEquality"
  , "primFloatInequality"
  , "primFloatLess"
  , "primFloatIsInfinite"
  , "primFloatIsNaN"
  , "primFloatIsNegativeZero"
  , "primFloatIsSafeInteger"
  , "primFloatToWord64"
  -- , "primFloatToWord64Injective"  -- missing
  , "primNatToFloat"
  , "primIntToFloat"
  -- , "primFloatRound"              -- in Agda.Builtin.Float
  -- , "primFloatFloor"              -- in Agda.Builtin.Float
  -- , "primFloatCeiling"            -- in Agda.Builtin.Float
  -- , "primFloatToRatio"            -- in Agda.Builtin.Float
  , "primRatioToFloat"
  -- , "primFloatDecode"             -- in Agda.Builtin.Float
  -- , "primFloatEncode"             -- in Agda.Builtin.Float
  , "primShowFloat"
  , "primFloatPlus"
  , "primFloatMinus"
  , "primFloatTimes"
  , "primFloatNegate"
  , "primFloatDiv"
  , "primFloatSqrt"
  , "primFloatExp"
  , "primFloatLog"
  , "primFloatSin"
  , "primFloatCos"
  , "primFloatTan"
  , "primFloatASin"
  , "primFloatACos"
  , "primFloatATan"
  , "primFloatATan2"
  , "primFloatSinh"
  , "primFloatCosh"
  , "primFloatTanh"
  , "primFloatASinh"
  , "primFloatACosh"
  , "primFloatATanh"
  , "primFloatPow"

  -- Character functions
  -- , "primCharEquality"            -- missing
  -- , "primIsLower"                 -- missing
  -- , "primIsDigit"                 -- missing
  -- , "primIsAlpha"                 -- missing
  -- , "primIsSpace"                 -- missing
  -- , "primIsAscii"                 -- missing
  -- , "primIsLatin1"                -- missing
  -- , "primIsPrint"                 -- missing
  -- , "primIsHexDigit"              -- missing
  -- , "primToUpper"                 -- missing
  -- , "primToLower"                 -- missing
  -- , "primCharToNat"               -- missing
  -- , "primCharToNatInjective"      -- missing
  -- , "primNatToChar"               -- missing
  -- , "primShowChar"                -- in Agda.Builtin.String

  -- String functions
  -- , "primStringToList"            -- in Agda.Builtin.String
  -- , "primStringToListInjective"   -- missing
  -- , "primStringFromList"          -- in Agda.Builtin.String
  -- , "primStringFromListInjective" -- missing
  -- , "primStringAppend"            -- in Agda.Builtin.String
  -- , "primStringEquality"          -- in Agda.Builtin.String
  -- , "primShowString"              -- in Agda.Builtin.String
  -- , "primStringUncons"            -- in Agda.Builtin.String

  -- Other stuff
  -- , "primEraseEquality"           -- missing
  -- , "primForce"                   -- missing
  -- , "primForceLemma"              -- missing
  , "primQNameEquality"
  , "primQNameLess"
  , "primShowQName"
  , "primQNameFixity"
  -- , "primQNameToWord64s"          -- missing
  -- , "primQNameToWord64sInjective" -- missing
  -- , "primMetaEquality"            -- missing
  -- , "primMetaLess"                -- missing
  -- , "primShowMeta"                -- missing
  -- , "primMetaToNat"               -- missing
  -- , "primMetaToNatInjective"      -- missing
  -- , "primIMin"                    -- missing
  -- , "primIMax"                    -- missing
  -- , "primINeg"                    -- missing
  -- , "primPOr"                     -- missing
  -- , "primComp"                    -- missing
  -- , builtinTrans                  -- missing
  -- , builtinHComp                  -- missing
  -- , "primIdJ"                     -- missing
  -- , "primPartial"                 -- missing
  -- , "primPartialP"                -- missing
  -- , builtinGlue                   -- missing
  -- , builtin_glue                  -- missing
  -- , builtin_unglue                -- missing
  -- , builtinFaceForall             -- missing
  -- , "primDepIMin"                 -- missing
  -- , "primIdFace"                  -- missing
  -- , "primIdPath"                  -- missing
  -- , builtinIdElim                 -- missing
  -- , builtinSubOut                 -- missing
  -- , builtin_glueU                 -- missing
  -- , builtin_unglueU               -- missing
  ]
