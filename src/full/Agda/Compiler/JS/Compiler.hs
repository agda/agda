-- | Main module for JS backend.

module Agda.Compiler.JS.Compiler where

import Prelude hiding ( null, writeFile )

import Control.DeepSeq
import Control.Monad.Trans

import Data.Char     ( isSpace )
import Data.Foldable ( forM_ )
import Data.List     ( dropWhileEnd, elemIndex, intercalate, partition )
import Data.Set      ( Set )

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Text as T

import GHC.Generics (Generic)

import System.Directory   ( createDirectoryIfMissing )
import System.Environment ( setEnv )
import System.FilePath    ( splitFileName, (</>) )
import System.Process     ( callCommand )

import Paths_Agda

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name ( isNoName )
import Agda.Syntax.Abstract.Name
  ( QName,
    mnameToList, qnameName, qnameModule, nameId )
import Agda.Syntax.Internal
  ( Name, Type
  , nameFixity, unDom, telToList )
import Agda.Syntax.Literal       ( Literal(..) )
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName(..))
import Agda.Syntax.Treeless      ( ArgUsage(..), filterUsed )
import qualified Agda.Syntax.Treeless as T

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce ( instantiateFull )
import Agda.TypeChecking.Substitute as TC ( TelV(..), raise, subst )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Telescope ( telViewPath )

import Agda.Utils.FileName ( isNewerThan )
import Agda.Utils.Function ( iterate' )
import Agda.Utils.List ( downFrom, headWithDefault )
import Agda.Utils.List1 ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe ( boolToMaybe, catMaybes, caseMaybeM, fromMaybe, whenNothing )
import Agda.Utils.Monad ( ifM, when )
import Agda.Utils.Null  ( null )
import Agda.Utils.Pretty (prettyShow, render)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.IO.Directory
import Agda.Utils.IO.UTF8 ( writeFile )
import Agda.Utils.Singleton ( singleton )
import Agda.Utils.Size (size)

import Agda.Compiler.Common as CC
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.EliminateDefaults
import Agda.Compiler.Treeless.EliminateLiteralPatterns
import Agda.Compiler.Treeless.GuardsToPrims
import Agda.Compiler.Treeless.Erase ( computeErasedConstructorArgs )
import Agda.Compiler.Treeless.Subst ()
import Agda.Compiler.Backend (Backend(..), Backend'(..), Recompile(..))

import Agda.Compiler.JS.Syntax
  ( Exp(Self,Local,Global,Undefined,Null,String,Char,Integer,Double,Lambda,Object,Array,Apply,Lookup,If,BinOp,PlainJS),
    LocalId(LocalId), GlobalId(GlobalId), MemberId(MemberId,MemberIndex), Export(Export), Module(Module, modName, callMain), Comment(Comment),
    modName, expName, uses
  , JSQName
  )
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
  { optJSCompile  :: Bool
  , optJSOptimize :: Bool
  , optJSMinify   :: Bool
      -- ^ Remove spaces etc. See https://en.wikipedia.org/wiki/Minification_(programming).
  , optJSVerify   :: Bool
      -- ^ Run generated code through interpreter.
  }
  deriving Generic

instance NFData JSOptions

defaultJSOptions :: JSOptions
defaultJSOptions = JSOptions
  { optJSCompile  = False
  , optJSOptimize = False
  , optJSMinify   = False
  , optJSVerify   = False
  }

jsCommandLineFlags :: [OptDescr (Flag JSOptions)]
jsCommandLineFlags =
    [ Option [] ["js"] (NoArg enable) "compile program using the JS backend"
    , Option [] ["js-optimize"] (NoArg enableOpt) "turn on optimizations during JS code generation"
    -- Minification is described at https://en.wikipedia.org/wiki/Minification_(programming)
    , Option [] ["js-minify"] (NoArg enableMin) "minify generated JS code"
    , Option [] ["js-verify"] (NoArg enableVerify) "except for main module, run generated JS modules through `node` (needs to be in PATH)"
    ]
  where
    enable       o = pure o{ optJSCompile  = True }
    enableOpt    o = pure o{ optJSOptimize = True }
    enableMin    o = pure o{ optJSMinify   = True }
    enableVerify o = pure o{ optJSVerify   = True }

--- Top-level compilation ---

jsPreCompile :: JSOptions -> TCM JSOptions
jsPreCompile opts = do
  cubical <- optCubical <$> pragmaOptions
  let notSupported s =
        typeError $ GenericError $
          "Compilation of code that uses " ++ s ++ " is not supported."
  case cubical of
    Nothing      -> return ()
    Just CErased -> notSupported "--erased-cubical"
    Just CFull   -> notSupported "--cubical"

  return opts

-- | After all modules have been compiled, copy RTE modules and verify compiled modules.

jsPostCompile ::
  JSOptions -> IsMain -> Map.Map TopLevelModuleName Module -> TCM ()
jsPostCompile opts _ ms = do

  -- Copy RTE modules.

  compDir  <- compileDir
  liftIO $ do
    dataDir <- getDataDir
    let srcDir = dataDir </> "JS"
    copyDirContent srcDir compDir

  -- Verify generated JS modules (except for main).

  reportSLn "compile.js.verify" 10 $ "Considering to verify generated JS modules"
  when (optJSVerify opts) $ do

    reportSLn "compile.js.verify" 10 $ "Verifying generated JS modules"
    liftIO $ setEnv "NODE_PATH" compDir

    forM_ ms $ \ Module{ modName, callMain } -> do
      jsFile <- outFile modName
      reportSLn "compile.js.verify" 30 $ unwords [ "Considering JS module:" , jsFile ]

      -- Since we do not run a JS program for real, we skip all modules that could
      -- have a call to main.
      -- Atm, modules whose compilation was skipped are also skipped during verification
      -- (they appear here as main modules).
      whenNothing callMain $ do
        let cmd = unwords [ "node", "-", "<", jsFile ]
        reportSLn "compile.js.verify" 20 $ unwords [ "calling:", cmd ]
        liftIO $ callCommand cmd

--- Module compilation ---

data JSModuleEnv = JSModuleEnv
  { jsCoinductionKit :: Maybe CoinductionKit
  , jsCompile        :: Bool
    -- ^ Should this module be compiled?
  }

jsPreModule ::
  JSOptions -> IsMain -> TopLevelModuleName -> Maybe FilePath ->
  TCM (Recompile JSModuleEnv Module)
jsPreModule _opts _ m mifile = do
  cubical <- optCubical <$> pragmaOptions
  let compile = case cubical of
        -- Code that uses --cubical is not compiled.
        Just CFull   -> False
        Just CErased -> True
        Nothing      -> True
  ifM uptodate noComp (yesComp compile)
  where
    uptodate = case mifile of
      Nothing -> pure False
      Just ifile -> liftIO =<< isNewerThan <$> outFile_ <*> pure ifile
    ifileDesc = fromMaybe "(memory)" mifile

    noComp = do
      reportSLn "compile.js" 2 . (++ " : no compilation is needed.") . prettyShow =<< curMName
      return $ Skip skippedModule

    -- A skipped module acts as a fake main module, to be skipped by --js-verify as well.
    skippedModule = Module (jsMod m) mempty mempty (Just __IMPOSSIBLE__)

    yesComp compile = do
      m   <- prettyShow <$> curMName
      out <- outFile_
      reportSLn "compile.js" 1 $ repl [m, ifileDesc, out] "Compiling <<0>> in <<1>> to <<2>>"
      kit <- coinductionKit
      return $ Recompile $ JSModuleEnv
        { jsCoinductionKit = kit
        , jsCompile        = compile
        }

jsPostModule ::
  JSOptions -> JSModuleEnv -> IsMain -> TopLevelModuleName ->
  [Maybe Export] -> TCM Module
jsPostModule opts _ isMain _ defs = do
  m  <- jsMod <$> curMName
  is <- map (jsMod . fst) . iImportedModules <$> curIF
  let mod = Module m is (reorder es) callMain
  writeModule (optJSMinify opts) mod
  return mod
  where
  es       = catMaybes defs
  main     = MemberId "main"
  -- Andreas, 2020-10-27, only add invocation of "main" if such function is defined.
  -- This allows loading of generated .js files into an interpreter
  -- even if they do not define "main".
  hasMain  = isMain == IsMain && any ((singleton main ==) . expName) es
  callMain :: Maybe Exp
  callMain = boolToMaybe hasMain $ Apply (Lookup Self main) [Lambda 1 emp]


jsCompileDef :: JSOptions -> JSModuleEnv -> IsMain -> Definition -> TCM (Maybe Export)
jsCompileDef opts kit _isMain def = definition (opts, kit) (defName def, def)

--------------------------------------------------
-- Naming
--------------------------------------------------

prefix :: [Char]
prefix = "jAgda"

jsMod :: TopLevelModuleName -> GlobalId
jsMod m =
  GlobalId (prefix : map T.unpack (List1.toList (moduleNameParts m)))

jsFileName :: GlobalId -> String
jsFileName (GlobalId ms) = intercalate "." ms ++ ".js"

jsMember :: Name -> MemberId
jsMember n
  -- Anonymous fields are used for where clauses,
  -- and they're all given the concrete name "_",
  -- so we disambiguate them using their name id.
  | isNoName n = MemberId ("_" ++ show (nameId n))
  | otherwise  = MemberId $ prettyShow n

global' :: QName -> TCM (Exp, JSQName)
global' q = do
  i   <- iTopLevelModuleName <$> curIF
  top <- CC.topLevelModuleName (qnameModule q)
  let
    -- Global module prefix
    qms = mnameToList $ qnameModule q
    -- File-local module prefix
    localms = drop (size top) qms
    nm = fmap jsMember $ List1.snoc localms $ qnameName q
  if top == i
    then return (Self, nm)
    else return (Global (jsMod top), nm)

global :: QName -> TCM (Exp, JSQName)
global q = do
  d <- getConstInfo q
  case d of
    Defn { theDef = Constructor { conData = p } } -> do
      getConstInfo p >>= \case
        -- Andreas, 2020-10-27, comment quotes outdated fact.
        -- anon. constructors are now M.R.constructor.
        -- We could simplify/remove the workaround by switching "record"
        -- to "constructor", but this changes the output of the JS compiler
        -- maybe in ways that break user's developments
        -- (if they link to Agda-generated JS).
        -- -- Rather annoyingly, the anonymous constructor of a record R in module M
        -- -- is given the name M.recCon, but a named constructor C
        -- -- is given the name M.R.C, sigh. This causes a lot of hoop-jumping
        -- -- in the map from Agda names to JS names, which we patch by renaming
        -- -- anonymous constructors to M.R.record.
        Defn { theDef = Record { recNamedCon = False } } -> do
          (m,ls) <- global' p
          return (m, ls <> singleton (MemberId "record"))
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

reorder' :: Set JSQName -> [Export] -> [Export]
reorder' defs [] = []
reorder' defs (e : es) =
  let us = uses e `Set.difference` defs
  in  if null us
        then e : (reorder' (Set.insert (expName e) defs) es)
        else reorder' defs (insertAfter us e es)

isTopLevelValue :: Export -> Bool
isTopLevelValue (Export _ e) = case e of
  Object m | flatName `Map.member` m -> False
  Lambda{} -> False
  _        -> True

isEmptyObject :: Export -> Bool
isEmptyObject (Export _ e) = case e of
  Object m -> null m
  Lambda{} -> True
  _        -> False

insertAfter :: Set JSQName -> Export -> [Export] -> [Export]
insertAfter us e []                   = [e]
insertAfter us e (f : fs) | null us   = e : f : fs
insertAfter us e (f : fs) | otherwise =
  f : insertAfter (Set.delete (expName f) us) e fs

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

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

definition' :: EnvWithOpts -> QName -> Definition -> Type -> JSQName -> TCM (Maybe Export)
definition' kit q d t ls =
  if not (jsCompile (snd kit)) || not (usableModality d)
  then return Nothing
  else do
  checkCompilerPragmas q
  case theDef d of
    -- coinduction
    Constructor{}
      | Just q == (nameOfSharp <$> jsCoinductionKit (snd kit)) -> do
      return Nothing
    Function{}
      | Just q == (nameOfFlat <$> jsCoinductionKit (snd kit)) -> do
      ret $ Lambda 1 $ Apply (Lookup (local 0) flatName) []

    DataOrRecSig{} -> __IMPOSSIBLE__

    Axiom{} | Just e <- defJSDef d -> plainJS e
    Axiom{} | otherwise -> ret Undefined

    GeneralizableVar{} -> return Nothing

    Function{} | Just e <- defJSDef d -> plainJS e
    Function{} | otherwise -> do

      reportSDoc "compile.js" 5 $ "compiling fun:" <+> prettyTCM q
      caseMaybeM (toTreeless T.EagerEvaluation q) (pure Nothing) $ \ treeless -> do
        used <- fromMaybe [] <$> getCompiledArgUse q
        funBody <- eliminateCaseDefaults =<<
          eliminateLiteralPatterns
          (convertGuards treeless)
        reportSDoc "compile.js" 30 $ " compiled treeless fun:" <+> pretty funBody
        reportSDoc "compile.js" 40 $ " argument usage:" <+> (text . show) used

        let (body, given) = lamView funBody
              where
                lamView :: T.TTerm -> (T.TTerm, Int)
                lamView (T.TLam t) = (+1) <$> lamView t
                lamView t = (t, 0)

            -- number of eta expanded args
            etaN = length $ dropWhileEnd (== ArgUsed) $ drop given used

            unusedN = length $ filter (== ArgUnused) used

        funBody' <- compileTerm kit
                  $ iterate' (given + etaN - unusedN) T.TLam
                  $ eraseLocalVars (map (== ArgUnused) used)
                  $ T.mkTApp (raise etaN body) (T.TVar <$> downFrom etaN)

        reportSDoc "compile.js" 30 $ " compiled JS fun:" <+> (text . show) funBody'
        return $
          if funBody' == Null then Nothing
          else Just $ Export ls funBody'

    Primitive{primName = p}
      | p == builtin_glueU ->
        -- The string prim^glueU is not a valid JS name.
        plainJS "agdaRTS.prim_glueU"
      | p == builtin_unglueU ->
        -- The string prim^unglueU is not a valid JS name.
        plainJS "agdaRTS.prim_unglueU"
      | p `Set.member` primitives ->
        plainJS $ "agdaRTS." ++ p
      | Just e <- defJSDef d ->
        plainJS e
      | otherwise ->
        ret Undefined
    PrimitiveSort{} -> return Nothing

    Datatype{} -> do
        computeErasedConstructorArgs q
        ret emp
    Record{} -> do
        computeErasedConstructorArgs q
        return Nothing

    Constructor{} | Just e <- defJSDef d -> plainJS e
    Constructor{conData = p, conPars = nc} -> do
      TelV tel _ <- telViewPath t
      let np = length (telToList tel) - nc
      erased <- getErasedConArgs q
      let nargs = np - length (filter id erased)
          args = [ Local $ LocalId $ nargs - i | i <- [0 .. nargs-1] ]
      d <- getConstInfo p
      let l = List1.last ls
      case theDef d of
        Record { recFields = flds } -> ret $ curriedLambda nargs $
          if optJSOptimize (fst kit)
            then Lambda 1 $ Apply (Local (LocalId 0)) args
            else Object $ Map.singleton l $ Lambda 1 $ Apply (Lookup (Local (LocalId 0)) l) args
        dt -> do
          i <- index
          ret $ curriedLambda (nargs + 1) $ Apply (Lookup (Local (LocalId 0)) i) args
          where
            index :: TCM MemberId
            index
              | Datatype{} <- dt
              , optJSOptimize (fst kit) = do
                  q  <- canonicalName q
                  cs <- mapM canonicalName $ defConstructors dt
                  case q `elemIndex` cs of
                    Just i  -> return $ MemberIndex i (mkComment l)
                    Nothing -> __IMPOSSIBLE_VERBOSE__ $ unwords [ "Constructor", prettyShow q, "not found in", prettyShow cs ]
              | otherwise = return l
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
    go = \case
      T.TVar x -> return $ Local $ LocalId x
      T.TDef q -> do
        d <- getConstInfo q
        case theDef d of
          -- Datatypes and records are erased
          Datatype {} -> return (String "*")
          Record {} -> return (String "*")
          _ -> qname q
      T.TApp (T.TCon q) [x]
        | Just q == (nameOfSharp <$> jsCoinductionKit (snd kit)) -> do
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
        return $ Object $ Map.fromListWith __IMPOSSIBLE__
          [(flatName, PlainJS evalThunk)
          ,(MemberId "__flat_helper", Lambda 0 x)]
      T.TApp t' xs | Just f <- getDef t' -> do
        used <- case f of
          Left  q -> fromMaybe [] <$> getCompiledArgUse q
          Right c -> map (\ b -> if b then ArgUnused else ArgUsed) <$> getErasedConArgs c
            -- Andreas, 2021-02-10 NB: could be @map (bool ArgUsed ArgUnused)@
            -- but I find it unintuitive that 'bool' takes the 'False'-branch first.
        let given = length xs

            -- number of eta expanded args
            etaN = length $ dropWhile (== ArgUsed) $ reverse $ drop given used

            args = filterUsed used $
                     raise etaN xs ++ (T.TVar <$> downFrom etaN)

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
      T.TCase sc ct def alts | T.CTData _ dt <- T.caseType ct -> do
        dt <- getConstInfo dt
        alts' <- traverse (compileAlt kit) alts
        let cs  = defConstructors $ theDef dt
            obj = Object $ Map.fromListWith __IMPOSSIBLE__ [(snd x, y) | (x, y) <- alts']
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
      T.TError T.TMeta{}      -> return Undefined
      T.TCoerce t -> go t

    getDef (T.TDef f) = Just (Left f)
    getDef (T.TCon c) = Just (Right c)
    getDef (T.TCoerce x) = getDef x
    getDef _ = Nothing

    unit = return Null

    mkArray xs
        | 2 * length (filter ((==Null) . snd) xs) <= length xs = Array xs
        | otherwise = Object $ Map.fromListWith __IMPOSSIBLE__
            [ (MemberIndex i c, x) | (i, (c, x)) <- zip [0..] xs, x /= Null ]

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
compileAlt kit = \case
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
visitorName q = do (m,ls) <- global q; return (List1.last ls)

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
  (LitMeta _ m) -> litmeta m

litqname :: QName -> Exp
litqname q =
  Object $ Map.fromListWith __IMPOSSIBLE__
    [ (mem "id", Integer $ fromIntegral n)
    , (mem "moduleId", Integer $ fromIntegral m)
    , (mem "name", String $ T.pack $ prettyShow q)
    , (mem "fixity", litfixity fx)]
  where
    mem = MemberId
    NameId n (ModuleNameHash m) = nameId $ qnameName q
    fx = theFixity $ nameFixity $ qnameName q

    litfixity :: Fixity -> Exp
    litfixity fx = Object $ Map.fromListWith __IMPOSSIBLE__
      [ (mem "assoc", litAssoc $ fixityAssoc fx)
      , (mem "prec", litPrec $ fixityLevel fx)]

    -- TODO this will probably not work well together with the necessary FFI bindings
    litAssoc NonAssoc   = String "non-assoc"
    litAssoc LeftAssoc  = String "left-assoc"
    litAssoc RightAssoc = String "right-assoc"

    litPrec Unrelated   = String "unrelated"
    litPrec (Related l) = Double l

litmeta :: MetaId -> Exp
litmeta (MetaId m h) =
  Object $ Map.fromListWith __IMPOSSIBLE__
    [ (MemberId "id", Integer $ fromIntegral m)
    , (MemberId "module", Integer $ fromIntegral $ moduleNameHash h) ]


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

-- | Primitives implemented in the JS Agda RTS.
--
-- TODO: Primitives that are not part of this set, and for which
-- 'defJSDef' does not return anything, are silently compiled to
-- 'Undefined'. A better approach might be to list exactly those
-- primitives which should be compiled to 'Undefined'.
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
  , "primMetaEquality"
  , "primMetaLess"
  , "primShowMeta"
  , "primMetaToNat"
  -- , "primMetaToNatInjective"      -- missing
  , builtinIMin
  , builtinIMax
  , builtinINeg
  , "primPartial"
  , "primPartialP"
  , builtinPOr
  , builtinComp
  , builtinTrans
  , builtinHComp
  , builtinSubOut
  , builtin_glueU
  , builtin_unglueU
  , builtinFaceForall
  , "primDepIMin"
  , "primIdFace"
  , "primIdPath"
  , builtinIdElim
  , builtinConId
  -- , builtinGlue                   -- missing
  -- , builtin_glue                  -- missing
  -- , builtin_unglue                -- missing
  ]
