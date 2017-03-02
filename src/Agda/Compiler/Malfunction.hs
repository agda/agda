{-# LANGUAGE TupleSections #-}
module Agda.Compiler.Malfunction (backend) where

import           Agda.Compiler.Backend
import           Agda.Utils.Pretty
import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Trans
import           Data.Bifunctor
import           Data.Char
import           Data.Either
import           Data.Generics.Uniplate
import           Data.Ix                             (rangeSize)
import           Data.Ix
import           Data.List
import           Data.Map                            (Map)
import qualified Data.Map                            as Map
import           Data.Maybe
import           Data.Set                            (Set)
import qualified Data.Set                            as Set
import           Numeric                             (showHex)
import           System.Console.GetOpt
import           Text.Printf

import           Agda.Compiler.Malfunction.AST
import qualified Agda.Compiler.Malfunction.Compiler  as Mlf
import           Agda.Compiler.Malfunction.Instances
import           Agda.Compiler.Malfunction.Run
import qualified Agda.Compiler.Malfunction.Run       as Run
import           Agda.Syntax.Common                  (NameId)

backend :: Backend
backend = Backend backend'

data MlfOptions = Opts
  { _enabled    :: Bool
  , _resultVar  :: Maybe Ident
  , _outputFile :: Maybe FilePath
  , _outputMlf  :: Maybe FilePath
  , _debug      :: Bool
  }

defOptions :: MlfOptions
defOptions = Opts
  { _enabled    = False
  , _resultVar  = Nothing
  , _outputFile = Nothing
  , _outputMlf  = Nothing
  , _debug      = False
  }

ttFlags :: [OptDescr (Flag MlfOptions)]
ttFlags =
  [ Option [] ["mlf"] (NoArg $ \ o -> return o{ _enabled = True })
    "Generate Malfunction"
  , Option ['r'] ["print-var"] (ReqArg (\r o -> return o{_resultVar = Just r}) "VAR")
    "(DEBUG) Run the module and print the integer value of a variable"
  , Option ['o'] [] (ReqArg (\r o -> return o{_outputFile = Just r}) "FILE")
    "(DEBUG) Place outputFile resulting module into FILE"
  , Option ['d'] ["debug"] (NoArg $ \ o -> return o{ _debug = True })
    "Generate Malfunction"
  , Option [] ["compilemlf"] (ReqArg (\r o -> return o{_outputMlf = Just r}) "MODNAME")
    "Runs the malfunction compiler on the output file"
  ]

backend' :: Backend' MlfOptions MlfOptions () [Definition] Definition
backend' = Backend' {
  backendName = "malfunction"
  , options = defOptions
  , commandLineFlags = ttFlags
  , isEnabled = _enabled
  , preCompile = return
  , postCompile = mlfPostCompile --liftIO (putStrLn "post compile")
  , preModule = \_enf _m _ifile -> return $ Recompile ()
  , compileDef = \_env _menv def -> return def
  , postModule = \_env _menv _m _mod defs -> return defs --mlfPostModule env defs
  , backendVersion = Nothing
  , scopeCheckingSuffices = False
  }

definitionSummary :: MlfOptions -> Definition -> TCM ()
definitionSummary opts def = when (_debug opts) $ do
  liftIO (putStrLn ("Summary for: " ++ show q))
  liftIO $ putStrLn $ unlines [
    show (defName def)
      ++ "  (" ++ show (Mlf.qnameNameId q)++ "), " ++ defntype
    ]
  case theDef def of
    Function{} ->
      whenJustM (toTreeless q) $
        \tt ->
          liftIO . putStrLn . render
          $  header '=' (show q)
          $$ sect "Treeless (abstract syntax)"    (text . show $ tt)
          $$ sect "Treeless (concrete syntax)"    (pretty tt)
    _ -> return ()
    where
      sect t dc = text t $+$ nest 2 dc $+$ text ""
      header c h = let cs = replicate 15 c
                   in text $ printf "%s %s %s" cs h cs
      q = defName def
      defntype = case theDef def of
        Constructor{}  -> "constructor"
        Primitive{}    -> "primitive"
        Function{}     -> "function"
        Datatype{}     -> "datatype"
        Record{}       -> "record"
        AbstractDefn{} -> "abstract"
        Axiom{}        -> "axiom"

-- TODO: Maybe we'd like to refactor this so that we first do something like
-- this (in the calling function)
--
--    partition [Definition] -> ([Function], [Primitive], ...)
--
-- And then we can simply do the topologic sorting stuff on the functions only.
-- This would certainly make this funciton a helluva lot cleaner.
--
-- | Compiles a whole module
mlfMod
  :: [Definition]   -- ^ All visible definitions
  -> TCM Mod
mlfMod allDefs = do
  grps' <- mapMaybeM act allDefs
  let (primsAndAxioms, tlFunBindings) = partitionEithers grps'
      (prims, axioms) = partitionEithers primsAndAxioms
  env <- getCompilerEnv (getConstructors allDefs) tlFunBindings
  let (MMod funBindings ts) = compile env tlFunBindings
      primBindings = catMaybes $ Mlf.runTranslate (mapM (uncurry Mlf.compilePrim) prims) env
      axiomBindings = catMaybes $ Mlf.runTranslate (mapM Mlf.compileAxiom axioms) env
  return $ MMod (axiomBindings ++ primBindings ++ funBindings) ts
    where
      act :: Definition -> TCM (Maybe (Either (Either (QName, String) QName) (QName, TTerm)))
      act def@Defn{defName = q, theDef = d} = case d of
        Function{}                -> fmap Right <$> getBindings def
        Primitive{ primName = s } -> return $ Just $ Left $ Left (q, s)
        Axiom{}                   -> return $ Just $ Left $ Right q
        _                         -> return Nothing

compile :: Mlf.Env -> [(QName, TTerm)] -> Mod
compile env bs = Mlf.compile env bs

qnamesInTerm :: Set QName -> TTerm -> Set QName
qnamesInTerm s t = go t s
  where
    go :: TTerm -> Set QName -> Set QName
    go t qs = case t of
      TDef q           -> Set.insert q qs
      TApp f args      -> foldr go qs (f:args)
      TLam b           -> go b qs
      TCon q           -> Set.insert q qs
      TLet a b         -> foldr go qs [a, b]
      TCase _ _ p alts -> foldr qnamesInAlt (go p qs) alts
      _                -> qs
      where
        qnamesInAlt a qs = case a of
          TACon q _ t -> Set.insert q (go t qs)
          TAGuard t b -> foldr go qs [t, b]
          TALit _ b   -> go b qs


-- | The argument allNames is optional. If you provide an empty list concrete
-- names will not be appended to the NameId
getCompilerEnv :: [[QName]] -> [(QName, TTerm)] -> TCM Mlf.Env
getCompilerEnv allcons bs
  | any ((>rangeSize Mlf.mlfTagRange) . length) allcons = error "too many constructors"
  | otherwise = do
      wa <- withArity allcons
      return (Mlf.mkCompilerEnv2 allNames wa)
  where
    allNames = Set.toList $ foldr step mempty bs
    step (qn, tt) acc = qnamesInTerm (Set.insert qn acc) tt

-- | Creates a mapping for all the constructors in the array. The constructors
-- should reference the same data-type.
withArity :: [[QName]] -> TCM [[(QName, Int)]]
withArity = mapM (mapM (\q -> (q,) <$> arityQName q))

-- | If the qnames references a constructor the arity of that constructor is returned.
arityQName :: QName -> TCM Int
arityQName q = f . theDef <$> getConstInfo q
  where
    f def = case def of
      Constructor{} -> conArity def
      _             -> error "Not a constructor :("

getBindings :: Definition -> TCM (Maybe (QName, TTerm))
getBindings Defn{defName = q} = fmap (\t -> (q, t)) <$> toTreeless q

mlfPostCompile :: MlfOptions -> IsMain -> Map ModuleName [Definition] -> TCM ()
mlfPostCompile opts _ modToDefs = do
  mapM_ (definitionSummary opts) allDefs
  void $ mlfPostModule opts allDefs
  where
    allDefs :: [Definition]
    allDefs = concat (Map.elems modToDefs)

-- TODO: `Definition`'s should be sorted *and* grouped by `defMutual` (a field
-- in Definition). each group should compile to:
--
--    (rec
--       x0 = def0
--       ...
--    )
mlfPostModule :: MlfOptions -> [Definition] -> TCM Mod
mlfPostModule opts defs = do
  modl@(MMod binds _) <- mlfMod defs
  let modlTxt = prettyShow $ fromMaybe modl
       ((withPrintInts modl . pure)  <$>  (_resultVar opts >>=  fromSimpleIdent binds))
  when (_debug opts) $ liftIO . putStrLn $ modlTxt
  whenJust (_resultVar opts) (printVars opts modl . pure)
  whenJust (_outputFile opts) (liftIO . (`writeFile`modlTxt))
  whenJust (_outputMlf opts) $ \fp -> liftIO $ Run.runMalfunction fp modlTxt
  return modl

printVars :: MonadIO m => MlfOptions -> Mod -> [Ident] -> m ()
printVars opts modl@(MMod binds _) simpleVars = when (_debug opts) $ do
  liftIO (putStrLn "\n=======================")
  case fullNames of
    Just vars -> liftIO $ runModPrintInts modl vars >>= putStrLn
    _ ->
      liftIO $
      putStrLn
        "Variable not bound, did you specify the *fully quailified* name, e.g. \"Test.var\"?"
  where
    fullNames = mapM (fromSimpleIdent binds) simpleVars

-- | "Test2.a" --> 24.1932f7ddf4cc7d3a.Test2.a
fromSimpleIdent :: [Binding] -> Ident -> Maybe Ident
fromSimpleIdent binds simple = listToMaybe (filter (isSuffixOf simple) (getNames binds))
  where
    getNames = mapMaybe getName
    getName (Named u _) = Just u
    getName _           = Nothing

-- | Returns all constructors grouped by data type.
getConstructors :: [Definition] -> [[QName]]
getConstructors = mapMaybe (getCons . theDef)
  where
    getCons :: Defn -> Maybe [QName]
    getCons c@Datatype{} = Just (dataCons c)
    -- The way I understand it a record is just like a data-type
    -- except it only has one constructor and that one constructor
    -- takes as many arguments as the number of fields in that
    -- record.
    getCons c@Record{}   = Just . pure . recCon $ c
    -- TODO: Stub value here!
    getCons _            = Nothing
