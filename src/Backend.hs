module Backend (backend) where

import           Agda.Compiler.Backend
import           Agda.Utils.Pretty
import qualified Compiler              as Mlf
import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Trans
import           Data.Bifunctor
import           Data.Either
import           Data.List
import           Data.Map              (Map)
import qualified Data.Map              as Map
import           Data.Maybe
import           Malfunction.AST
import           Malfunction.Run
import           System.Console.GetOpt
import           System.FilePath       (takeBaseName)
import           System.IO             (hPutStr, hFlush)
import           System.IO.Temp        (withSystemTempFile)
import           System.Process
import           Text.Printf

import           Primitive             (compilePrim, compileAxiom)

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
  , Option ['d'] ["debug"] (NoArg $ \ o -> return o{ _enabled = True })
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
  -- grps' <- mapM (mapM getBindings . filter (isFunction . theDef)) grps
  grps' <- mapM (mapMaybeM act) defsByDefmutual
  let
    (primBindings, tlFunBindings) = first concat (unzip (map partitionEithers grps'))
    (MMod funBindings ts) = Mlf.compile (getConstructors allDefs) tlFunBindings
  -- liftIO $ summaryRecGroups tlFunBindings
  return $ MMod (primBindings ++ funBindings) ts
    where
      -- defsByDefmutual = groupSortOn defMutual allDefs
      defsByDefmutual = [allDefs]
      act :: Definition -> TCM (Maybe (Either Binding (QName, TTerm)))
      act def@Defn{defName = q, theDef = d} = case d of
        Function{}                -> fmap Right <$> getBindings def
        Primitive{ primName = s } -> fmap Left <$> compilePrim q s
        Axiom{}                   -> fmap Left <$> compileAxiom q
        _                         -> return Nothing

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
  whenJust (_outputMlf opts) $ \fp -> liftIO $ runMalfunction fp modlTxt
  return modl

-- FIXME: I do realize that similar functionality exists in `Malfunction.Run` I
-- didn't use this because it also prints some stuff to stdout, so I felt it was
-- easier to just repeat these 3 lines of code.
-- | `runMalfunction fp inp` calls the malfunction compiler on the input `inp`
-- and places the output at `fp`. Assumes that the executable `malfunction` is
-- in `PATH`.
runMalfunction :: FilePath -> String -> IO ()
runMalfunction nm modl = takeBaseName nm `withSystemTempFile` \fp h -> do
  hPutStr h modl
  hFlush h
  callProcess "malfunction" ["compile", fp, "-o", nm]

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
    getName _ = Nothing

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
