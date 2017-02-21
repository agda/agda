module Backend (backend) where

import           Agda.Compiler.Backend
import           Agda.Utils.Pretty
import qualified Compiler              as Mlf
import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.Trans
import           Data.Bifunctor
import           Data.Either
import           Data.Function
import           Data.List
import           Data.List.Extra
import           Data.Map              (Map)
import qualified Data.Map              as Map
import           Data.Maybe
import           Malfunction.AST
import           Malfunction.Run
import           System.Console.GetOpt
import           Text.Printf

import           Primitive             (compilePrim)

backend :: Backend
backend = Backend backend'

data MlfOptions = Opts
  { _enabled    :: Bool
  , _resultVar  :: Maybe Ident
  , _outputFile :: Maybe FilePath
  , _debug      :: Bool
  }

defOptions :: MlfOptions
defOptions = Opts
  { _enabled    = False
  , _resultVar  = Nothing
  , _outputFile = Nothing
  , _debug      = False
  }

ttFlags :: [OptDescr (Flag MlfOptions)]
ttFlags =
  [ Option [] ["mlf"] (NoArg $ \ o -> return o{ _enabled = True })
    "Generate Malfunction"
  , Option ['r'] [] (ReqArg (\r o -> return o{_resultVar = Just r}) "VAR")
    "(DEBUG) Run the module and print the integer value of a variable"
  , Option ['o'] [] (ReqArg (\r o -> return o{_outputFile = Just r}) "FILE")
    "(DEBUG) Place outputFile resulting module into FILE"
  , Option ['d'] ["debug"] (NoArg $ \ o -> return o{ _enabled = True })
    "Generate Malfunction"
  ]

backend' :: Backend' MlfOptions MlfOptions () [Definition] Definition
backend' = Backend' {
  backendName = "malfunction"
  , options = defOptions
  , commandLineFlags = ttFlags
  , isEnabled = _enabled
  , preCompile = return
  , postCompile = mlfPostCompile --liftIO (putStrLn "post compile")
  , preModule = \enf m ifile -> return $ Recompile ()
  , compileDef = \env menv def -> return def
  , postModule = \env menv m mod defs -> return defs --mlfPostModule env defs
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
        _                         -> return Nothing

-- summaryRecGroups :: [[(QName,TTerm)]] -> IO ()
-- summaryRecGroups = putStrLn . intercalate "\n----------------\n" . map summaryRecGroup
--   where summaryRecGroup :: [(QName, TTerm)] -> String
--         summaryRecGroup g = intercalate ", " (map show qs)
--           where (qs, ts) = unzip g

getBindings :: Definition -> TCM (Maybe (QName, TTerm))
getBindings Defn{defName = q} = fmap (\t -> (q, t)) <$> toTreeless q

recGrp :: MlfOptions -> [Definition] -> [Definition] -> TCM (Maybe Binding)
recGrp opts allDefs defs = toGrp <$> bs
  where
    toGrp []  = Nothing
    toGrp [x] = Just x
    toGrp xs  = Just  . Recursive . concatMap bindingToPair $ xs
    bs = catMaybes <$> mapM (mlfDef opts allDefs) defs
    -- TODO: It's a bit ugly to take apart the bindings we just created.
    -- Also it's perhaps a bit ugly that *everything* get translated to groups
    -- of recursive bindings. We could e.g. handle the special case where
    -- there is only one definition.
    -- I've also discovered another restriction. All bindings in a `rec`-group
    -- have to be functions. Moreover, the groups can't contain unnamed bindings.
    bindingToPair :: Binding -> [(Ident, Term)]
    bindingToPair b = case b of
      Unnamed{}    -> error "Can't handle unnamed bindings in rec-groups"
      Recursive bs -> bs
      Named i t    -> [(i, t)]

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
mlfPostModule mlfopt defs = do
  modl <- mlfMod defs
  let modlTxt = prettyShow modl
  when (_debug mlfopt) $ liftIO . putStrLn $ modlTxt
  case _resultVar mlfopt of
    Just v  -> printVars modl [v]
    Nothing -> return ()
  case _outputFile mlfopt of
    Just fp -> liftIO $ writeFile fp modlTxt
    Nothing -> return ()
  return modl

printVars :: MonadIO m => Mod -> [Ident] -> m ()
printVars modl@(MMod binds _) vars = do
  liftIO (putStrLn "\n=======================")
  liftIO $
    if all defined vars
    then runModPrintInts vars modl >>= putStrLn
    else putStrLn "Variable not bound, did you specify the *fully quailified* name?"
    where
      defined v = any (defVar v) binds
      defVar v (Named u _) = u == v
      defVar _ _           = False

-- TODO: `mlfDef` should honor the flag "--debug" and only print to stdout in
-- case this is enabled. Also it would be nice to split up IO and the actual
-- translation into two different functions.
mlfDef :: MlfOptions -> [Definition] -> Definition -> TCM (Maybe Binding)
mlfDef opts alldefs d@Defn{ defName = q } =
  case theDef d of
    Function{} -> do
      mtt <- toTreeless q
      case mtt of
        Nothing -> return Nothing
        Just tt -> do
          logd . render
            $  header '=' (show q)
            $$ sect "Treeless (abstract syntax)"    (text . show $ tt)
            $$ sect "Treeless (concrete syntax)"    (pretty tt)
          let
            mlf = Mlf.translateDef' (getConstructors alldefs) q tt
          logd . render $
            sect "Malfunction (abstract syntax)" (text . show $ mlf)
            $$ sect "Malfunction (concrete syntax)" (pretty mlf)
          return (Just mlf)
            where
              sect t dc = text t $+$ nest 2 dc $+$ text ""
              header c h = let cs = replicate 15 c
                           in text $ printf "%s %s %s" cs h cs

    Primitive{ primName = s } -> compilePrim q s
    Axiom         -> return Nothing
    AbstractDefn  -> error "impossible"
    Datatype{}    -> liftIO (putStrLn $ "  data " ++ show q) >> return Nothing
    Record{}      -> liftIO (putStrLn $ "  record " ++ show q) >> return Nothing
    Constructor{} -> liftIO (putStrLn $ "  constructor " ++ show q) >> return Nothing
  where logd = liftIO . when (_debug opts) . putStrLn


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
