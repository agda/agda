module Backend (backend) where

import           Agda.Compiler.Backend
import           Agda.Utils.Pretty
import qualified Compiler as Mlf
import           Control.Monad
import           Control.Monad.Trans
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.List
import           Data.Function
import           Malfunction.AST
import           Malfunction.Run
import           System.Console.GetOpt
import           Text.Printf

backend :: Backend
backend = Backend backend'

data MlfOptions = Opts {
  _enabled :: Bool
  , _resultVar :: Maybe Ident
  , _outputFile :: Maybe FilePath
  }

defOptions :: MlfOptions
defOptions = Opts {
  _enabled = False
  , _resultVar = Nothing
  , _outputFile = Nothing
  }

ttFlags :: [OptDescr (Flag MlfOptions)]
ttFlags =
  [ Option [] ["mlf"] (NoArg $ \ o -> return o{ _enabled = True })
    "Generate Malfunction"
  , Option ['r'] [] (ReqArg (\r o -> return o{_resultVar = Just r}) "VAR")
    "(DEBUG) Run the module and print the integer value of a variable"
  , Option ['o'] [] (ReqArg (\r o -> return o{_outputFile = Just r}) "FILE")
    "(DEBUG) Place outputFile resulting module into FILE"
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

mlfMod :: [Definition] -> [[Definition]] -> TCM Mod
mlfMod allDefs = fmap ((`MMod` []) . catMaybes) . mapM (recGrp allDefs)

recGrp :: [Definition] -> [Definition] -> TCM (Maybe Binding)
recGrp allDefs defs = toGrp <$> bs
  where
    toGrp [] = Nothing
    toGrp [x] = Just x
    toGrp xs = Just  . Recursive . concatMap bindingToPair $ xs
    bs = catMaybes <$> mapM (mlfDef allDefs) defs
    -- TODO: It's a bit ugly to take apart the bindings we just created.
    -- Also it's perhaps a bit ugly that *everything* get translated to groups
    -- of recursive bindings. We could e.g. handle the special case where
    -- there is only one definition.
    -- I've also discovered another restriction. All bindings in a `rec`-group
    -- have to be functions. Moreover, the groups can't contain unnamed bindings.
    bindingToPair :: Binding -> [(Ident, Term)]
    bindingToPair b = case b of
      Unnamed{} -> error "Can't handle unnamed bindings in rec-groups"
      Recursive bs -> bs
      Named i t -> [(i, t)]

mlfPostCompile :: MlfOptions -> IsMain -> Map ModuleName [Definition] -> TCM ()
mlfPostCompile opts _ modToDefs = do
  liftIO (putStrLn "sdlkfj")
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
  modl <- mlfMod defs . groupNSort $ defs
  let modlTxt = prettyShow modl
  liftIO . putStrLn $ modlTxt
  case _resultVar mlfopt of
    Just v   -> printVar modl v
    Nothing  -> return ()
  case _outputFile mlfopt of
    Just fp -> liftIO $ writeFile fp modlTxt
    Nothing -> return ()
  return modl
  where
    groupNSort :: [Definition] -> [[Definition]]
    groupNSort
      = sortBy (compare `on` defMutual . head)
      . groupBy ((==) `on` defMutual)

printVar :: MonadIO m => Mod -> Ident -> m ()
printVar modl@(MMod binds _) v = do
  liftIO (putStrLn "\n=======================")
  liftIO $
    if any defVar binds
    then runModPrintInts [v] modl >>= putStrLn
    else putStrLn "Variable not bound, did you specify the *fully quailified* name?"
    where
      defVar (Named u _) = u == v
      defVar _ = False

mlfDef :: [Definition] -> Definition -> TCM (Maybe Binding)
mlfDef alldefs d@Defn{ defName = q } =
  case theDef d of
    Function{} -> do
      mtt <- toTreeless q
      case mtt of
        Nothing -> return Nothing
        Just tt -> do
          liftIO . putStrLn . render
            $  header '=' (show q)
            $$ sect "Treeless (abstract syntax)"    (text . show $ tt)
            $$ sect "Treeless (concrete syntax)"    (pretty tt)
          let
            mlf = Mlf.translateDef' (getConstructors alldefs) q tt
          liftIO . putStrLn . render $
            sect "Malfunction (abstract syntax)" (text . show $ mlf)
            $$ sect "Malfunction (concrete syntax)" (pretty mlf)
          return (Just mlf)
            where
              sect t dc = text t $+$ nest 2 dc $+$ text ""
              header c h = let cs = replicate 15 c
                           in text $ printf "%s %s %s" cs h cs

    Primitive{ primName = s } ->
      liftIO (putStrLn $ "  primitive " ++ s) >> return Nothing
    Axiom         -> return Nothing
    AbstractDefn  -> error "impossible"
    Datatype{}    -> liftIO (putStrLn $ "  data " ++ show q) >> return Nothing
    Record{}      -> liftIO (putStrLn $ "  record " ++ show q) >> return Nothing
    Constructor{} -> liftIO (putStrLn $ "  constructor " ++ show q) >> return Nothing

-- | Returns all constructors for the given definition.
getConstructors :: [Definition] -> [[QName]]
getConstructors = mapMaybe (getCons . theDef)
  where
    getCons :: Defn -> Maybe [QName]
    getCons c@Datatype{} = Just (dataCons c)
    -- The way I understand it a record is just like a data-type
    -- except it only has one constructor and that one constructor
    -- takes as many arguments as the number of fields in that
    -- record.
    getCons c@Record{} = Just . pure . recCon $ c
    -- TODO: Stub value here!
    getCons _ = Nothing
