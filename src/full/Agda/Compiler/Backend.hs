{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}


-- | Interface for compiler backend writers.
module Agda.Compiler.Backend
  ( Backend(..), Backend'(..), Recompile(..), IsMain(..)
  , Flag
  , toTreeless
  , module Agda.Syntax.Treeless
  , module Agda.TypeChecking.Monad
  , module CheckResult
  , activeBackendMayEraseType
    -- For Agda.Main
  , backendInteraction
  , parseBackendOptions
    -- For InteractionTop
  , callBackend
    -- Tools
  , lookupBackend
  , activeBackend
  ) where

import Control.DeepSeq
import Control.Monad              ( (<=<) )
import Control.Monad.Trans        ( lift )
import Control.Monad.Trans.Maybe

import qualified Data.List as List
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as Map

import GHC.Generics (Generic)

import System.Console.GetOpt

import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Treeless
import Agda.TypeChecking.Errors (getAllWarnings)
-- Agda.TypeChecking.Monad.Base imports us, relying on the .hs-boot file to
-- resolve the circular dependency. Fine. However, ghci loads the module after
-- compilation, so it brings in all of the symbols. That causes .Base to see
-- getBenchmark (defined in Agda.TypeChecking.Monad.State) *and* the one
-- defined in Agda.Utils.Benchmark, which causes an error. So we explicitly
-- hide it here to prevent it from being seen there and causing an error.
import Agda.TypeChecking.Monad hiding (getBenchmark)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty as P

import Agda.Interaction.Options
import Agda.Interaction.FindFile
import Agda.Interaction.Imports as CheckResult (CheckResult(CheckResult), crInterface, crWarnings, crMode)
import Agda.TypeChecking.Warnings

import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.IndexedList
import Agda.Utils.Lens
import Agda.Utils.Monad

import Agda.Compiler.ToTreeless
import Agda.Compiler.Common

import Agda.Utils.Impossible

-- Public interface -------------------------------------------------------

data Backend where
  Backend :: NFData opts => Backend' opts env menv mod def -> Backend

data Backend' opts env menv mod def = Backend'
  { backendName      :: String
  , backendVersion   :: Maybe String
      -- ^ Optional version information to be printed with @--version@.
  , options          :: opts
      -- ^ Default options
  , commandLineFlags :: [OptDescr (Flag opts)]
      -- ^ Backend-specific command-line flags. Should at minimum contain a
      --   flag to enable the backend.
  , isEnabled        :: opts -> Bool
      -- ^ Unless the backend has been enabled, @runAgda@ will fall back to
      --   vanilla Agda behaviour.
  , preCompile       :: opts -> TCM env
      -- ^ Called after type checking completes, but before compilation starts.
  , postCompile      :: env -> IsMain -> Map TopLevelModuleName mod ->
                        TCM ()
      -- ^ Called after module compilation has completed. The @IsMain@ argument
      --   is @NotMain@ if the @--no-main@ flag is present.
  , preModule        :: env -> IsMain -> TopLevelModuleName ->
                        Maybe FilePath -> TCM (Recompile menv mod)
      -- ^ Called before compilation of each module. Gets the path to the
      --   @.agdai@ file to allow up-to-date checking of previously written
      --   compilation results. Should return @Skip m@ if compilation is not
      --   required. Will be @Nothing@ if only scope checking.
  , postModule       :: env -> menv -> IsMain -> TopLevelModuleName ->
                        [def] -> TCM mod
      -- ^ Called after all definitions of a module have been compiled.
  , compileDef       :: env -> menv -> IsMain -> Definition -> TCM def
      -- ^ Compile a single definition.
  , scopeCheckingSuffices :: Bool
      -- ^ True if the backend works if @--only-scope-checking@ is used.
  , mayEraseType     :: QName -> TCM Bool
      -- ^ The treeless compiler may ask the Backend if elements
      --   of the given type maybe possibly erased.
      --   The answer should be 'False' if the compilation of the type
      --   is used by a third party, e.g. in a FFI binding.
  }
  deriving Generic

data Recompile menv mod = Recompile menv | Skip mod

-- | Call the 'compilerMain' function of the given backend.

callBackend :: String -> IsMain -> CheckResult -> TCM ()
callBackend name iMain checkResult = lookupBackend name >>= \case
  Just (Backend b) -> compilerMain b iMain checkResult
  Nothing -> do
    backends <- useTC stBackends
    genericError $
      "No backend called '" ++ name ++ "' " ++
      "(installed backends: " ++
      List.intercalate ", "
        (List.sort $ otherBackends ++
                     [ backendName b | Backend b <- backends ]) ++
      ")"

-- | Backends that are not included in the state, but still available
--   to the user.

otherBackends :: [String]
otherBackends = ["GHCNoMain", "QuickLaTeX"]

-- | Look for a backend of the given name.

lookupBackend :: BackendName -> TCM (Maybe Backend)
lookupBackend name = useTC stBackends <&> \ backends ->
  listToMaybe [ b | b@(Backend b') <- backends, backendName b' == name ]

-- | Get the currently active backend (if any).

activeBackend :: TCM (Maybe Backend)
activeBackend = runMaybeT $ do
  bname <- MaybeT $ asksTC envActiveBackendName
  lift $ fromMaybe __IMPOSSIBLE__ <$> lookupBackend bname

-- | Ask the active backend whether a type may be erased.
--   See issue #3732.

activeBackendMayEraseType :: QName -> TCM Bool
activeBackendMayEraseType q = do
  Backend b <- fromMaybe __IMPOSSIBLE__ <$> activeBackend
  mayEraseType b q

instance NFData Backend where
  rnf (Backend b) = rnf b

instance NFData opts => NFData (Backend' opts env menv mod def) where
  rnf (Backend' a b c d e f g h i j k l) =
    rnf a `seq` rnf b `seq` rnf c `seq` rnf' d `seq` rnf e `seq`
    rnf f `seq` rnf g `seq` rnf h `seq` rnf i `seq` rnf j `seq`
    rnf k `seq` rnf l
    where
    rnf' []                   = ()
    rnf' (Option a b c d : e) =
      rnf a `seq` rnf b `seq` rnf'' c `seq` rnf d `seq` rnf' e

    rnf'' (NoArg a)    = rnf a
    rnf'' (ReqArg a b) = rnf a `seq` rnf b
    rnf'' (OptArg a b) = rnf a `seq` rnf b

-- Internals --------------------------------------------------------------

data BackendWithOpts opts where
  BackendWithOpts ::
    NFData opts =>
    Backend' opts env menv mod def ->
    BackendWithOpts opts

backendWithOpts :: Backend -> Some BackendWithOpts
backendWithOpts (Backend backend) = Some (BackendWithOpts backend)

forgetOpts :: BackendWithOpts opts -> Backend
forgetOpts (BackendWithOpts backend) = Backend backend

bOptions :: Lens' opts (BackendWithOpts opts)
bOptions f (BackendWithOpts b) = f (options b) <&> \ opts -> BackendWithOpts b{ options = opts }

embedFlag :: Lens' a b -> Flag a -> Flag b
embedFlag l flag = l flag

embedOpt :: Lens' a b -> OptDescr (Flag a) -> OptDescr (Flag b)
embedOpt l = fmap (embedFlag l)

parseBackendOptions :: [Backend] -> [String] -> CommandLineOptions -> OptM ([Backend], CommandLineOptions)
parseBackendOptions backends argv opts0 =
  case makeAll backendWithOpts backends of
    Some bs -> do
      let agdaFlags    = map (embedOpt lSnd) (deadStandardOptions ++ standardOptions)
          backendFlags = do
            Some i            <- forgetAll Some $ allIndices bs
            BackendWithOpts b <- [lookupIndex bs i]
            opt               <- commandLineFlags b
            return $ embedOpt (lFst . lIndex i . bOptions) opt
      (backends, opts) <- getOptSimple (stripRTS argv)
                                       (agdaFlags ++ backendFlags) (embedFlag lSnd . inputFlag)
                                       (bs, opts0)
      () <- checkOpts opts
      return (forgetAll forgetOpts backends, opts)

backendInteraction :: AbsolutePath -> [Backend] -> TCM () -> (AbsolutePath -> TCM CheckResult) -> TCM ()
backendInteraction mainFile backends setup check = do
  setup
  checkResult <- check mainFile

  -- reset warnings
  stTCWarnings `setTCLens` []

  noMain <- optCompileNoMain <$> pragmaOptions
  let isMain | noMain    = NotMain
             | otherwise = IsMain

  unlessM (optAllowUnsolved <$> pragmaOptions) $ do
    let ws = crWarnings checkResult
        mode = crMode checkResult
    -- Possible warnings, but only scope checking: ok.
    -- (Compatibility with scope checking done during options validation).
    unless (mode == ModuleScopeChecked || null ws) $
      genericError $ "You can only compile modules without unsolved metavariables."

  sequence_ [ compilerMain backend isMain checkResult | Backend backend <- backends ]

  -- print warnings that might have accumulated during compilation
  ws <- filter (not . isUnsolvedWarning . tcWarning) <$> getAllWarnings AllWarnings
  unless (null ws) $ reportSDoc "warning" 1 $ P.vcat $ P.prettyTCM <$> ws


compilerMain :: Backend' opts env menv mod def -> IsMain -> CheckResult -> TCM ()
compilerMain backend isMain0 checkResult = inCompilerEnv checkResult $ do
  locallyTC eActiveBackendName (const $ Just $ backendName backend) $ do
    -- BEWARE: Do not use @optOnlyScopeChecking@ here; it does not authoritatively describe the type-checking mode!
    -- InteractionTop currently may invoke type-checking with scope checking regardless of that flag.
    when (not (scopeCheckingSuffices backend) && crMode checkResult == ModuleScopeChecked) $
      genericError $
        "The --only-scope-checking flag cannot be combined with " ++
        backendName backend ++ "."

    let i = crInterface checkResult
    -- Andreas, 2017-08-23, issue #2714
    -- If the backend is invoked from Emacs, we can only get the --no-main
    -- pragma option now, coming from the interface file.
    isMain <- ifM (optCompileNoMain <$> pragmaOptions)
      {-then-} (return NotMain)
      {-else-} (return isMain0)

    env  <- preCompile backend (options backend)
    mods <- doCompile
        -- This inner function is called for both `Agda.Primitive` and the module in question,
        -- and all (distinct) imported modules. So avoid shadowing "isMain" or "i".
        (\ifaceIsMain iface ->
          Map.singleton (iTopLevelModuleName iface) <$>
          compileModule backend env ifaceIsMain iface)
        isMain i
    -- Note that `doCompile` calls `setInterface` for each distinct module in the graph prior to calling into
    -- `compileModule`. This last one is just to ensure it's reset to _this_ module.
    setInterface i
    postCompile backend env isMain mods

compileModule :: Backend' opts env menv mod def -> env -> IsMain -> Interface -> TCM mod
compileModule backend env isMain i = do
  mName <- curMName
  -- The interface file will only exist if performing af full type-check, vs scoping.
  -- FIXME: Expecting backends to read the timestamp of the output path of the interface
  --        file for dirtiness checking is very roundabout and heavily couples backend
  --        implementations to the filesystem as the source of cache state.
  mifile <- (Just . filePath . intFilePath =<<) <$> findInterfaceFile mName
  r      <- preModule backend env isMain (iTopLevelModuleName i) mifile
  case r of
    Skip m         -> return m
    Recompile menv -> do
      defs <- map snd . sortDefs <$> curDefs
      res  <- mapM (compileDef' backend env menv isMain <=< instantiateFull) defs
      postModule backend env menv isMain (iTopLevelModuleName i) res

compileDef' :: Backend' opts env menv mod def -> env -> menv -> IsMain -> Definition -> TCM def
compileDef' backend env menv isMain def =
  setCurrentRange (defName def) $
    compileDef backend env menv isMain def
