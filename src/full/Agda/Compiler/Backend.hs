{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Interface for compiler backend writers.
module Agda.Compiler.Backend
  ( Backend(..), Backend'(..), Recompile(..), IsMain(..)
  , Flag
  , toTreeless
  , module Agda.Syntax.Treeless
  , module Agda.TypeChecking.Monad
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

import Control.Monad.State
import Control.Monad.Trans.Maybe

import qualified Data.List as List
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as Map

import System.Console.GetOpt

import Agda.Syntax.Treeless
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
import Agda.Interaction.Imports (getAllWarnings)
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
  Backend :: Backend' opts env menv mod def -> Backend

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
  , postCompile      :: env -> IsMain -> Map ModuleName mod -> TCM ()
      -- ^ Called after module compilation has completed. The @IsMain@ argument
      --   is @NotMain@ if the @--no-main@ flag is present.
  , preModule        :: env -> IsMain -> ModuleName -> FilePath -> TCM (Recompile menv mod)
      -- ^ Called before compilation of each module. Gets the path to the
      --   @.agdai@ file to allow up-to-date checking of previously written
      --   compilation results. Should return @Skip m@ if compilation is not
      --   required.
  , postModule       :: env -> menv -> IsMain -> ModuleName -> [def] -> TCM mod
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

data Recompile menv mod = Recompile menv | Skip mod

-- | Call the 'compilerMain' function of the given backend.

callBackend :: String -> IsMain -> Interface -> TCM ()
callBackend name iMain i = lookupBackend name >>= \case
  Just (Backend b) -> compilerMain b iMain i
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
otherBackends = ["GHCNoMain", "LaTeX", "QuickLaTeX"]

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

-- Internals --------------------------------------------------------------

data BackendWithOpts opts where
  BackendWithOpts :: Backend' opts env menv mod def -> BackendWithOpts opts

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
      opts <- checkOpts opts
      return (forgetAll forgetOpts backends, opts)

backendInteraction :: [Backend] -> (TCM (Maybe Interface) -> TCM ()) -> TCM (Maybe Interface) -> TCM ()
backendInteraction [] fallback check = fallback check
backendInteraction backends _ check = do
  opts   <- commandLineOptions
  let backendNames = [ backendName b | Backend b <- backends ]
      err flag = genericError $ "Cannot mix --" ++ flag ++ " and backends (" ++ List.intercalate ", " backendNames ++ ")"
  when (optInteractive     opts) $ err "interactive"
  when (optGHCiInteraction opts) $ err "interaction"
  when (optJSONInteraction opts) $ err "interaction-json"
  mi     <- check

  -- reset warnings
  stTCWarnings `setTCLens` []

  noMain <- optCompileNoMain <$> pragmaOptions
  let isMain | noMain    = NotMain
             | otherwise = IsMain
  case mi of
    Nothing -> genericError $ "You can only compile modules without unsolved metavariables."
    Just i  -> sequence_ [ compilerMain backend isMain i | Backend backend <- backends ]

  -- print warnings that might have accumulated during compilation
  ws <- filter (not . isUnsolvedWarning . tcWarning) <$> getAllWarnings AllWarnings
  unless (null ws) $ reportSDoc "warning" 1 $ P.vcat $ P.prettyTCM <$> ws


compilerMain :: Backend' opts env menv mod def -> IsMain -> Interface -> TCM ()
compilerMain backend isMain0 i = inCompilerEnv i $ do
  locallyTC eActiveBackendName (const $ Just $ backendName backend) $ do
    onlyScoping <- optOnlyScopeChecking <$> commandLineOptions
    when (not (scopeCheckingSuffices backend) && onlyScoping) $
      genericError $
        "The --only-scope-checking flag cannot be combined with " ++
        backendName backend ++ "."

    -- Andreas, 2017-08-23, issue #2714
    -- If the backend is invoked from Emacs, we can only get the --no-main
    -- pragma option now, coming from the interface file.
    isMain <- ifM (optCompileNoMain <$> pragmaOptions)
      {-then-} (return NotMain)
      {-else-} (return isMain0)

    env  <- preCompile backend (options backend)
    mods <- doCompile isMain i $ \ isMain i -> Map.singleton (iModuleName i) <$> compileModule backend env isMain i
    setInterface i
    postCompile backend env isMain mods

compileModule :: Backend' opts env menv mod def -> env -> IsMain -> Interface -> TCM mod
compileModule backend env isMain i = do
  mName <- toTopLevelModuleName <$> curMName
  ifile <- maybe __IMPOSSIBLE__ (filePath . intFilePath) <$> findInterfaceFile mName
  r     <- preModule backend env isMain (iModuleName i) ifile
  case r of
    Skip m         -> return m
    Recompile menv -> do
      defs <- map snd . sortDefs <$> curDefs
      res  <- mapM (compileDef' backend env menv isMain <=< instantiateFull) defs
      postModule backend env menv isMain (iModuleName i) res

compileDef' :: Backend' opts env menv mod def -> env -> menv -> IsMain -> Definition -> TCM def
compileDef' backend env menv isMain def =
  setCurrentRange (defName def) $
    compileDef backend env menv isMain def
