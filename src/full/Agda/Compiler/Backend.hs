{-# OPTIONS_GHC -Wunused-imports #-}

-- | Interface for compiler backend writers.
module Agda.Compiler.Backend
  ( module Agda.Compiler.Backend.Base
  , Recompile(..), IsMain(..)
  , Flag
  , toTreeless
  , module Agda.Syntax.Treeless
  , module Agda.TypeChecking.Monad
  , module CheckResult
    -- For Agda.Main
  , backendInteraction
  , parseBackendOptions
    -- For InteractionTop
  , callBackend
  , callBackendInteractTop
  , callBackendInteractHole
  ) where

import Prelude hiding (null)

import Control.DeepSeq

import qualified Data.Map as Map
import qualified Data.Set as Set

import System.Console.GetOpt

import Agda.Compiler.Backend.Base
import Agda.Compiler.Common
import Agda.Compiler.ToTreeless

import Agda.Interaction.Options
import Agda.Interaction.FindFile
import Agda.Interaction.Imports as CheckResult (CheckResult(CheckResult), crInterface, crWarnings, crMode)

import Agda.Syntax.Common (BackendName)
import Agda.Syntax.Treeless

import Agda.TypeChecking.Errors (getAllWarnings)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Warnings

import Agda.Utils.CallStack (HasCallStack)
import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.IndexedList
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Maybe
import Agda.Syntax.Common (InteractionId)
import Agda.Syntax.Position (Range)

import Agda.Interaction.Command (CommandM)

-- Public interface -------------------------------------------------------

-- | Call the 'compilerMain' function of the given backend.
callBackend :: BackendName -> IsMain -> CheckResult -> TCM ()
callBackend name iMain checkResult =
  withKnownBackend name $ \(Backend b) ->
    compilerMain b iMain checkResult

-- | Call the 'backendInteractTop' function of the given backend.
callBackendInteractTop :: BackendName -> String -> CommandM ()
callBackendInteractTop name cmd =
  withKnownBackend name $ \(Backend b) ->
    whenJust (backendInteractTop b) \bi ->
      bi cmd

-- | Call the 'backendInteractHole' function of the given backend.
callBackendInteractHole ::
  BackendName -> String -> InteractionId -> Range -> String -> CommandM ()
callBackendInteractHole name cmd ii rng s =
  withKnownBackend name $ \(Backend b) ->
    whenJust (backendInteractHole b) \bi ->
      bi cmd ii rng s

-- | Run a monadic action given an existing backend.
-- Throws an error if the user requested an unknown backend.
withKnownBackend ::
  (MonadTCError m, ReadTCState m) => BackendName -> (Backend -> m ()) -> m ()
withKnownBackend name k = ifJustM (lookupBackend name) k $ do
  backends <- useTC stBackends
  let backendSet = otherBackends ++ [ backendName b | Backend b <- backends ]
  typeError $ UnknownBackend name (Set.fromList backendSet)

-- | Backends that are not included in the state, but still available
--   to the user.
otherBackends :: [BackendName]
otherBackends = ["GHCNoMain", "QuickLaTeX"]

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

bOptions :: Lens' (BackendWithOpts opts) opts
bOptions f (BackendWithOpts b) = f (options b) <&> \ opts -> BackendWithOpts b{ options = opts }

embedFlag :: Lens' b a -> Flag a -> Flag b
embedFlag l flag = l flag

embedOpt :: Lens' b a -> OptDescr (Flag a) -> OptDescr (Flag b)
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

backendInteraction :: AbsolutePath -> [Backend] -> TCM () -> (AbsolutePath -> TCM CheckResult) -> TCM ()
backendInteraction mainFile backends setup check = do
  setup
  checkResult <- check mainFile

  -- reset warnings
  stTCWarnings `setTCLens` empty

  noMain <- optCompileNoMain <$> pragmaOptions
  let isMain | noMain    = NotMain
             | otherwise = IsMain

  sequence_ [ compilerMain backend isMain checkResult | Backend backend <- backends ]

  -- print warnings that might have accumulated during compilation
  ws <- filter (not . isUnsolvedWarning . tcWarning) . Set.toAscList <$> getAllWarnings AllWarnings
  unless (null ws) $ alwaysReportSDoc "warning" 1 $
    -- Andreas, 2024-09-06 start warning list by a newline
    -- since type checker warnings are also newline separated.
    -- See e.g. test/Succeed/CompileBuiltinListWarning.warn.
    -- Also separate warnings by newlines (issue #6919).
    vcat $ concatMap (\ w -> [ "", prettyTCM w ]) ws


compilerMain :: Backend' opts env menv mod def -> IsMain -> CheckResult -> TCM ()
compilerMain backend isMain0 checkResult = inCompilerEnv checkResult $ do
  locallyTC eActiveBackendName (const $ Just $ backendName backend) $ do
    -- BEWARE: Do not use @optOnlyScopeChecking@ here; it does not authoritatively describe the type-checking mode!
    -- InteractionTop currently may invoke type-checking with scope checking regardless of that flag.
    when (not (scopeCheckingSuffices backend) && crMode checkResult == ModuleScopeChecked) $
      typeError $ BackendDoesNotSupportOnlyScopeChecking $ backendName backend

    !i <- instantiateFull $ crInterface checkResult
    -- Andreas, 2017-08-23, issue #2714
    -- If the backend is invoked from Emacs, we can only get the --no-main
    -- pragma option now, coming from the interface file.
    !isMain <- ifM (optCompileNoMain <$> pragmaOptions)
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

compileModule :: HasCallStack => Backend' opts env menv mod def -> env -> IsMain -> Interface -> TCM mod
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
      res  <- mapM (compileDef' backend env menv isMain) defs
      postModule backend env menv isMain (iTopLevelModuleName i) res

compileDef' :: Backend' opts env menv mod def -> env -> menv -> IsMain -> Definition -> TCM def
compileDef' backend env menv isMain def =
  setCurrentRange (defName def) $
    compileDef backend env menv isMain def
