{-# LANGUAGE CPP #-}

{-| Agda main module.
-}
module Agda.Main where

import Prelude hiding (null)

import qualified Control.Exception as E
import Control.Monad          ( void )
import Control.Monad.Except   ( MonadError(..), ExceptT(..), runExceptT )
import Control.Monad.IO.Class ( MonadIO(..) )

import qualified Data.List as List
import Data.Function          ( (&) )
import Data.Functor
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Text as T

import System.Environment ( getArgs, getProgName )
import System.Exit ( exitSuccess, ExitCode )
import System.FilePath ( takeFileName )
import System.Console.GetOpt
import qualified System.IO as IO

import Agda.Interaction.CommandLine
import Agda.Interaction.ExitCode as ExitCode (AgdaError(..), exitSuccess, exitAgdaWith)
import Agda.Interaction.Options
import Agda.Interaction.Options.Help (Help (..))
import Agda.Interaction.EmacsTop (mimicGHCi)
import Agda.Interaction.JSONTop (jsonREPL)
import Agda.Interaction.FindFile ( SourceFile(SourceFile) )
import qualified Agda.Interaction.Imports as Imp

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Errors
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Pretty

import Agda.Compiler.Backend
import Agda.Compiler.Builtin

import Agda.Setup ( getAgdaAppDir, getDataDir, setup )
import Agda.Setup.EmacsMode
import Agda.VersionCommit ( versionWithCommitInfo )

import qualified Agda.Utils.Benchmark as UtilsBench
import qualified Agda.Syntax.Common.Pretty.ANSI as ANSI
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Utils.FileName (absolute, filePath, AbsolutePath)
import Agda.Utils.String
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null

import Agda.Utils.Impossible

-- | The main function
runAgda :: [Backend] -> IO ()
runAgda backends = runAgda' $ builtinBackends ++ backends

-- | The main function without importing built-in backends
runAgda' :: [Backend] -> IO ()
runAgda' backends = do
  progName <- getProgName
  argv     <- getArgs
  let (z, warns) = runOptM $ parseBackendOptions backends argv defaultOptions
  conf     <- runExceptT $ do
    (bs, opts) <- ExceptT $ pure z
    -- The absolute path of the input file, if provided
    inputFile <- liftIO $ mapM absolute $ optInputFile opts
    mode      <- getInteractor bs inputFile opts
    return (bs, opts, mode)

  case conf of
    Left err -> optionError err
    Right (bs, opts, mode) -> do

      -- Setup Agda if requested
      when (optSetup opts) $ Agda.Setup.setup True

      -- Print information as requested
      whenJust (optPrintVersion opts) $ printVersion bs
      whenJust (optPrintHelp    opts) $ printUsage   bs
      when (optPrintAgdaAppDir  opts) $ printAgdaAppDir
      when (optPrintAgdaDataDir opts) $ printAgdaDataDir

      -- Setup emacs mode
      when (EmacsModeSetup `Set.member` optEmacsMode opts) do
        unless (optSetup opts) $ Agda.Setup.setup False
        setupDotEmacs $ takeFileName progName

      -- Compile emacs mode
      when (EmacsModeCompile `Set.member` optEmacsMode opts) do
        unless (optSetup opts) $ Agda.Setup.setup False
        compileElispFiles

      -- Locate emacs mode
      when (EmacsModeLocate `Set.member` optEmacsMode opts) do
        unless (optSetup opts) $ Agda.Setup.setup False
        printEmacsModeFile

      case mode of
        Nothing -> do
          let
            something = or
              [ opts & optSetup
              , opts & optPrintVersion & isJust
              , opts & optPrintHelp    & isJust
              , opts & optPrintAgdaAppDir
              , opts & optPrintAgdaDataDir
              , opts & optEmacsMode    & not . null
              ]
          -- if no task was given to Agda
          unless something $ optionError "No task given."

        Just interactor -> do
         unless (optSetup opts) $ Agda.Setup.setup False

         runTCMPrettyErrors do

          mapM_ (warning . OptionWarning) warns

          when (optTransliterate opts) $ liftIO $ do
            -- When --interaction or --interaction-json is used, then we
            -- use UTF-8 when writing to stdout (and when reading from
            -- stdin).
            if optGHCiInteraction opts || optJSONInteraction opts
            then optionError $
                   "The option --transliterate must not be combined with " ++
                   "--interaction or --interaction-json"
            else do
              -- Transliterate unsupported code points.
              enc <- IO.mkTextEncoding (show IO.localeEncoding ++ "//TRANSLIT")
              IO.hSetEncoding IO.stdout enc
              IO.hSetEncoding IO.stderr enc

          setTCLens stBackends bs
          runAgdaWithOptions interactor progName opts


type Interactor a
    -- Setup/initialization action.
    -- This is separated so that errors can be reported in the appropriate format.
    = TCM ()
    -- Type-checking action
    -> (AbsolutePath -> TCM CheckResult)
    -- Main transformed action.
    -> TCM a

-- | Major mode of operation, not including the standard mode (checking the given main module).
data FrontendType
  = FrontEndInteraction InteractionFormat
      -- ^ @--interaction@ or @--interaction-json@.
  | FrontEndRepl
      -- ^ @--interactive@.

data InteractionFormat
  = InteractionEmacs
      -- ^ @--interaction@.
  | InteractionJson
      -- ^ @--interaction-json@.

pattern FrontEndEmacs :: FrontendType
pattern FrontEndEmacs = FrontEndInteraction InteractionEmacs

pattern FrontEndJson :: FrontendType
pattern FrontEndJson  = FrontEndInteraction InteractionJson

{-# COMPLETE FrontEndEmacs, FrontEndJson, FrontEndRepl #-}

-- | Emacs/JSON mode. Note that it ignores the "check" action because it calls typeCheck directly.
interactionInteractor :: InteractionFormat -> Interactor ()
interactionInteractor InteractionEmacs setup _check = mimicGHCi setup
interactionInteractor InteractionJson  setup _check = jsonREPL  setup

-- The deprecated repl mode.
replInteractor :: Maybe AbsolutePath -> Interactor ()
replInteractor = runInteractionLoop

-- The interactor to use when there are no frontends or backends specified.
defaultInteractor :: AbsolutePath -> Interactor ()
defaultInteractor file setup check = do setup; void $ check file

getInteractor :: MonadError String m => [Backend] -> Maybe AbsolutePath -> CommandLineOptions -> m (Maybe (Interactor ()))
getInteractor configuredBackends maybeInputFile opts = do

  case enabledFrontends of
    _:_:_ -> throwError $ concat ["Must not specify multiple ", enabledFrontendNames]

    -- standard mode of operation
    [] -> do
      case (maybeInputFile, enabledBackends) of
        (Just inputFile, _:_) -> return $ Just $ backendInteraction inputFile enabledBackends
        (Just inputFile,  []) -> return $ Just $ defaultInteractor inputFile
        (Nothing,         []) -> return Nothing -- No backends, frontends, or input files specified.
        (Nothing,        _:_) -> throwError $ concat ["No input file specified for ", enabledBackendNames]

    -- special mode of operation
    [fe] -> do
      case fe of
        -- --interactive
        FrontEndRepl -> do
          noBackends fe
          notJustScopeChecking fe
          return $ Just $ replInteractor maybeInputFile
        -- --interaction(-json)
        FrontEndInteraction i -> do
          noBackends fe
          notJustScopeChecking fe
          noInputFile fe
          return $ Just $ interactionInteractor i
  where
    -- NOTE: The notion of a backend being "enabled" *just* refers to this top-level interaction mode selection. The
    -- interaction/interactive front-ends may still invoke available backends even if they are not "enabled".
    isBackendEnabled (Backend b) = isEnabled b (options b)
    enabledBackends = filter isBackendEnabled configuredBackends
    enabledFrontends = concat
      [ [ FrontEndRepl  | optInteractive     opts ]
      , [ FrontEndEmacs | optGHCiInteraction opts ]
      , [ FrontEndJson  | optJSONInteraction opts ]
      ]
    -- Constructs messages like "(no backend)", "backend ghc", "backends (ghc, ocaml)"
    pluralize w []  = concat ["(no ", w, ")"]
    pluralize w [x] = concat [w, " ", x]
    pluralize w xs  = concat [w, "s (", List.intercalate ", " xs, ")"]
    enabledBackendNames  = pluralize "backend" [ T.unpack $ backendName b | Backend b <- enabledBackends ]
    enabledFrontendNames = pluralize "frontend" (frontendFlagName <$> enabledFrontends)
    frontendFlagName = ("--" ++) . \case
      FrontEndEmacs -> "interaction"
      FrontEndJson -> "interaction-json"
      FrontEndRepl -> "interactive"
    noBackends fe = unless (null enabledBackends) $
      throwError $ concat ["Cannot mix ", frontendFlagName fe, " with ", enabledBackendNames]
    noInputFile fe = whenJust maybeInputFile \ inputFile -> errorFrontendFileDisallowed inputFile fe
    notJustScopeChecking = when (optOnlyScopeChecking opts) . errorFrontendScopeChecking
    errorFrontendScopeChecking fe = throwError $
      concat ["The --only-scope-checking flag cannot be combined with ", frontendFlagName fe]
    errorFrontendFileDisallowed inputFile fe = throwError $
      concat ["Must not specify an input file (", filePath inputFile, ") with ", frontendFlagName fe]

-- | Run Agda with parsed command line options
runAgdaWithOptions
  :: Interactor a       -- ^ Backend interaction
  -> String             -- ^ program name
  -> CommandLineOptions -- ^ parsed command line options
  -> TCM a
runAgdaWithOptions interactor progName opts = do
          -- Main function.
          -- Bill everything to root of Benchmark trie.
          UtilsBench.setBenchmarking UtilsBench.BenchmarkOn
            -- Andreas, Nisse, 2016-10-11 AIM XXIV
            -- Turn benchmarking on provisionally, otherwise we lose track of time spent
            -- on e.g. LaTeX-code generation.
            -- Benchmarking might be turned off later by setCommandlineOptions

          Bench.billTo [] $
            interactor initialSetup checkFile
          `finally_` do
            -- Print benchmarks.
            Bench.print

            -- Print accumulated statistics.
            printStatistics Nothing =<< useTC lensAccumStatistics
  where
    -- Options are fleshed out here so that (most) errors like
    -- "bad library path" are validated within the interactor,
    -- so that they are reported with the appropriate protocol/formatting.
    initialSetup :: TCM ()
    initialSetup = do
      opts <- addTrustedExecutables opts
      setCommandLineOptions opts

    checkFile :: AbsolutePath -> TCM CheckResult
    checkFile inputFile = do
        -- Andreas, 2013-10-30 The following 'resetState' kills the
        -- verbosity options.  That does not make sense (see fail/Issue641).
        -- 'resetState' here does not seem to serve any purpose,
        -- thus, I am removing it.
        -- resetState
          let mode = if optOnlyScopeChecking opts
                     then Imp.ScopeCheck
                     else Imp.TypeCheck

          src <- srcFromPath inputFile
          result <- Imp.typeCheckMain mode =<< Imp.parseSource src

          unless (crMode result == ModuleScopeChecked) $
            Imp.raiseNonFatalErrors result

          let i = crInterface result
          reportSDoc "main" 50 $ pretty i

          -- Print accumulated warnings
          unlessNullM (tcWarnings . classifyWarnings . Set.toAscList <$> getAllWarnings AllWarnings) $ \ ws -> do
            let banner = text $ "\n" ++ delimiter "All done; warnings encountered"
            alwaysReportSDoc "warning" 1 $
              vsep $ (banner :) $ map prettyTCM $ Set.toAscList ws

          return result



-- | Print usage information.
printUsage :: [Backend] -> Help -> IO ()
printUsage backends hp = do
  progName <- getProgName
  putStr $ usage standardOptions_ progName hp
  when (hp == GeneralHelp) $ mapM_ (putStr . backendUsage) backends

backendUsage :: Backend -> String
backendUsage (Backend b) =
  usageInfo ("\n" ++ T.unpack (backendName b) ++ " backend options") $
    map void (commandLineFlags b)

-- | Print version information.
printVersion :: [Backend] -> PrintAgdaVersion -> IO ()
printVersion _ PrintAgdaNumericVersion = putStrLn versionWithCommitInfo
printVersion backends PrintAgdaVersion = do
  putStrLn $ "Agda version " ++ versionWithCommitInfo
  unless (null flags) $
    mapM_ putStrLn $ ("Built with flags (cabal -f)" :) $ map bullet flags
  mapM_ putStrLn
    [ bullet $ T.unpack $ T.unwords [ name, "backend version", ver ]
    | Backend Backend'{ backendName = name, backendVersion = Just ver } <- backends ]
  where
  bullet = (" - " ++)
  -- Print cabal flags that were involved in compilation.
  flags =
#ifdef COUNT_CLUSTERS
    "enable-cluster-counting: unicode cluster counting in LaTeX backend using the ICU library" :
#endif
#ifdef OPTIMISE_HEAVILY
    "optimise-heavily: extra optimisations" :
#endif
#ifdef DEBUG
    "debug: enable debug printing ('-v' verbosity flags)" :
#endif
#ifdef DEBUG_PARSING
    "debug-parsing: enable printing grammars for operator parsing via '-v scope.grammar:10'" :
#endif
#ifdef DEBUG_SERIALISATION
    "debug-serialisation: extra debug info during serialisation into '.agdai' files" :
#endif
    []

printAgdaDataDir :: IO ()
printAgdaDataDir = putStrLn =<< getDataDir

printAgdaAppDir :: IO ()
printAgdaAppDir = putStrLn =<< getAgdaAppDir

-- | What to do for bad options.
optionError :: String -> IO ()
optionError err = do
  prog <- getProgName
  putStrLn $ "Error: " ++ err ++ "\nRun '" ++ prog ++ " --help' for help on command line options."
  exitAgdaWith ExitCode.OptionError

-- | Run a TCM action in IO; catch and pretty print errors.

-- If some error message cannot be printed due to locale issues, then
-- one may get the "Error when handling error" error message. There is
-- currently no test case for this error, but on some systems one can
-- (at the time of writing) trigger it by running @LC_CTYPE=C agda
-- --no-libraries Bug.agda@, where @Bug.agda@ contains the following
-- code (if there is some other file in the same directory, for
-- instance @Bug.lagda@, then the error message may be different):
--
-- @
-- _ : Set
-- _ = Set
-- @

runTCMPrettyErrors :: TCM () -> IO ()
runTCMPrettyErrors tcm = do
  r <- runTCMTop
    ( ( (Nothing <$ tcm)
          `catchError` \err -> do
            s2s <- prettyTCWarnings' =<< getAllWarningsOfTCErr err
            s1  <- prettyError err
            ANSI.putDoc $ P.vsep $ s2s ++ [ s1 ]
            liftIO $ do
              helpForLocaleError err
            return (Just TCMError)
      ) `catchImpossible` \e -> do
          printException e
          return (Just ImpossibleError)
    ) `E.catches`
        -- Catch all exceptions except for those of type ExitCode
        -- (which are thrown by exitWith) and asynchronous exceptions
        -- (which are for instance raised when Ctrl-C is used, or if
        -- the program runs out of heap or stack space).
        [ E.Handler $ \(e :: ExitCode)         -> E.throw e
        , E.Handler $ \(e :: E.AsyncException) -> E.throw e
        , E.Handler $ \(e :: E.SomeException)  -> do
            printException e
            return $ Right (Just UnknownError)
        ]
  case r of
    Right Nothing       -> exitSuccess
    Right (Just reason) -> exitAgdaWith reason
    Left err            -> do
      liftIO $ do
        putStrLn "\n\nError when handling error:"
        putStrLn $ tcErrString err
        helpForLocaleError err
      exitAgdaWith UnknownError
  where
    printException e = liftIO $ putStr $
      -- Andreas, 2024-07-03, issue #7299
      -- Regression in base-4.20: printing of exception produces trailing whitespace.
      -- https://gitlab.haskell.org/ghc/ghc/-/issues/25052
#if MIN_VERSION_base(4,20,0)
      rtrim $
#endif
      E.displayException e

-- | If the error is an IO error, and the error message suggests that
-- the problem is related to locales or code pages, print out some
-- extra information.

helpForLocaleError :: TCErr -> IO ()
helpForLocaleError e = case e of
  (IOException _ _ e)
    | "invalid argument" `List.isInfixOf` show e -> msg
  _                                              -> return ()
  where
  msg = putStr $ unlines
    [ ""
    , "This error may be due to the use of a locale or code page that does not"
    , "support some character used in the program being type-checked."
    , ""
    , "If it is, then one option is to use the option --transliterate, in which"
    , "case unsupported characters are (hopefully) replaced with something else,"
    , "perhaps question marks. However, that could make the output harder to"
    , "read."
    , ""
    , "If you want to fix the problem \"properly\", then you could try one of the"
    , "following suggestions:"
    , ""
    , "* If you are using Windows, try switching to a different code page (for"
    , "  instance by running the command 'CHCP 65001')."
    , ""
    , "* If you are using a Unix-like system, try using a different locale. The"
    , "  installed locales are perhaps printed by the command 'locale -a'. If"
    , "  you have a UTF-8 locale installed (for instance sv_SE.UTF-8), then you"
    , "  can perhaps make Agda use this locale by running something like"
    , "  'LC_ALL=sv_SE.UTF-8 agda <...>'."
    ]
