import Control.Exception
import Control.Monad
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Time.Clock
import GHC.IO.Encoding
import Options.Applicative
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.Posix.Signals
import System.Process
import Text.PrettyPrint.ANSI.Leijen hiding ((<>), (<$>), (</>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Text.Printf

-- | A string used to detect internal errors.

internalErrorString :: String
internalErrorString =
  "An internal error has occurred. Please report this as a bug."

-- | Strings that are used to signal to continuous integration systems
-- that this commit should be skipped.

ciSkipStrings :: [String]
ciSkipStrings = ["[ci skip]", "[skip ci]"]

-- | Default flags given to Agda.

defaultFlags :: [String]
defaultFlags =
  [ "--ignore-interfaces"
  , "--no-default-libraries"
  , "--no-libraries"
  ]

-- | Default flags given to cabal v1-install (excludes some flags that
-- cannot be overridden).

defaultCabalFlags :: [String]
defaultCabalFlags =
  [ "--ghc-option=-O0"
  ]

-- | An absolute path to the compiled Agda executable. (If caching is
-- not enabled.)

compiledAgda :: IO FilePath
compiledAgda =
  (</> ".cabal-sandbox/bin/agda") <$> getCurrentDirectory

-- | Options.

data Options = Options
  { mustSucceed               :: Bool
  , mustOutput, mustNotOutput :: [String]
  , noInternalError           :: Bool
      -- ^ Implies \"must-fail\" and \"must-not-output\"
      -- 'internalErrorString'.
  , mustFinishWithin          :: Maybe Int
  , extraArguments            :: Bool
  , compiler                  :: Maybe String
  , defaultCabalOptions       :: Bool
  , cabalOptions              :: [String]
  , skipStrings               :: [String]
  , onlyOnBranches            :: [String]
  , skipBranches              :: [String]
  , cacheBuilds               :: Bool
  , logFile                   :: Maybe String
  , start                     :: Either FilePath (String, String)
  , dryRun                    :: Maybe (Either FilePath String)
  , scriptOrArguments         :: Either (FilePath, [String]) [String]
  }

-- | Parses command-line options. Prints usage information and aborts
-- this program if the options are malformed (or the help flag is
-- given).

options :: IO Options
options =
  execParser
    (info (helper <*> (fixOptions <$> opts))
          (header "Git bisect wrapper script for the Agda code base" <>
           footerDoc (Just msg)))
  where
  opts = Options
    <$> (not <$>
         (switch $
            long "must-fail" <>
            help "The command must fail (by default it must succeed)"))
    <*> many
          (strOption (long "must-output" <>
                      help "The command must output STRING" <>
                      metavar "STRING"))
    <*> many
          (strOption (long "must-not-output" <>
                      help "The command must not output STRING" <>
                      metavar "STRING"))
    <*> switch
          (long "no-internal-error" <>
           help (unwords
             [ "The command must not output"
             , show internalErrorString ++ ";"
             , "implies --must-fail"
             ]))
    <*> (optional $
           option
             (do n <- auto
                 if n < 0 || n > maxBound then
                   readerError "Argument out of range"
                  else
                   return n)
             (long "timeout" <>
              metavar "N" <>
              help ("The command must finish in less than " ++
                    "(approximately) N seconds; implies " ++
                    "--no-default-cabal-options")))
    <*> (not <$>
         switch (long "no-extra-arguments" <>
                 help "Do not give any extra arguments to Agda"))
    <*> optional
          (strOption (long "compiler" <>
                      help "Use COMPILER to compile Agda" <>
                      metavar "COMPILER" <>
                      action "command"))
    <*> (not <$>
         switch
           (long "no-default-cabal-options" <>
            help (unwords
              [ "Do not (by default) give certain options to cabal"
              , "v1-install"
              ])))
    <*> many
          (strOption
             (long "cabal-option" <>
              help "Additional option given to cabal v1-install" <>
              metavar "OPTION" <>
              completer (commandCompleter "cabal"
                           ["v1-install", "--list-options"])))
    <*> ((\skip -> if skip then ciSkipStrings else []) <$>
         switch (long "skip-skipped" <>
                 help ("Skip commits with commit messages " ++
                       "containing one of the following strings: " ++
                       intercalate ", " (map show ciSkipStrings))))
    <*> many (strOption (long "on-branch" <>
                         help ("Skip commits that are not on BRANCH " ++
                               "(if this option is repeated, then " ++
                               "commits that are not on any of the " ++
                               "given branches are skipped)") <>
                         metavar "BRANCH" <>
                         completer branchCompleter))
    <*> many (strOption (long "not-on-branch" <>
                         help "Skip commits that are on BRANCH" <>
                         metavar "BRANCH" <>
                         completer branchCompleter))
    <*> switch (long "cache" <>
                help "Cache builds")
    <*> optional
          (strOption (long "log" <>
                      help "Store a git bisect log in FILE" <>
                      metavar "FILE" <>
                      action "file"))
    <*> (((\b g -> Right (b, g)) <$>
          strOption (long "bad" <>
                     metavar "BAD" <>
                     help "Bad commit" <>
                     completer commitCompleter) <*>
          strOption (long "good" <>
                     metavar "GOOD" <>
                     help "Good commit" <>
                     completer commitCompleter))
           <|>
         (Left <$>
          strOption (long "replay" <>
                     metavar "LOG" <>
                     help ("Replay the git bisect log in LOG " ++
                           "(which is assumed to be well-formed)") <>
                     action "file")))
    <*> optional
          ((Left <$>
            strOption (long "dry-run" <>
                       metavar "AGDA" <>
                       action "command" <>
                       help ("Do not run git bisect, just run the " ++
                             "test once using AGDA")))
             <|>
           (Right <$>
            strOption (long "dry-run-with-commit" <>
                       metavar "C" <>
                       completer commitCompleter <>
                       help ("Do not run git bisect, just run the " ++
                             "test once using commit C"))))
    <*> ((Right <$>
          many (strArgument (metavar "ARGUMENTS..." <>
                             help "The arguments supplied to Agda")))
           <|>
         ((\prog args -> Left (prog, args)) <$>
          strOption (long "script" <>
                     metavar "PROGRAM" <>
                     help ("Do not invoke Agda directly, run " ++
                           "PROGRAM instead") <>
                     action "command") <*>
          many
            (strArgument (metavar "PROGRAM ARGUMENTS..." <>
                          help ("Extra arguments for the " ++
                                "--script program")))))

  -- | Substantiates implied options, e.g. those implied by
  -- 'noInternalError'. Note that this function is not idempotent.

  fixOptions :: Options -> Options
  fixOptions = fix3 . fix2 . fix1
    where
    fix1 opt
      | noInternalError opt = opt
          { mustSucceed   = False
          , mustNotOutput = internalErrorString : mustNotOutput opt
          }
      | otherwise = opt

    fix2 opt = case mustFinishWithin opt of
      Nothing -> opt
      Just _  -> opt { defaultCabalOptions = False }

    fix3 opt
      | defaultCabalOptions opt = opt
          { cabalOptions = defaultCabalFlags ++ cabalOptions opt
          }
      | otherwise = opt

  paragraph ss      = fillSep (map string $ words $ unlines ss)
  d1 `newline` d2   = d1 PP.<> hardline PP.<> d2
  d1 `emptyLine` d2 = d1 PP.<> hardline PP.<> hardline PP.<> d2

  msg = foldr1 emptyLine
    [ paragraph
        [ "For every step of the bisection process this script tries to"
        , "compile Agda, run the resulting program (if any) with the"
        , "given arguments, and determine if the result is"
        , "satisfactory. (When --timeout is used an unsatisfactory"
        , "run that does not time out is treated as an install"
        , "failure.)"
        ]

    , paragraph
        [ "Start the script from the root directory of an Agda"
        , "repository. The script takes care of invoking various"
        , "\"git bisect\" subcommands (start, replay, reset, good,"
        , "bad, skip). Feel free to use \"git bisect visualize\" or"
        , "\"git bisect log\" to inspect the script's progress."
        ]

    , paragraph
        [ "Use \"--\" to signal that the remaining arguments are"
        , "not options to this script (but to Agda or the --script"
        , "program)."
        ]

    , paragraph
        [ "The script gives the following options to cabal v1-install,"
        , "unless --no-default-cabal-options has been given:"
        ] `newline`
      indent 2 (foldr1 newline $ map string defaultCabalFlags)
        `newline`
      paragraph
        [ "(Other options are also given to cabal v1-install.)"
        ]

    , paragraph
        [ "The script inserts the following flags before ARGUMENTS,"
        , "unless --no-extra-arguments has been given (and only those"
        , "options which agda --help indicates are available):"
        ] `newline`
      indent 2 (foldr1 newline $ map string defaultFlags)

    , paragraph
        [ "The --script program, if any, is called with a path to the"
        , "Agda executable as the first argument. (If --dry-run is not"
        , "used, then this path is absolute.) Note that usual platform"
        , "conventions (like the PATH) are used to determine what"
        , "program PROGRAM refers to. If the script's exit code is 127,"
        , "then this is treated as an install failure."
        ]

    , paragraph
        [ "If --cache is used then compiled binaries are cached, and if"
        , "the current commit has already been cached, then it is not"
        , "rebuilt. An attempt is made to copy data files, but this"
        , "attempt could fail (and in that case the bisection process"
        , "is not interrupted). The library is not installed, tests"
        , "that rely on the Agda library should not use this option."
        , "Note that no attempt is made to control the bisection"
        , "process so that cached commits are preferred over other"
        , "ones."
        ]

    , paragraph
        [ "By default Agda is compiled without optimisation (to reduce"
        , "compilation times). For this reason a separate cache is used"
        , "when --timeout is active. When --timeout is not active"
        , "programs from either cache can be used."
        ]

    , paragraph
        [ "You should install suitable versions of the following"
        , "commands before running the script (in addition to any"
        , "programs invoked by cabal v1-install):"
        ] PP.<$>
      indent 2 (fillSep $ map string ["cabal", "git", "sed", "timeout"])

    , paragraph
        [ "The script may not work on all platforms." ]
    ]

  -- Constructs completions by running a command. The command's output
  -- is assumed to be encoded using UTF-8, and to contain one possible
  -- completion per line.
  commandCompleter prog args = mkCompleter $ \prefix -> do
    (code, out, _) <- withUTF8Ignore $
                        readProcessWithExitCode prog args ""
    return $
      if code == ExitSuccess then
        filter (prefix `isPrefixOf`) $ lines out
       else
        []

  -- The man page for one version of git rev-parse states that "While
  -- the ref name encoding is unspecified, UTF-8 is preferred as some
  -- output processing may assume ref names in UTF-8".

  -- A completer for tags.
  commitCompleter =
    commandCompleter "git"
      ["for-each-ref", "--format=%(refname:short)", "refs/tags/"]

  -- A completer for branches.
  branchCompleter =
    commandCompleter "git"
      ["for-each-ref", "--format=%(refname:short)", "refs/heads/"]

-- | The top-level program.

main :: IO ()
main = do
  opts <- options
  case dryRun opts of
    Just (Left agda) -> do
      runAgda agda opts
      return ()

    Just (Right commit) -> do
      setupSandbox

      let checkout c = callProcess "git" ["checkout", c]
      bracket currentCommit checkout $ \_ -> do
        checkout commit

        installAndRunAgda opts
        return ()

    Nothing -> do
      setupSandbox

      bisect opts

-- | The current git commit.

currentCommit :: IO String
currentCommit = do
  s <- withEncoding char8 $
         readProcess "git" ["rev-parse", "HEAD"] ""
  return $ dropFinalNewline s
  where
  dropFinalNewline s = case reverse s of
    '\n' : s -> reverse s
    _        -> s

-- | The branches that contain the current git commit.

currentBranches :: IO [String]
currentBranches = do
  s <- withEncoding char8 $
         readProcess "git"
           [ "for-each-ref"
           , "--format=%(refname:short)"
           , "refs/heads/"
           , "--contains=HEAD"
           ]
           ""
  return $ lines s

-- | Raises an error if the given string does not refer to a unique
-- git revision.

validRevision :: String -> IO ()
validRevision rev = do
  ok <- callProcessWithResultSilently "git" ["show", rev]
  unless ok $ do
    putStrLn $ "Invalid revision: " ++ rev ++ "."
    exitFailure

-- | Tries to make sure that a Cabal sandbox will be used.

setupSandbox :: IO ()
setupSandbox = do
  sandboxExists <- callProcessWithResultSilently
                     "cabal" ["v1-sandbox", "list-sources"]
  unless sandboxExists $
    callProcess "cabal" ["v1-sandbox", "init"]

-- | Performs the bisection process.

bisect :: Options -> IO ()
bisect opts =
  initialise
    `finally`
  callProcess "git" ["bisect", "reset"]
  where
  initialise :: IO ()
  initialise = do
    case start opts of
      Left log          -> callProcess "git" ["bisect", "replay", log]
      Right (bad, good) -> do
        validRevision bad
        validRevision good
        callProcess "git" ["bisect", "start", bad, good]

    -- It seems as if git bisect log returns successfully iff
    -- bisection is in progress. Note, however, that git bisect start
    -- accepts invalid revisions. One can currently use a malformed
    -- replay log to fool this script into compiling the currently
    -- checked out revision.
    inProgress <- callProcessWithResultSilently "git" ["bisect", "log"]
    when inProgress run

  run :: IO ()
  run = do
    before   <- currentCommit
    branches <- currentBranches

    msg <- withUTF8Ignore $
             readProcess "git" [ "show"
                               , "--no-patch"
                               , "--pretty=format:%B"
                               , "--encoding=UTF-8"
                               , "HEAD"
                               ] ""

    r <- if any (`isInfixOf` msg) (skipStrings opts)
              ||
            any (`elem` branches) (skipBranches opts)
              ||
            (not (null $ onlyOnBranches opts)
               &&
             not (any (`elem` branches) (onlyOnBranches opts)))
         then return Skip
         else installAndRunAgda opts

    ok <- callProcessWithResult "git" ["bisect", map toLower (show r)]

    case logFile opts of
      Nothing -> return ()
      Just f  -> do
        s <- withEncoding char8 $
               readProcess "git" ["bisect", "log"] ""
        withBinaryFile f WriteMode $ \h -> hPutStr h s

    when ok $ do
      after <- currentCommit
      when (before /= after) run

-- | The result of a single test.

data Result = Good | Bad | Skip
  deriving Show

-- | Tries to first install Agda, and then run the test.

installAndRunAgda :: Options -> IO Result
installAndRunAgda opts = do
  ok <- installAgda opts
  case ok of
    Nothing   -> return Skip
    Just agda -> runAgda agda opts

-- | Runs Agda. Returns 'True' iff the result is satisfactory.

runAgda :: FilePath  -- ^ Agda.
        -> Options
        -> IO Result
runAgda agda opts = do
  (prog, args) <-
    case scriptOrArguments opts of
      Left (prog, args) -> return (prog, agda : args)
      Right args        -> do
        flags <- if extraArguments opts then do
                   help <- readProcess agda ["--help"] ""
                   return $ filter (`isInfixOf` help) defaultFlags
                  else
                   return []
        return (agda, flags ++ args)

  putStrLn $ "Command: " ++ showCommandForUser prog args

  let -- The timeout functionality is implemented using the GNU
      -- timeout command.
      runMaybeTimeout prog args = case mustFinishWithin opts of
        Nothing -> (\r -> Just (r, Nothing)) <$>
                     readProcessWithExitCode prog args ""
        Just n  -> do
          before      <- getCurrentTime
          r@(c, _, _) <- readProcessWithExitCode
                           "timeout"
                           ("--kill-after=3" : show n : prog : args)
                           ""
          after       <- getCurrentTime
          return $ case c of
            -- The documentation of the GNU timeout command states
            -- that if the program is timed out, then the exit code is
            -- 124, and if the command is killed using the KILL
            -- signal, then the exit code is 128+9.
            ExitFailure c
              | c `elem` [124, fromEnum (-sigKILL)] -> Nothing
            _                                       ->
              Just (r, Just (diffUTCTime after before))
              -- The documentation of Data.Time.Clock suggests that
              -- the time difference computed here may be off due to
              -- the presence of a leap second.

  result <- runMaybeTimeout prog args
  case result of
    Nothing -> do
      putStrLn "Timeout"
      return Bad

    Just ((code, out, err), time) -> do
      case time of
        Nothing   -> return ()
        Just time -> putStrLn $
          printf "Elapsed time (roughly): %d min %.2f s" m (s :: Double)
          where
          (ti, tf) = properFraction time
          m        = ti `div` 60
          s        = fromRational
                       (fromInteger (ti `mod` 60) + toRational tf)

      let occurs s       = s `isInfixOf` out || s `isInfixOf` err
          success        = code == ExitSuccess
          expectedResult = mustSucceed opts == success
          testsOK        = expectedResult
                              &&
                           all occurs (mustOutput opts)
                              &&
                           not (any occurs (mustNotOutput opts))
          result         = case (scriptOrArguments opts, code) of
                             (Left _, ExitFailure 127) -> Skip
                             _                         ->
                               case (mustFinishWithin opts, testsOK) of
                                 (Just _,  False) -> Skip
                                 (Nothing, False) -> Bad
                                 (_,       True)  -> Good

      putStrLn $
        "Result: " ++
        (if success then "Success" else "Failure") ++
        " (" ++ (if expectedResult then "good" else "bad") ++ ")"
      unless (null out) $ putStr $ "Stdout:\n" ++ indent out
      unless (null err) $ putStr $ "Stderr:\n" ++ indent err
      putStrLn $ "Verdict: " ++ show result

      return result
  where
  indent = unlines . map ("  " ++) . lines

-- | Tries to install Agda.
--
-- If the installation is successful, then the path to the Agda binary
-- is returned.

installAgda :: Options -> IO (Maybe FilePath)
installAgda opts
  | cacheBuilds opts = do
      commit <- currentCommit
      agdas  <- forM (True : if timeout opts then [] else [False])
                     (\timeout -> do
                       agda <- cachedAgda commit timeout
                       b    <- doesFileExist agda
                       return $ if b then Just agda else Nothing)
      case catMaybes agdas of
        []       -> install
        agda : _ -> do
          copyDataFiles opts
          return (Just agda)
  | otherwise = install
  where
  install =
    uncurry bracket_ makeBuildEasier $ do
      ok <- cabalInstall opts "Agda.cabal"
      case ok of
        Nothing -> return ok
        Just _  -> do
          let executable = "src/main/Agda-executable.cabal"
          exists <- doesFileExist executable
          if exists then
            cabalInstall opts executable
           else
            return ok

-- | Tries to install the package in the given cabal file.
--
-- If the installation is successful, then the path to the Agda binary
-- is returned (on the assumption that the built package includes a
-- binary called @agda@).

cabalInstall :: Options -> FilePath -> IO (Maybe FilePath)
cabalInstall opts file = do
  commit <- currentCommit
  ok <- callProcessWithResult "cabal" $
    [ "v1-install"
    , "--force-reinstalls"
    , "--disable-library-profiling"
    , "--disable-documentation"
    ] ++ (if cacheBuilds opts then ["--program-suffix=" ++
                                    programSuffix commit (timeout opts)]
                              else [])
      ++ compilerFlag opts
      ++ cabalOptions opts ++
    [ file
    ]
  case (ok, cacheBuilds opts) of
    (True, False) -> Just <$> compiledAgda
    (True, True)  -> Just <$> cachedAgda commit (timeout opts)
    (False, _)    -> return Nothing

-- | Tries to copy data files to the correct location.
--
-- This command is somewhat brittle. It relies on @cabal copy@ copying
-- data files before possibly failing to copy other files, and it
-- ignores the exit codes of the programs it calls.

copyDataFiles :: Options -> IO ()
copyDataFiles opts = do
  callProcessWithResult "cabal" (["v1-configure"] ++ compilerFlag opts)
  callProcessWithResult "cabal" ["v1-copy", "-v"]
  return ()

-- | The suffix of the Agda binary.

programSuffix
  :: String  -- ^ The commit hash.
  -> Bool    -- ^ Is the @--timeout@ option active?
  -> String
programSuffix commit timeout =
  (if timeout then "-timeout" else "") ++
  "-" ++ commit

-- | Is the @--timeout@ option active?

timeout :: Options -> Bool
timeout opts = isJust (mustFinishWithin opts)

-- | An absolute path to the cached Agda binary (if any).

cachedAgda
  :: String
  -> Bool
  -> IO FilePath
cachedAgda commit timeout =
   (\agda -> agda ++ programSuffix commit timeout) <$> compiledAgda

-- | Generates a @--with-compiler=…@ flag if the user has specified
-- that a specific compiler should be used.

compilerFlag :: Options -> [String]
compilerFlag opts = case compiler opts of
  Nothing -> []
  Just c  -> ["--with-compiler=" ++ c]

-- | The first command tries to increase the chances that Agda will
-- build. The second command undoes any changes performed to the
-- repository.

makeBuildEasier :: (IO (), IO ())
makeBuildEasier =
  (do callProcessWithResult "sed"
        [ "-ri"
        , "-e", "s/cpphs >=[^,]*/cpphs/"
        , "-e", "s/alex >=[^,]*/alex/"
        , "-e", "s/geniplate[^,]*/geniplate-mirror/"
        , "-e", "s/-Werror(=.*)?//g"
        , cabalFile
        ]
      writeFile "Setup.hs" $ unlines
        [ "import Distribution.Simple"
        , "main = defaultMain"
        ]
      return ()
  , callProcess "git" ["reset", "--hard"]
  )
  where
  cabalFile = "Agda.cabal"

-- | Runs the given program with the given arguments. Returns 'True'
-- iff the command exits successfully.

callProcessWithResult :: FilePath -> [String] -> IO Bool
callProcessWithResult prog args = do
  code <- waitForProcess =<< spawnProcess prog args
  return (code == ExitSuccess)

-- | Like 'callProcessWithResult', but the process does not inherit
-- stdin/stdout/stderr (and @"UTF-8//IGNORE"@ is used as the locale
-- encoding).

callProcessWithResultSilently :: FilePath -> [String] -> IO Bool
callProcessWithResultSilently prog args = do
  (code, _, _) <-
    withUTF8Ignore $
      readProcessWithExitCode prog args ""
  return (code == ExitSuccess)

-- | Runs the given action using the given 'TextEncoding' as the
-- locale encoding.

withEncoding :: TextEncoding -> IO a -> IO a
withEncoding enc action = do
  locale <- getLocaleEncoding
  bracket_ (setLocaleEncoding enc)
           (setLocaleEncoding locale)
           action

-- | Runs the given action using @"UTF-8//IGNORE"@ as the locale
-- encoding.

withUTF8Ignore :: IO a -> IO a
withUTF8Ignore action = do
  utf8Ignore <- mkTextEncoding "UTF-8//IGNORE"
  withEncoding utf8Ignore action
