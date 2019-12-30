-- | Functions that can be used to communicate with an Agda process.

module RunAgda
  ( getAgda
  , runAgda
  , runAgda'
  , AgdaCommands(..)
  , command
  , writeUTF8File
  ) where

import Control.Exception
import Control.Monad
import System.Environment
import System.IO
import System.Process
import Text.Show

-- | The first arguments given to the Agda process.

firstArguments :: [String]
firstArguments = ["--interaction"]

-- | The prompt used by the Agda process. It is assumed that the
-- process places prompts at the start of a line.
--
-- Invariant: The prompt does not contain newline characters.

prompt :: String
prompt = "Agda2> "

-- | Constructs commands of a certain kind.

-- This code is somewhat hacky. An alternative would be to add a
-- dependency on the Agda library.

command
  :: String       -- ^ The name of the command (minus @Cmd_@).
  -> FilePath     -- ^ The file to operate on.
  -> Maybe String -- ^ Non-default highlighting arguments.
  -> Maybe String -- ^ Optional arguments to the command (including
                  --   the file name, if required).
  -> String
command cmd f mHigh mArgs =
  "IOTCM " ++ show f ++ " " ++ high ++ " " ++
    "(Cmd_" ++ cmd ++ " " ++ args ++ ")"
  where
  high = case mHigh of
    Nothing -> "None Indirect"
    Just h  -> h
  args = case mArgs of
    Nothing   -> ""
    Just args -> " " ++ args

-- | Constructs a (certain kind of) "load" command from a file name.

loadCommand :: FilePath -> String
loadCommand f = command "load" f Nothing (Just $ show f ++ "[]")

-- | Reads at most the given number of characters from the given
-- handle. Stops reading if a newline character is encountered, and in
-- that case the returned boolean is True, and the newline character
-- is discarded.

readAtMost :: Int -> Handle -> IO (Bool, String)
readAtMost n h
  | n <= 0    = return (False, [])
  | otherwise = do
    c <- hGetChar h
    if c == '\n'
      then return (True, [])
      else fmap (\(b, s) -> (b, c : s)) (readAtMost (n - 1) h)

-- Reads lines from the handle until a prompt is encountered. The
-- prompt is not returned.

readUntilPrompt' :: Handle -> IO [String]
readUntilPrompt' h = do
  (nl, s) <- readAtMost (length prompt) h
  if s == prompt then return [] else do
    line <- if nl then return s
                  else fmap (s ++) (hGetLine h)
    liftM (line :) $ readUntilPrompt' h

-- | Echoes lines read from the first handle on the second handle
-- until a prompt is encountered. The prompt is not echoed.

echoUntilPrompt' :: Handle -> Handle -> IO [String]
echoUntilPrompt' rd wr = do
  ss <- readUntilPrompt' rd
  mapM_ (hPutStrLn wr) ss
  return ss

-- | Commands that can be used to communicate with the Agda process.
--
-- The commands that read Agda output do not return (or echo) the
-- prompt.

data AgdaCommands = AgdaCommands
  { readUntilPrompt :: IO [String]
    -- ^ Read lines until a prompt is encountered.
  , echoUntilPrompt :: IO [String]
    -- ^ Echo lines until a prompt is encountered.
  , send :: String -> IO ()
    -- ^ Send the given command to the Agda process.
  , load :: FilePath -> IO ()
    -- ^ Load the given Agda file (in a certain way).
  , loadAndEcho :: FilePath -> IO [String]
    -- ^ Load the given Agda file (in a certain way) and echo lines
    -- until a prompt is encountered.
  , callAgda :: [String] -> IO ()
    -- ^ Run an independent Agda process, synchronously, with the
    -- given arguments.
  }

-- | Takes the name of the Agda executable from the first argument
-- on the command line.
getAgda :: IO FilePath
getAgda = do
  args <- getArgs
  case args of
    agda : _ -> return agda
    []       -> error "getAgda: No command-line arguments."

-- | Starts Agda, invokes the continuation, and finally shuts down Agda.
--
-- The name of the Agda executable is assumed to be the first argument
-- on the command line.

runAgda
  :: [String]                -- ^ Extra arguments given to Agda.
  -> (AgdaCommands -> IO a)  -- ^ Continuation.
  -> IO a
runAgda extraArgs cont = do
  agda <- getAgda
  runAgda' agda extraArgs cont

-- | Starts Agda, invokes the continuation, and finally shuts down Agda.

runAgda'
  :: FilePath                -- ^ Path to Agda.
  -> [String]                -- ^ Extra arguments given to Agda.
  -> (AgdaCommands -> IO a)  -- ^ Continuation.
  -> IO a
runAgda' agda extraArgs cont =
  bracket
    (createProcess ((proc agda (firstArguments ++ extraArgs))
                      { std_in  = CreatePipe
                      , std_out = CreatePipe
                      }))

    (\(Just wr, _, _, p) -> do
       -- Let Agda shut down gracefully.
       hClose wr
       waitForProcess p)

    (\(Just wr, Just rd, Nothing, p) -> do
       mapM_ (\h -> hSetEncoding h utf8) [wr, rd, stdout]
       hSetBuffering wr LineBuffering
       hSetBuffering rd NoBuffering
       let echo = echoUntilPrompt' rd stdout
           send = hPutStrLn wr
           load = send . loadCommand
       cont (AgdaCommands
               { readUntilPrompt = readUntilPrompt' rd
               , echoUntilPrompt = echo
               , send            = send
               , load            = load
               , loadAndEcho     = \f -> load f >> echo
               , callAgda        = callProcess agda
               }))

-- | Writes the given string to the given file, using the UTF-8
-- encoding.

writeUTF8File :: FilePath -> String -> IO ()
writeUTF8File f s = withFile f WriteMode $ \h -> do
  hSetEncoding h utf8
  hPutStr h s
