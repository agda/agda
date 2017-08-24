import Control.Monad
import Data.List
import System.Environment
import System.Process
import System.IO

name        = "Issue1829"
args        = [ "--interaction"
              , "--caching"
              , "+RTS"
              , "-M4M"
              , "-RTS"
              ]
command     = "IOTCM \"" ++ name ++ ".agda\" None Indirect " ++
                "(Cmd_load \"" ++ name ++ ".agda\" [])"
repetitions = 1000
prompt      = "Agda2> "

-- Reads at most the given number of characters from the given handle.
-- Stops reading if a newline character is encountered, and in that
-- case the returned boolean is True.
--
-- Precondition: The number must be non-negative.

readAtMost 0 h = return (False, [])
readAtMost n h = do
  c <- hGetChar h
  if c == '\n'
    then return (True, [])
    else fmap (\(b, s) -> (b, c : s)) (readAtMost (n - 1) h)

-- Checks if the string read from the given handle starts with the
-- prompt. If it doesn't, then a complete line is read, and the
-- continuation is applied to the line. Otherwise the prompt is
-- discarded and the continuation is not called.
--
-- Precondition: The prompt must not contain newline characters.

unlessPromptPresent h cont = do
  (nl, s) <- readAtMost (length prompt) h
  unless (s == prompt) $ do
    s <- if nl then return s
               else fmap (s ++) (hGetLine h)
    cont s

-- Echoes lines read from the first handle on the second handle until
-- a prompt is encountered (at the start of a line).

echoUntilPrompt rd wr =
  unlessPromptPresent rd $ \line -> do
    hPutStrLn wr line
    echoUntilPrompt rd wr

-- Precondition: The program must be called with a single argument,
-- the path to Agda.

main = do
  -- Start Agda, allocating handles to write commands and read
  -- results.
  [agda] <- getArgs
  (Just wr, Just rd, Nothing, p) <-
    createProcess ((proc agda args) { std_in  = CreatePipe
                                    , std_out = CreatePipe
                                    })
  mapM_ (\h -> hSetEncoding h utf8) [wr, rd, stdout]
  hSetBuffering wr LineBuffering
  hSetBuffering rd NoBuffering
  let echo = echoUntilPrompt rd stdout

  -- Run the given command repeatedly. Wait until the first
  -- command has completed before initiating the /third/ one. Why
  -- not the second one? Because this made the test case
  -- considerably slower.
  --
  -- Note that a prompt precedes the output from the first
  -- command. After the first command is initiated the initial
  -- prompt is discarded and then a second command is initiated.
  -- Only then is the output from the initial command echoed.
  replicateM_ repetitions $ do
    hPutStrLn wr command
    echo

  -- Echo the final output.
  echo

  -- Let Agda shut down gracefully.
  hClose wr
  waitForProcess p
