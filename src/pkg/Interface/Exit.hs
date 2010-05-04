module Interface.Exit where
-- FIXME: Proper exports

import qualified Data.ByteString.Char8
  as BS

-- Standard Library Imports
import System.Environment
import System.Exit
import System.IO

--------------------------------------------------------------------------------

-- FIXME: ditch these functions in favor of utils in Cabal?
bye :: String -> IO a
bye msg = do
  hPutStrLn stdout msg
  exitWith ExitSuccess

die :: String -> IO a
die = dieWith 1

dieWith :: Int -> String -> IO a
dieWith exitCode msg = do
  hFlush stdout
  progName <- getProgName
  hPutStrLn stderr $ progName ++ ": " ++ msg
  exitWith $ ExitFailure exitCode

byeBS :: BS.ByteString -> IO a
byeBS msg = do
  hPutStrLn stdout (BS.unpack msg)
  exitWith ExitSuccess

dieBS :: BS.ByteString -> IO a
dieBS = dieWithBS 1

dieWithBS :: Int -> BS.ByteString -> IO a
dieWithBS exitCode msg = do
  hFlush stdout
  progName <- getProgName
  hPutStrLn stderr $ progName ++ ": " ++ BS.unpack msg
  exitWith $ ExitFailure exitCode
