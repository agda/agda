
module Utils.IO where

import qualified Prelude (print, putStr, putStrLn)
import Prelude hiding (print, putStr, putStrLn)
import Utils.Unicode
import System.IO hiding (print, putStr, putStrLn)

print :: Show a => a -> IO ()
print x = putStrLn (show x)

putStr :: String -> IO ()
putStr s = Prelude.putStr (toUTF8 s)

putStrLn :: String -> IO ()
putStrLn s = Prelude.putStrLn (toUTF8 s)

readBinaryFile :: FilePath -> IO String
readBinaryFile file = do
    h <- openBinaryFile file ReadMode
    hGetContents h

writeBinaryFile :: FilePath -> String -> IO ()
writeBinaryFile file s = do
    h <- openBinaryFile file WriteMode
    hPutStr h s
    hClose h

