
module Utils.IO where

import qualified Prelude (print, putStr, putStrLn, writeFile, readFile)
import Prelude hiding (print, putStr, putStrLn, writeFile, readFile)
import Control.Monad
import System.IO hiding (print, putStr, putStrLn, writeFile, readFile)
import Utils.Unicode

print :: Show a => a -> IO ()
print x = putStrLn (show x)

putStr :: String -> IO ()
putStr s = Prelude.putStr (toUTF8 s)

putStrLn :: String -> IO ()
putStrLn s = Prelude.putStrLn (toUTF8 s)

putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr . toUTF8

putErr :: String -> IO ()
putErr = hPutStr stderr . toUTF8

writeFile :: FilePath -> String -> IO ()
writeFile file = Prelude.writeFile file . toUTF8

readFile :: FilePath -> IO String
readFile file = fmap fromUTF8 $ Prelude.readFile file

readBinaryFile :: FilePath -> IO String
readBinaryFile file = liftM fst $ readBinaryFile' file

-- | Returns a close function for the file together with the contents.
readBinaryFile' :: FilePath -> IO (String, IO ())
readBinaryFile' file = do
    h <- openBinaryFile file ReadMode
    s <- hGetContents h
    return (s, hClose h)

writeBinaryFile :: FilePath -> String -> IO ()
writeBinaryFile file s = do
    h <- openBinaryFile file WriteMode
    hPutStr h s
    hClose h

