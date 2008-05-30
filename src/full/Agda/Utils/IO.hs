{-# OPTIONS -cpp #-}

module Agda.Utils.IO where

import qualified Prelude (print, putStr, putStrLn, writeFile, readFile, appendFile)
import Prelude hiding (print, putStr, putStrLn, writeFile, readFile, appendFile)
import Control.Monad
import qualified System.IO as IO (hPutStr)
import System.IO hiding (print, putStr, putStrLn, writeFile, readFile, appendFile, hPutStr)
import Agda.Utils.Unicode
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Lazy.Char8 as BS8

print :: Show a => a -> IO ()
print x = putStrLn (show x)

putStr :: String -> IO ()
putStr s = Prelude.putStr (toUTF8 s)

hPutStr :: Handle -> String -> IO ()
hPutStr h s = IO.hPutStr h (toUTF8 s)

putStrLn :: String -> IO ()
putStrLn s = Prelude.putStrLn (toUTF8 s)

putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr . toUTF8

putErr :: String -> IO ()
putErr = hPutStr stderr . toUTF8

writeFile :: FilePath -> String -> IO ()
writeFile file = Prelude.writeFile file . toUTF8

appendFile :: FilePath -> String -> IO ()
appendFile file = Prelude.appendFile file . toUTF8

readFile :: FilePath -> IO String
readFile file = fmap fromUTF8 $ Prelude.readFile file

readBinaryFile :: FilePath -> IO ByteString
readBinaryFile file = liftM fst $ readBinaryFile' file

-- | Returns a close function for the file together with the contents.
readBinaryFile' :: FilePath -> IO (ByteString, IO ())
readBinaryFile' file = do
#ifdef mingw32_HOST_OS
    h <- System.IO.openBinaryFile file ReadMode
    s <- BS8.pack `fmap` hGetContents h
#else
    h <- openBinaryFile file ReadMode
    s <- BS.hGetContents h
#endif
    return (s, hClose h)

writeBinaryFile :: FilePath -> String -> IO ()
writeBinaryFile file s = do
#ifdef mingw32_HOST_OS
    h <- System.IO.openBinaryFile file WriteMode
#else
    h <- openBinaryFile file WriteMode
#endif
    hPutStr h s
    hClose h

