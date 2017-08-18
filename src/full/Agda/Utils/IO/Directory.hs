module Agda.Utils.IO.Directory
  ( copyDirContent
  )
where

import Control.Monad
import System.Directory
import System.FilePath
import Data.ByteString as BS

import Paths_Agda

-- | @copyDirContent src dest@ recursively copies directory @src@ onto @dest@.
--
--   Precondition: @src@ and @dest@ are disjoint.
--   E.g. @copyDirContent "A/" "A/B/"@ would loop producing @A/B/B/B/...@.
--
copyDirContent :: FilePath -> FilePath -> IO ()
copyDirContent src dest = do
  createDirectoryIfMissing True dest
  chlds <- getDirectoryContents src
  forM_ chlds $ \ x -> do
    isDir <- doesDirectoryExist (src </> x)
    case isDir of
      _ | x == "." || x == ".." -> return ()
      True  -> copyDirContent (src </> x) (dest </> x)
      False -> copyIfChanged (src </> x) (dest </> x)

-- | @copyIfChanged src dst@ makes sure that @dst@ exists
--   and has the same content as @dst@.
--
copyIfChanged :: FilePath -> FilePath -> IO ()
copyIfChanged src dst = do
  exist <- doesFileExist dst
  if not exist then copyFile src dst else do
    new <- BS.readFile src
    old <- BS.readFile dst
    unless (old == new) $ copyFile src dst
