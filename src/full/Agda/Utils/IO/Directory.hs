module Agda.Utils.IO.Directory
  ( copyDirContent
  )
where

import Control.Monad
import System.Directory
import System.FilePath

import Paths_Agda

copyDirContent :: FilePath -> FilePath -> IO ()
copyDirContent src dest = do
  createDirectoryIfMissing True dest
  chlds <- getDirectoryContents src
  mapM_ (\x -> do
    isDir <- doesDirectoryExist (src </> x)
    case isDir of
      _ | x == "." || x == ".." -> return ()
      True  -> copyDirContent (src </> x) (dest </> x)
      False -> copyIfChanged (src </> x) (dest </> x)
    ) chlds

copyIfChanged :: FilePath -> FilePath -> IO ()
copyIfChanged src dst = do
  exist <- doesFileExist dst
  if not exist then copyFile src dst else do
    new <- readFile src
    old <- readFile dst
    unless (old == new) $ copyFile src dst

