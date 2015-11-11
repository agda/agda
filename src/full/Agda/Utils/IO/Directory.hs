module Agda.Utils.IO.Directory
  ( copyDirContent
  )
where

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
      False -> copyFile (src </> x) (dest </> x)
    ) chlds

