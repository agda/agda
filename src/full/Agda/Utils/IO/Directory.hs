{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Utils.IO.Directory
  ( copyDirContent
  , copyIfChanged
  , findWithInfo
  )
where

import Control.Monad
import Control.Monad.Writer ( WriterT, execWriterT, tell )
import Control.Monad.Trans  ( lift )

import Data.ByteString      as BS
import Data.Monoid          ( Endo(Endo, appEndo) )

import System.Directory
import System.FilePath
import qualified System.FilePath.Find as Find


-- | Search a directory recursively, with recursion controlled by a
--   'RecursionPredicate'.  Lazily return a unsorted list of all files
--   matching the given 'FilterPredicate'.  Any errors that occur are
--   ignored, with warnings printed to 'stderr'.
findWithInfo
  :: Find.RecursionPredicate  -- ^ Control recursion into subdirectories.
  -> Find.FilterPredicate     -- ^ Decide whether a file appears in the result.
  -> FilePath                 -- ^ Directory to start searching.
  -> IO [Find.FileInfo]       -- ^ Files that matched the 'FilterPredicate'.
findWithInfo recurse filt dir = Find.fold recurse act [] dir
  where
  -- Add file to list front when it matches the filter
  act :: [Find.FileInfo] -> Find.FileInfo -> [Find.FileInfo]
  act fs f = if Find.evalClause filt f then f : fs else fs


-- | @copyDirContent src dest@ recursively copies directory @src@ onto @dest@.
--
--   First, a to-do list of copy actions is created.
--   Then, the to-do list is carried out.
--
--   This avoids copying files we have just created again, which can happen
--   if @src@ and @dest@ are not disjoint.
--   (See issue #2705.)
--
copyDirContent :: FilePath -> FilePath -> IO ()
copyDirContent src dest = mapM_ performAction =<< do
  (`appEndo` []) <$> execWriterT (copyDirContentDryRun src dest)

-- | Action to be carried out for copying a directory recursively.
--
data CopyDirAction
  = MkDir    FilePath
      -- ^ Create directory if missing.
  | CopyFile FilePath FilePath
      -- ^ Copy file if changed.

-- | Perform scheduled 'CopyDirAction'.
--
performAction :: CopyDirAction -> IO ()
performAction = \case
  MkDir d           -> createDirectoryIfMissing True d
  CopyFile src dest -> copyIfChanged src dest

-- | @copyDirContentDryRun src dest@ creates a to-do list
--   for recursively copying directory @src@ onto @dest@.
--
copyDirContentDryRun :: FilePath -> FilePath -> WriterT (Endo [CopyDirAction]) IO ()
copyDirContentDryRun src dest = do
  tell $ Endo (MkDir dest :)
  chlds <- lift $ getDirectoryContents src
  forM_ chlds $ \ x -> do
    isDir <- lift $ doesDirectoryExist (src </> x)
    case isDir of
      _ | x == "." || x == ".." -> return ()
      True  -> copyDirContentDryRun (src </> x) (dest </> x)
      False -> tell $ Endo (CopyFile (src </> x) (dest </> x) :)

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
