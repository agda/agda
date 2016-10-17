{-# LANGUAGE TemplateHaskell #-}

module Agda.VersionCommit where

import Development.GitRev

import Agda.Version

versionWithCommitInfo :: String
versionWithCommitInfo = version ++ case commitInfo of
                                     Nothing   -> ""
                                     Just info -> "-" ++ info

-- | Information about current git commit, generated at compile time
commitInfo :: Maybe String
commitInfo = case $(gitHash) of
  "UNKNOWN" -> Nothing
  hash      -> Just $ abbrev hash ++ dirty
  where
    -- | Check if there are uncommitted changes
    dirty | $(gitDirty) = "-dirty"
          | otherwise   = ""

    -- | Abbreviate a commit hash while keeping it unambiguous
    abbrev = take 7
