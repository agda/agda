{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module Agda.VersionCommit where

import Data.Maybe         ( fromMaybe )
import Data.List          ( find )
import Development.GitRev ( gitHash, gitDirtyTracked )
import Text.Regex.TDFA    ( (=~) )

import Agda.Version       ( version )
import Agda.Utils.Git     ( gitTags )

-- | Agda's version suffixed with the git commit hash.
versionWithCommitInfo :: String
versionWithCommitInfo = version ++ maybe "" ("-" ++) commitInfo

-- | Information about current git commit, generated at compile time.
commitInfo :: Maybe String
commitInfo
  | hash == "UNKNOWN" = Nothing
  | otherwise         = Just $ abbrev hash ++ dirty
  where
    hash = $(gitHash)

    -- Check if any tracked files have uncommitted changes
    dirty | $(gitDirtyTracked) = "-dirty"
          | otherwise          = ""

    -- Abbreviate a commit hash while keeping it unambiguous
    abbrev = take 7

-- | Returns a URL corresponding to the given section in the documentation for
-- the current version.
-- The current version is @latest@ unless the current commit has a release tag.
docsUrl :: String -> String
docsUrl = (prefix ++)
  where
    prefix = "https://agda.readthedocs.io/en/" ++ v ++ "/"
    v      = fromMaybe "latest" $ find isReleaseTag tags
    tags   = $(gitTags)

-- | Release tags are @nightly@ or @vNNN.NNN.NNN...@.
isReleaseTag :: String -> Bool
isReleaseTag tag = tag == "nightly" || tag =~ versionPattern

-- | Recognize a release tag.
versionPattern :: String
versionPattern = "v[0-9]+\\.[0-9]+\\.[0-9]+.*"
