{-# LANGUAGE TemplateHaskell #-}

-- | Git utilities.

module Agda.Utils.Git where

import Control.Exception          ( SomeException, try )
import Data.List                  ( lines )
import Language.Haskell.TH        ( Q, Exp )
import Language.Haskell.TH.Syntax ( lift, runIO )
import System.Process             ( readProcess )

-- | Get a Git tags pointing at HEAD, if any, at compile time.
--   Returns an expression that produces the possibly empty string list of tags.
gitTags :: Q Exp
gitTags = do
  let call = readProcess "git" ["tag", "--points-at", "HEAD"] ""
  result <- runIO $ try call :: Q (Either SomeException String)
  lift $ either (const []) lines result
