module IgnoreWarnings where

-- all of the following files have warnings, which should be ignored
-- because of the command-line flag

import Issue2243
import Issue708quote
import OldCompilerPragmas
import RewritingEmptyPragma
import Unreachable

-- this should also be ignored
{-# REWRITE #-}
