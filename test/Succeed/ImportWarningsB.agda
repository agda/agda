module ImportWarningsB where

-- all of the following files have warnings, which should be displayed
-- when loading this file

import Issue2243
import Issue708quote
import OldCompilerPragmas
import RewritingEmptyPragma
import Unreachable

-- this warning will be ignored
{-# REWRITE #-}
