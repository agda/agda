module ImportWarningsB where

-- all of the following files have warnings, which should be displayed
-- when loading this file

import Issue2243
import Issue708quote
import RewritingEmptyPragma
import Unreachable

-- also this warning should be displayed
{-# REWRITE #-}
