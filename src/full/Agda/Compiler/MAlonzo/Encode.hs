------------------------------------------------------------------------
-- Module name encoding
------------------------------------------------------------------------

module Agda.Compiler.MAlonzo.Encode
  ( encodeModuleName
  ) where

import Data.Char
import Data.Function
import qualified Data.List as List
import qualified Agda.Utils.Haskell.Syntax as HS

import Agda.Compiler.MAlonzo.Misc

-- | Haskell module names have to satisfy the Haskell (including the
-- hierarchical module namespace extension) lexical syntax:
--
--   @modid -> [modid.] large {small | large | digit | ' }@
--
-- 'encodeModuleName' is an injective function into the set of module
-- names defined by @modid@. The function preserves @.@s, and it also
-- preserves module names whose first name part is not 'mazstr'.
--
-- Precondition: The input must not start or end with @.@, and no two
-- @.@s may be adjacent.

encodeModuleName :: HS.ModuleName -> HS.ModuleName
encodeModuleName (HS.ModuleName s) = HS.ModuleName $ case List.stripPrefix mazstr s of
  Just s' -> mazstr ++ foldr encNamePart "" (splitUp' s')
  Nothing -> s
  where
  -- splitUp ".apa.bepa." == [".","apa",".","bepa","."]
  -- splitUp = groupBy ((&&) `on` (/= '.'))

  -- Since comparison against "." is wasteful, and modules name components are nonempty,
  -- we can use "" as the separator.
  -- Since modules name components are nonempty,
  -- this is more efficient than adding a Maybe wrapper:
  -- We are effectively using ``String = Maybe NEString''.
  --
  -- splitUp' ".apa.bepa." == ["","apa","","bepa",""]
  splitUp' :: String -> [String]
  splitUp' = h
    where
      h [] = []
      h (c : cs) = case c of
        '.' -> "" : h cs
        _ -> g (c :) cs
      g acc [] = [acc []]
      g acc (c : cs) = case c of
        '.' -> acc [] : "" : h cs
        _ -> g (acc . (c :)) cs

  encNamePart "" r = '.' : r
  encNamePart s  r = ensureFirstCharLarge s $ foldr enc r s

  ensureFirstCharLarge s r = case s of
    c : cs | isUpper c && c /= largeChar -> r
    _                                    -> largeChar : r

  largeChar  = 'Q'
  escapeChar = 'Z'

  isOK c = c /= escapeChar && isModChar c

  enc c r | isOK c    = c : r
          | otherwise = escapeChar : shows (fromEnum c) (escapeChar : r)
