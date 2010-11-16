------------------------------------------------------------------------
-- Module name encoding
------------------------------------------------------------------------

module Agda.Compiler.MAlonzo.Encode
  ( encodeModuleName
  , tests
  ) where

import Data.Char
import Data.Function
import Data.List
import qualified Language.Haskell.Exts.Syntax as HS
import Test.QuickCheck

import Agda.Compiler.MAlonzo.Misc

import Agda.Utils.QuickCheck
import Agda.Utils.TestHelpers

-- | Can the character be used in a Haskell module name part
-- (@conid@)? This function is more restrictive than what the Haskell
-- report allows.

isModChar :: Char -> Bool
isModChar c =
  isLower c || c == '_' || isUpper c || isDigit c || c == '\''

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
encodeModuleName (HS.ModuleName s) = HS.ModuleName $ case splitUp s of
  ps | mazstr' `isPrefixOf` ps ->
       concat (mazstr' ++ map encNamePart (drop (length mazstr') ps))
  _                            -> s
  where
  -- splitUp ".apa.bepa." == [".","apa",".","bepa","."]
  splitUp = groupBy ((&&) `on` (/= '.'))

  mazstr' = splitUp mazstr

  encNamePart "." = "."
  encNamePart s   = ensureFirstCharLarge s ++ concatMap enc s

  ensureFirstCharLarge s = case s of
    c : cs | isUpper c && c /= largeChar -> ""
    _                                    -> [largeChar]

  largeChar  = 'Q'
  escapeChar = 'Z'

  isOK c = c /= escapeChar && isModChar c

  enc c | isOK c    = [c]
        | otherwise = [escapeChar] ++ show (fromEnum c) ++ [escapeChar]

-- Note: This injectivity test is quite weak. A better, dedicated
-- generator could strengthen it.

prop_encodeModuleName_injective (M s1) (M s2) =
  if encodeModuleName (HS.ModuleName s1) ==
     encodeModuleName (HS.ModuleName s2) then
    s1 == s2
   else
    True

prop_encodeModuleName_OK (M s') =
  s ~= unM (encodeModuleName (HS.ModuleName s))
  where
  s = mazstr ++ "." ++ s'

  ""        ~= ""         = True
  ('.' : s) ~= ('.' : s') = s ~= s'
  s         ~= (c : s')   = isUpper c && all isModChar s1' &&
                            dropWhile (/= '.') s ~= s2'
                              where (s1', s2') = span (/= '.') s'
  _         ~= _          = False

  unM (HS.ModuleName s) = s

prop_encodeModuleName_preserved (M m) =
  shouldBePreserved m ==>
    encodeModuleName (HS.ModuleName m) == HS.ModuleName m
  where
  shouldBePreserved m =
    not (m == mazstr || (mazstr ++ ".") `isPrefixOf` m)

-- | Agda module names. Used to test 'encodeModuleName'.

newtype M = M String deriving (Show)

instance Arbitrary M where
  arbitrary = do
    ms <- choose (0, 2)
    m <- vectorOf ms namePart
    return $ M (intercalate "." m)
    where
    namePart =
      oneof [ return mazstr
            , do cs <- choose (1, 2)
                 vectorOf cs (elements "a_AQZ0'-∀")
            ]

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Compiler.MAlonzo.Encode"
  [ quickCheck' prop_encodeModuleName_injective
  , quickCheck' prop_encodeModuleName_OK
  , quickCheck' prop_encodeModuleName_preserved
  ]
