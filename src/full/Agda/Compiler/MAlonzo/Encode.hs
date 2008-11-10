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
import Language.Haskell.Syntax
import Test.QuickCheck

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
-- names defined by @modid@. The function often preserves names. The
-- function always preserves @.@s.
--
-- Precondition: The input must not start or end with @.@, and no two
-- @.@s may be adjacent.

encodeModuleName :: Module -> Module
encodeModuleName (Module s) = Module (concatMap encNamePart $ splitUp s)
  where
  -- splitUp ".apa.bepa." == [".","apa",".","bepa","."]
  splitUp = groupBy ((&&) `on` (/= '.'))

  encNamePart "." = "."
  encNamePart s   = ensureFirstCharLarge s ++ concatMap enc s

  ensureFirstCharLarge s = case s of
    c : cs | isUpper c -> ""
    _                  -> "M"

  isOK c = c /= 'Z' && isModChar c

  enc c | isOK c    = [c]
        | otherwise = "Z" ++ show (fromEnum c) ++ "Z"

-- Note: This injectivity test is quite weak. A better, dedicated
-- generator could strengthen it.

prop_encodeModuleName_injective (M s1) (M s2) =
  if encodeModuleName (Module s1) == encodeModuleName (Module s2) then
    s1 == s2
   else
    True

prop_encodeModuleName_OK (M s) =
  s ~= unM (encodeModuleName (Module s))
  where
  ""        ~= ""         = True
  ('.' : s) ~= ('.' : s') = s ~= s'
  s         ~= (c : s')   = isUpper c && all isModChar s1' &&
                            dropWhile (/= '.') s ~= s2'
                              where (s1', s2') = span (/= '.') s'
  _         ~= _          = False

  unM (Module s) = s

-- | Agda module names. Used to test 'encodeModuleName'.

newtype M = M String deriving (Show)

instance Arbitrary M where
  arbitrary = do
    ms <- choose (0, 2)
    m <- vectorOf ms namePart
    return $ M (intercalate "." m)
    where
    namePart = do
      cs <- choose (1, 2)
      vectorOf cs (elements "a_AZ0'-∀")

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Compiler.MAlonzo.Encode"
  [ quickCheck' prop_encodeModuleName_injective
  , quickCheck' prop_encodeModuleName_OK
  ]
