
module InternalTests.Compiler.MAlonzo.Encode ( tests ) where

import Agda.Compiler.MAlonzo.Encode
import Agda.Compiler.MAlonzo.Misc

import Data.Char
import Data.List

import InternalTests.Helpers

import qualified Language.Haskell.Exts.Syntax as HS

-- Note: This injectivity test is quite weak. A better, dedicated
-- generator could strengthen it.

prop_encodeModuleName_injective :: M -> M -> Bool
prop_encodeModuleName_injective (M s1) (M s2) =
  if encodeModuleName (HS.ModuleName s1) ==
     encodeModuleName (HS.ModuleName s2) then
    s1 == s2
   else
    True

prop_encodeModuleName_OK :: M -> Bool
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

prop_encodeModuleName_preserved :: M -> Property
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
tests = runTests "InternalTests.Compiler.MAlonzo.Encode"
  [ quickCheck' prop_encodeModuleName_injective
  , quickCheck' prop_encodeModuleName_OK
  , quickCheck' prop_encodeModuleName_preserved
  ]
