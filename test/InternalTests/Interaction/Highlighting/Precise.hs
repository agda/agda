{-# LANGUAGE CPP #-}

module InternalTests.Interaction.Highlighting.Precise ( tests ) where

import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>), (<*>) )
#endif
import Control.Monad

import qualified Data.IntMap as IntMap
import Data.List

import InternalTests.Helpers
import InternalTests.Interaction.Highlighting.Range ()
import InternalTests.Syntax.Common ()
import InternalTests.Syntax.Concrete.Name ()

------------------------------------------------------------------------
-- Compressed files

prop_compress :: File -> Bool
prop_compress f =
  compressedFileInvariant c
  &&
  decompress c == f
  where c = compress f

------------------------------------------------------------------------
-- Operations that work directly with compressed files

prop_singleton :: Ranges -> Aspects -> Bool
prop_singleton rs m = singleton rs m == decompress (singletonC rs m)

prop_several :: [Ranges] -> Aspects -> Bool
prop_several rss m = several rss m == decompress (severalC rss m)

prop_merge :: File -> File -> Bool
prop_merge f1 f2 =
  merge f1 f2 == decompress (mergeC (compress f1) (compress f2))

prop_splitAtC :: Int -> CompressedFile -> Bool
prop_splitAtC p f =
  all (<  p) (positions f1) &&
  all (>= p) (positions f2) &&
  decompress (mergeC f1 f2) == decompress f
  where
  (f1, f2) = splitAtC p f

  positions = IntMap.keys . toMap . decompress

prop_smallestPos :: CompressedFile -> Bool
prop_smallestPos f = smallestPos (decompress f) == smallestPosC f

------------------------------------------------------------------------
-- Algebraic properties

-- | 'Aspects' is a monoid.
prop_monoid_Aspects :: Aspects -> Aspects -> Aspects -> Bool
prop_monoid_Aspects = isMonoid

-- | 'File' is a monoid.
prop_monoid_File :: File -> File -> File -> Bool
prop_monoid_File = isMonoid

-- | 'CompressedFile' is a monoid.
prop_monoid_CompressedFile :: CompressedFile -> CompressedFile -> CompressedFile -> Bool
prop_monoid_CompressedFile = isMonoid

------------------------------------------------------------------------
-- Generators

instance Arbitrary Aspect where
  arbitrary =
    frequency [ (3, elements [ Comment, Option, Keyword, String, Number
                             , Symbol, PrimitiveType ])
              , (1, liftM2 Name (maybeGen arbitrary) arbitrary)
              ]

  shrink Name{} = [Comment]
  shrink _      = []

instance CoArbitrary Aspect where
  coarbitrary Comment       = variant 0
  coarbitrary Option        = variant 1
  coarbitrary Keyword       = variant 2
  coarbitrary String        = variant 3
  coarbitrary Number        = variant 4
  coarbitrary Symbol        = variant 5
  coarbitrary PrimitiveType = variant 6
  coarbitrary (Name nk b)   =
    variant 7 . maybeCoGen coarbitrary nk . coarbitrary b

instance Arbitrary NameKind where
  arbitrary = oneof $ [liftM Constructor arbitrary] ++
                      map return [ Bound
                                 , Datatype
                                 , Field
                                 , Function
                                 , Module
                                 , Postulate
                                 , Primitive
                                 , Record
                                 ]

  shrink Constructor{} = [Bound]
  shrink _             = []

instance CoArbitrary NameKind where
  coarbitrary Bound             = variant 0
  coarbitrary (Constructor ind) = variant 1 . coarbitrary ind
  coarbitrary Datatype          = variant 2
  coarbitrary Field             = variant 3
  coarbitrary Function          = variant 4
  coarbitrary Module            = variant 5
  coarbitrary Postulate         = variant 6
  coarbitrary Primitive         = variant 7
  coarbitrary Record            = variant 8
  coarbitrary Argument          = variant 9
  coarbitrary Macro             = variant 10

instance Arbitrary OtherAspect where
  arbitrary = elements [minBound .. maxBound]

instance CoArbitrary OtherAspect where
  coarbitrary = coarbitrary . fromEnum

instance Arbitrary Aspects where
  arbitrary = do
    aspect  <- arbitrary
    other   <- arbitrary
    note    <- maybeGen string
    defSite <- arbitrary
    return (Aspects { aspect = aspect, otherAspects = other
                     , note = note, definitionSite = defSite })
    where string = listOfElements "abcdefABCDEF/\\.\"'@()åäö\n"

  shrink (Aspects a o n d) =
    [ Aspects a o n d | a <- shrink a ] ++
    [ Aspects a o n d | o <- shrink o ] ++
    [ Aspects a o n d | n <- shrink n ] ++
    [ Aspects a o n d | d <- shrink d ]

instance CoArbitrary Aspects where
  coarbitrary (Aspects aspect otherAspects note defSite) =
    coarbitrary aspect .
    coarbitrary otherAspects .
    coarbitrary note .
    coarbitrary defSite

instance Arbitrary DefinitionSite where
  arbitrary = liftM4 DefinitionSite arbitrary arbitrary arbitrary $ maybeGen string
    where string = listOfElements "abcdefABCDEF/\\.'åäö"

  shrink (DefinitionSite a b c d) =
    [ DefinitionSite a b c d | a <- shrink a ] ++
    [ DefinitionSite a b c d | b <- shrink b ] ++
    [ DefinitionSite a b c d | c <- shrink c ] ++
    [ DefinitionSite a b c d | d <- shrink d ]

instance CoArbitrary DefinitionSite where
  coarbitrary (DefinitionSite a b c d) =
    coarbitrary a .
    coarbitrary b .
    coarbitrary c .
    coarbitrary d

instance Arbitrary File where
  arbitrary = fmap (File . IntMap.fromList) $ listOf arbitrary
  shrink    = map (File . IntMap.fromList) . shrink . IntMap.toList . toMap

instance CoArbitrary File where
  coarbitrary (File rs) = coarbitrary (IntMap.toAscList rs)

instance Arbitrary CompressedFile where
  arbitrary = do
    rs <- (\ns1 ns2 -> toRanges $ sort $
                         ns1 ++ concatMap (\n -> [n, succ n]) (ns2 :: [Int])) <$>
            arbitrary <*> arbitrary
    CompressedFile <$> mapM (\r -> (,) r <$> arbitrary) rs
    where
    toRanges (f : t : rs)
      | f == t    = toRanges (t : rs)
      | otherwise = Range { from = f, to = t } :
                    toRanges (case rs of
                                f : rs | t == f -> rs
                                _               -> rs)
    toRanges _ = []

  shrink (CompressedFile f) = CompressedFile <$> shrink f

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "InternalTests.Interaction.Highlighting.Precise"
  [ quickCheck' compressedFileInvariant
  , quickCheck' (all compressedFileInvariant . shrink)
  , quickCheck' (\r m -> compressedFileInvariant $ singletonC r m)
  , quickCheck' (\rs m -> compressedFileInvariant $ severalC rs m)
  , quickCheck' (\f1 f2 -> compressedFileInvariant $ mergeC f1 f2)
  , quickCheck' (\i f -> all compressedFileInvariant $
                         (\(f1, f2) -> [f1, f2]) $
                         splitAtC i f)
  , quickCheck' prop_compress
  , quickCheck' prop_singleton
  , quickCheck' prop_several
  , quickCheck' prop_merge
  , quickCheck' prop_splitAtC
  , quickCheck' prop_smallestPos
  , quickCheck' prop_monoid_Aspects
  , quickCheck' prop_monoid_File
  , quickCheck' prop_monoid_CompressedFile
  ]
