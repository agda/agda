{-# LANGUAGE TemplateHaskell #-}

module Internal.Interaction.Highlighting.Precise ( tests ) where

import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Highlighting.Range

import Control.Monad

import qualified Data.IntMap as IntMap
import Data.List

import Internal.Helpers
import Internal.Interaction.Highlighting.Range ()
import Internal.Syntax.Common ()
import Internal.Syntax.Concrete.Name ()

------------------------------------------------------------------------
-- 'compressedFileInvariant'

prop_compressedFileInvariant1 :: CompressedFile -> Bool
prop_compressedFileInvariant1 = compressedFileInvariant

prop_compressedFileInvariant2 :: CompressedFile -> Bool
prop_compressedFileInvariant2 = all compressedFileInvariant . shrink

prop_compressedFileInvariant3 :: Ranges -> Aspects -> Bool
prop_compressedFileInvariant3 r m = compressedFileInvariant $ singletonC r m

prop_compressedFileInvariant4 :: [Ranges] -> Aspects -> Bool
prop_compressedFileInvariant4 rs m = compressedFileInvariant $ severalC rs m

prop_compressedFileInvariant5 :: CompressedFile -> CompressedFile -> Bool
prop_compressedFileInvariant5 f1 f2 = compressedFileInvariant $ mergeC f1 f2

prop_compressedFileInvariant6 :: Int -> CompressedFile -> Bool
prop_compressedFileInvariant6 i f =
  all compressedFileInvariant $ (\(f1, f2) -> [f1, f2]) $ splitAtC i f

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
prop_monoid_Aspects :: Property3 Aspects
prop_monoid_Aspects = isMonoid

-- | 'File' is a monoid.
prop_monoid_File :: Property3 File
prop_monoid_File = isMonoid

-- | 'CompressedFile' is a monoid.
prop_monoid_CompressedFile :: Property3 CompressedFile
prop_monoid_CompressedFile = isMonoid

------------------------------------------------------------------------
-- Generators

instance Arbitrary Aspect where
  arbitrary =
    frequency [ (3, elements [ Comment, Keyword, String, Number
                             , Symbol, PrimitiveType, Pragma ])
              , (1, liftM2 Name (maybeGen arbitrary) arbitrary)
              ]

  shrink Name{} = [Comment]
  shrink _      = []

instance CoArbitrary Aspect where
  coarbitrary Comment       = variant 0
  coarbitrary Keyword       = variant 1
  coarbitrary String        = variant 2
  coarbitrary Number        = variant 3
  coarbitrary Symbol        = variant 4
  coarbitrary PrimitiveType = variant 5
  coarbitrary (Name nk b)   =
    variant 6 . maybeCoGen coarbitrary nk . coarbitrary b
  coarbitrary Pragma        = variant 7
  coarbitrary Background    = variant 8
  coarbitrary Markup        = variant 9

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
  coarbitrary Generalizable     = variant 11

instance Arbitrary OtherAspect where
  arbitrary = elements [minBound .. maxBound]

instance CoArbitrary OtherAspect where
  coarbitrary = coarbitrary . fromEnum

instance Arbitrary Aspects where
  arbitrary = do
    aspect     <- arbitrary
    other      <- arbitrary
    note       <- maybeGen string
    defSite    <- arbitrary
    tokenBased <- arbitrary
    return (Aspects { aspect         = aspect
                    , otherAspects   = other
                    , note           = note
                    , definitionSite = defSite
                    , tokenBased     = tokenBased
                    })
    where string = listOfElements "abcdefABCDEF/\\.\"'@()åäö\n"

  shrink (Aspects a o n d t) =
    [ Aspects a o n d t | a <- shrink a ] ++
    [ Aspects a o n d t | o <- shrink o ] ++
    [ Aspects a o n d t | n <- shrink n ] ++
    [ Aspects a o n d t | d <- shrink d ] ++
    [ Aspects a o n d t | t <- shrink t ]

instance CoArbitrary Aspects where
  coarbitrary (Aspects aspect otherAspects note defSite tokenBased) =
    coarbitrary aspect .
    coarbitrary otherAspects .
    coarbitrary note .
    coarbitrary defSite .
    coarbitrary tokenBased

instance Arbitrary TokenBased where
  arbitrary = elements [TokenBased, NotOnlyTokenBased]

  shrink TokenBased        = [NotOnlyTokenBased]
  shrink NotOnlyTokenBased = []

instance CoArbitrary TokenBased where
  coarbitrary TokenBased        = variant 0
  coarbitrary NotOnlyTokenBased = variant 1

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

smaller :: Int -> Gen a -> Gen a
smaller k g = sized $ \ n -> resize (div n k) g

instance Arbitrary File where
  arbitrary = smaller 5 $ fmap (File . IntMap.fromList) $ listOf arbitrary
  shrink    = map (File . IntMap.fromList) . shrink . IntMap.toList . toMap

instance CoArbitrary File where
  coarbitrary (File rs) = coarbitrary (IntMap.toAscList rs)

instance Arbitrary CompressedFile where
  arbitrary = smaller 5 $ do
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
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
--
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.Interaction.Highlighting.Precise" $allProperties
