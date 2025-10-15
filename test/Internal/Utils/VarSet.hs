{-# LANGUAGE TemplateHaskell       #-}

module Internal.Utils.VarSet ( tests ) where

import Test.QuickCheck

import Data.Coerce
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe

import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet
import Agda.Utils.Serialize

import Internal.Helpers

-- | An integer in the range @[0..1024]@.
newtype Var = Var { unVar :: Int }
  deriving (Eq, Ord, Show)

instance Arbitrary Var where
  arbitrary = Var <$> chooseInt (0, 1024)
  shrink (Var n) = Var <$> drop 1 (takeWhile (> 0) $ iterate (`quot` 2) n)

pattern Vars :: [Int] -> [Var]
pattern Vars ns <- (coerce @[Var] @[Int] -> ns)
{-# COMPLETE Vars #-}

sameElems :: VarSet -> IntSet -> Property
sameElems xs ys = VarSet.toAscList xs === IntSet.toAscList ys

--------------------------------------------------------------------------------
-- Construction

prop_empty :: Property
prop_empty = VarSet.empty `sameElems` IntSet.empty

prop_singleton :: Var -> Property
prop_singleton (Var n) = VarSet.singleton n `sameElems` IntSet.singleton n

prop_fromList :: [Var] -> Property
prop_fromList (Vars ns) = VarSet.fromList ns `sameElems` IntSet.fromList ns

prop_full :: Var -> Property
prop_full (Var n) = VarSet.full n `sameElems` IntSet.fromList [0..n-1]

-- We only have 'IntSet.fromRange' for @containers >= 0.7@, which
-- is not on stackage for GHC 9.6.7.
prop_range :: Var -> Var -> Property
prop_range (Var lo) (Var hi) =
  VarSet.range (lo - 1) (hi + 1) `sameElems` IntSet.fromList [lo..hi]

--------------------------------------------------------------------------------
-- Insertion

prop_insert :: Var -> [Var] -> Property
prop_insert (Var n) (Vars ns) =
  VarSet.insert n (VarSet.fromList ns) `sameElems` IntSet.insert n (IntSet.fromList ns)

--------------------------------------------------------------------------------
-- Deletion

prop_delete :: Var -> [Var] -> Property
prop_delete (Var n) (Vars ns) =
  VarSet.delete n (VarSet.fromList ns) `sameElems` IntSet.delete n (IntSet.fromList ns)

--------------------------------------------------------------------------------
-- Queries

prop_null :: [Var] -> Property
prop_null (Vars ns) =
  VarSet.null (VarSet.fromList ns) === IntSet.null (IntSet.fromList ns)

prop_member :: Var -> [Var] -> Property
prop_member (Var n) (Vars ns) =
  VarSet.member n (VarSet.fromList ns) === IntSet.member n (IntSet.fromList ns)

-- @lookupMin@ is only available in @containers >= 0.8@, so we emulate it instead.
prop_lookupMin :: [Var] -> Property
prop_lookupMin (Vars []) = VarSet.lookupMin VarSet.empty === Nothing
prop_lookupMin (Vars ns) = fromJust (VarSet.lookupMin (VarSet.fromList ns)) === IntSet.findMin (IntSet.fromList ns)

prop_size :: [Var] -> Property
prop_size (Vars ns) =
    VarSet.size (VarSet.fromList ns) === IntSet.size (IntSet.fromList ns)

prop_disjoint :: [Var] -> [Var] -> Property
prop_disjoint (Vars ns1) (Vars ns2) =
    VarSet.disjoint (VarSet.fromList ns1) (VarSet.fromList ns2) === IntSet.disjoint (IntSet.fromList ns1) (IntSet.fromList ns2)

prop_isSubsetOf :: [Var] -> [Var] -> Property
prop_isSubsetOf (Vars ns1) (Vars ns2) =
    VarSet.isSubsetOf (VarSet.fromList ns1) (VarSet.fromList ns2) === IntSet.isSubsetOf (IntSet.fromList ns1) (IntSet.fromList ns2)

-- There is no analog to 'VarSet.inRange', so we have to emulate it.
prop_inRange :: Var -> Var -> [Var] -> Property
prop_inRange (Var lo) (Var hi) (Vars ns) =
  let intSet = IntSet.fromList ns in
  VarSet.inRange (lo - 1) (hi + 1) (VarSet.fromList ns) === (IntSet.lookupLT lo intSet == Nothing && IntSet.lookupGT hi intSet == Nothing)

--------------------------------------------------------------------------------
-- Combining VarSets

prop_union :: [Var] -> [Var] -> Property
prop_union (Vars ns1) (Vars ns2) =
    VarSet.union (VarSet.fromList ns1) (VarSet.fromList ns2) `sameElems` IntSet.union (IntSet.fromList ns1) (IntSet.fromList ns2)

prop_unions :: [[Var]] -> Property
prop_unions nss =
  VarSet.unions (fmap (VarSet.fromList . coerce) nss) `sameElems` IntSet.unions (fmap (IntSet.fromList . coerce) nss)

prop_intersection :: [Var] -> [Var] -> Property
prop_intersection (Vars ns1) (Vars ns2) =
    VarSet.intersection (VarSet.fromList ns1) (VarSet.fromList ns2) `sameElems` IntSet.intersection (IntSet.fromList ns1) (IntSet.fromList ns2)

prop_difference :: [Var] -> [Var] -> Property
prop_difference (Vars ns1) (Vars ns2) =
    VarSet.difference (VarSet.fromList ns1) (VarSet.fromList ns2) `sameElems` IntSet.difference (IntSet.fromList ns1) (IntSet.fromList ns2)

prop_complement :: Var -> [Var] -> Property
prop_complement (Var n) (Vars ns) =
  VarSet.complement n (VarSet.fromList ns) `sameElems` (IntSet.fromList [0..n-1] IntSet.\\ IntSet.fromList ns)

--------------------------------------------------------------------------------
-- Filters

prop_split :: Var -> [Var] -> Property
prop_split (Var n) (Vars ns) =
    let (vs1, vs2) = VarSet.split n (VarSet.fromList ns)
        (is1, is2) = IntSet.split n (IntSet.fromList ns)
    in (vs1 `sameElems` is1) .&&. (vs2 `sameElems` is2)

--------------------------------------------------------------------------------
-- Views

prop_minView :: [Var] -> Property
prop_minView (Vars ns) =
  case (VarSet.minView (VarSet.fromList ns), IntSet.minView (IntSet.fromList ns)) of
    (Just (v, vs), Just (i, is)) -> (v === i) .&&. (vs `sameElems` is)
    (Nothing, Nothing) -> property True
    (vs, is) -> counterexample (show vs <> " /= " <> show is) (property False)

--------------------------------------------------------------------------------
-- Folds

prop_foldr :: (Function a, CoArbitrary a, Arbitrary a, Show a, Eq a) => Fun (Int, a) a -> a -> [Var] -> Property
prop_foldr f a (Vars xs) =
  VarSet.foldr (applyFun2 f) a (VarSet.fromList xs) === IntSet.foldr (applyFun2 f) a (IntSet.fromList xs)

prop_foldl :: (Function a, CoArbitrary a, Arbitrary a, Show a, Eq a) => Fun (a, Int) a -> a -> [Var] -> Property
prop_foldl f a (Vars xs) =
  VarSet.foldl (applyFun2 f) a (VarSet.fromList xs) === IntSet.foldl (applyFun2 f) a (IntSet.fromList xs)

--------------------------------------------------------------------------------
-- Contextual operations

prop_strengthen :: Var -> [Var] -> Property
prop_strengthen (Var n) (Vars ns) =
  VarSet.strengthen n (VarSet.fromList ns) `sameElems` IntSet.filter (>= 0) (IntSet.map (\x -> x - n) (IntSet.fromList ns))

prop_weaken :: Var -> [Var] -> Property
prop_weaken (Var n) (Vars ns) =
  VarSet.weaken n (VarSet.fromList ns) `sameElems` IntSet.map (\x -> x + n) (IntSet.fromList ns)

--------------------------------------------------------------------------------
-- Conversions

prop_toDescList :: [Var] -> Property
prop_toDescList (Vars ns) =
  VarSet.toDescList (VarSet.fromList ns) === IntSet.toDescList (IntSet.fromList ns)

-- Technically redundant as 'sameElems' uses toDescList, but if this
-- fails we know something has truly gone south.
prop_toAscList :: [Var] -> Property
prop_toAscList (Vars ns) =
  VarSet.toAscList (VarSet.fromList ns) === IntSet.toAscList (IntSet.fromList ns)

--------------------------------------------------------------------------------
-- Serialization

prop_decode_encode :: [Var] -> Property
prop_decode_encode (Vars ns) =
  let xs = VarSet.fromList ns
  in deserializePure @VarSet (serializePure xs) === xs


------------------------------------------------------------------------
-- All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

tests :: TestTree
tests = testProperties "Internal.Utils.VarSet" $allProperties
