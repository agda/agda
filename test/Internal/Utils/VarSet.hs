{-# LANGUAGE TemplateHaskell       #-}

module Internal.Utils.VarSet ( tests ) where

import Test.QuickCheck

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe

import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

import Internal.Helpers

var :: Gen Int
var = chooseInt (0, 1024)

vars :: Gen [Int]
vars = listOf var

vars1 :: Gen [Int]
vars1 = listOf1 var

sameElems :: VarSet -> IntSet -> Property
sameElems xs ys = VarSet.toAscList xs === IntSet.toAscList ys

prop_singleton :: Property
prop_singleton =
  forAll var \n -> VarSet.singleton n `sameElems` IntSet.singleton n

prop_fromList :: Property
prop_fromList =
  forAll vars \ns -> VarSet.fromList ns `sameElems` IntSet.fromList ns

prop_all :: Property
prop_all =
  forAll var \n -> VarSet.all n `sameElems` IntSet.fromList [0..n-1]

prop_insert :: Property
prop_insert =
  forAll var \n ->
  forAll vars \ns ->
  VarSet.insert n (VarSet.fromList ns) `sameElems` IntSet.insert n (IntSet.fromList ns)

prop_delete :: Property
prop_delete =
  forAll var \n ->
  forAll vars \ns ->
  VarSet.delete n (VarSet.fromList ns) `sameElems` IntSet.delete n (IntSet.fromList ns)

prop_null :: Property
prop_null =
  forAll vars \ns ->
  VarSet.null (VarSet.fromList ns) === IntSet.null (IntSet.fromList ns)

prop_member :: Property
prop_member =
  forAll var \n ->
  forAll vars \ns ->
  VarSet.member n (VarSet.fromList ns) === IntSet.member n (IntSet.fromList ns)

prop_lookupMinNothing :: Property
prop_lookupMinNothing = VarSet.lookupMin VarSet.empty === Nothing

prop_lookupMinJust :: Property
prop_lookupMinJust =
  forAll vars1 \ns ->
    fromJust (VarSet.lookupMin (VarSet.fromList ns)) === IntSet.findMin (IntSet.fromList ns)

prop_size :: Property
prop_size =
  forAll vars \ns ->
    VarSet.size (VarSet.fromList ns) === IntSet.size (IntSet.fromList ns)

prop_disjoint :: Property
prop_disjoint =
  forAll vars \ns1 ->
  forAll vars \ns2 ->
    VarSet.disjoint (VarSet.fromList ns1) (VarSet.fromList ns2) === IntSet.disjoint (IntSet.fromList ns1) (IntSet.fromList ns2)

prop_union :: Property
prop_union =
  forAll vars \ns1 ->
  forAll vars \ns2 ->
    VarSet.union (VarSet.fromList ns1) (VarSet.fromList ns2) `sameElems` IntSet.union (IntSet.fromList ns1) (IntSet.fromList ns2)

prop_intersection :: Property
prop_intersection =
  forAll vars \ns1 ->
  forAll vars \ns2 ->
    VarSet.intersection (VarSet.fromList ns1) (VarSet.fromList ns2) `sameElems` IntSet.intersection (IntSet.fromList ns1) (IntSet.fromList ns2)

prop_difference :: Property
prop_difference =
  forAll vars \ns1 ->
  forAll vars \ns2 ->
    VarSet.difference (VarSet.fromList ns1) (VarSet.fromList ns2) `sameElems` IntSet.difference (IntSet.fromList ns1) (IntSet.fromList ns2)

prop_isSubsetOf :: Property
prop_isSubsetOf =
  forAll vars \ns1 ->
  forAll vars \ns2 ->
    VarSet.isSubsetOf (VarSet.fromList ns1) (VarSet.fromList ns2) === IntSet.isSubsetOf (IntSet.fromList ns1) (IntSet.fromList ns2)

prop_split :: Property
prop_split =
  forAll var \n ->
  forAll vars \ns ->
    let (vs1, vs2) = VarSet.split n (VarSet.fromList ns)
        (is1, is2) = IntSet.split n (IntSet.fromList ns)
    in (vs1 `sameElems` is1) .&&. (vs2 `sameElems` is2)


------------------------------------------------------------------------
-- All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

tests :: TestTree
tests = testProperties "Internal.Utils.VarSet" $allProperties
