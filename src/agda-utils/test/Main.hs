-- | Responsible for grouping all internal tests.

-- NB. Before adding new importations see the 'Internal
-- test-suite' section in the HACKING file.

module Main where

import Internal.Helpers

import Test.Tasty as T
import Test.Tasty.Silver.Interactive as TM
import Test.Tasty.Silver.Filter (RegexFilter)

import System.Exit

--import Utils
import qualified Internal.Utils.AssocList                          as UtilAList    ( tests )
import qualified Internal.Utils.Bag                                as UtilBag      ( tests )
import qualified Internal.Utils.BiMap                              as UtilBiMap    ( tests )
import qualified Internal.Utils.Cluster                            as UtilClust    ( tests )
import qualified Internal.Utils.Either                             as UtilEith     ( tests )
import qualified Internal.Utils.Favorites                          as UtilFav      ( tests )
import qualified Internal.Utils.FileName                           as UtilFile     ( tests )
--import qualified Internal.Utils.Graph.AdjacencyMap.Unidirectional  as UtilGraphUni ( tests )
import qualified Internal.Utils.IntSet                             as UtilIntSet   ( tests )
import qualified Internal.Utils.List                               as UtilList     ( tests )
import qualified Internal.Utils.ListT                              as UtilListT    ( tests )
import qualified Internal.Utils.Maybe.Strict                       as UtilMaybeS   ( tests )
import qualified Internal.Utils.Monoid                             as UtilMonoid   ( tests )
import qualified Internal.Utils.NonEmptyList                       as UtilNonEmpty ( tests )
import qualified Internal.Utils.PartialOrd                         as UtilPOrd     ( tests )
--import qualified Internal.Utils.Permutation                        as UtilPerm     ( tests )
import qualified Internal.Utils.Three                              as UtilThree    ( tests )
import qualified Internal.Utils.Trie                               as UtilTrie     ( tests )
import qualified Internal.Utils.Warshall                           as UtilWarsh    ( tests )

main :: IO ()
main = TM.defaultMain tests

-- Keep this list in the import order, please!
tests :: TestTree
tests = testGroup "Utils"
  [ UtilAList.tests
  , UtilBag.tests
  , UtilBiMap.tests
  , UtilClust.tests
  , UtilEith.tests
  , UtilFav.tests
  , UtilFile.tests
--  , UtilGraphUni.tests
  , UtilIntSet.tests
  , UtilList.tests
  , UtilListT.tests
  , UtilMaybeS.tests
  , UtilMonoid.tests
  , UtilNonEmpty.tests
  , UtilPOrd.tests
--  , UtilPerm.tests
  , UtilThree.tests
  , UtilTrie.tests
  , UtilWarsh.tests
  ]
