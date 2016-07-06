-- | Responsible for running all internal tests.
module Agda.Tests (testSuite) where

import Agda.Utils.TestHelpers

import Agda.Syntax.Position                   as SyntPosi   (tests)
import Agda.Termination.CallGraph             as TermCall   (tests)
import Agda.Termination.CallMatrix            as TermCM     (tests)
import Agda.Termination.Order                 as TermOrd    (tests)
import Agda.Termination.Semiring              as TermRing   (tests)
import Agda.Termination.SparseMatrix          as TermSparse (tests)
import Agda.Termination.Termination           as TermTerm   (tests)
import Agda.TypeChecking.Positivity.Occurrence as Occurrence (tests)
import Agda.TypeChecking.Tests                as TypeChck   (tests)
import Agda.Utils.Bag                         as UtilBag    (tests)
import Agda.Utils.BiMap                       as UtilBiMap  (tests)
import Agda.Utils.Cluster                     as UtilClust  (tests)
import Agda.Utils.Either                      as UtilEith   (tests)
import Agda.Utils.Favorites                   as UtilFav    (tests)
import Agda.Utils.FileName                    as UtilFile   (tests)
import Agda.Utils.List                        as UtilList   (tests)
import Agda.Utils.ListT.Tests                 as UtilListT  (tests)
import Agda.Utils.PartialOrd                  as UtilPOrd   (tests)

testSuite :: IO Bool
testSuite = runTests "QuickCheck test suite:"
  [ UtilFav.tests
  , UtilListT.tests
  , UtilPOrd.tests
  , SyntPosi.tests
  , TermCall.tests
  , TermCM.tests
  , TermOrd.tests
  , TermRing.tests
  , TermSparse.tests
  , TermTerm.tests
  , Occurrence.tests
  , TypeChck.tests
  , UtilBag.tests
  , UtilBiMap.tests
  , UtilClust.tests
  , UtilEith.tests
  , UtilFile.tests
  , UtilList.tests
  ]
