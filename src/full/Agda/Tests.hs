
-- | Responsible for running all internal tests.
module Agda.Tests (testSuite) where

import Agda.Utils.TestHelpers

import Agda.Interaction.Highlighting.Emacs    as InteEmac   (tests)
import Agda.Interaction.Highlighting.Generate as InteGene   (tests)
import Agda.Interaction.Highlighting.Precise  as IntePrec   (tests)
import Agda.Interaction.Highlighting.Range    as InteRang   (tests)
import Agda.Termination.Termination	      as TermTerm   (tests)
import Agda.Termination.CallGraph	      as TermCall   (tests)
import Agda.Termination.Lexicographic         as TermLex    (tests)
import Agda.Termination.Matrix                as TermMatrix (tests)
import Agda.Termination.Semiring	      as TermRing   (tests)
import Agda.Termination.Utilities	      as TermUtil   (tests)
import Agda.TypeChecking.Tests                as TypeChck   (tests)
import Agda.Utils.Either	              as UtilEith   (tests)
import Agda.Utils.FileName                    as UtilFile   (tests)
import Agda.Utils.List                        as UtilList   (tests)

testSuite :: IO Bool
testSuite = runTests "QuickCheck test suite:"
  [ InteEmac.tests
  , InteGene.tests
  , IntePrec.tests
  , InteRang.tests
  , TermTerm.tests
  , TermUtil.tests
  , TermRing.tests
  , TermMatrix.tests
  , TermLex.tests
  , TermCall.tests
  , TypeChck.tests
  , UtilEith.tests
  , UtilFile.tests
  , UtilList.tests
  ]
