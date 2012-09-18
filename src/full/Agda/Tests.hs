
-- | Responsible for running all internal tests.
module Agda.Tests (testSuite) where

import Agda.Utils.TestHelpers

import Agda.Compiler.MAlonzo.Encode           as CompEnco   (tests)
import Agda.Interaction.Highlighting.Emacs    as InteEmac   (tests)
import Agda.Interaction.Highlighting.Generate as InteGene   (tests)
import Agda.Interaction.Highlighting.Precise  as IntePrec   (tests)
import Agda.Interaction.Highlighting.Range    as InteRang   (tests)
import Agda.Interaction.Options               as InteOpti   (tests)
import Agda.Syntax.Parser.Parser              as SyntPars   (tests)
import Agda.Syntax.Position                   as SyntPosi   (tests)
import Agda.Termination.Termination	      as TermTerm   (tests)
import Agda.Termination.CallGraph	      as TermCall   (tests)
import Agda.Termination.Lexicographic         as TermLex    (tests)
import Agda.Termination.Matrix                as TermMatrix (tests)
import Agda.Termination.Semiring	      as TermRing   (tests)
import Agda.Termination.SparseMatrix          as TermSparse (tests)
import Agda.TypeChecking.Irrelevance          as Irrel      (tests)
import Agda.TypeChecking.Tests                as TypeChck   (tests)
import Agda.Utils.Either	              as UtilEith   (tests)
import Agda.Utils.FileName                    as UtilFile   (tests)
import Agda.Utils.Graph                       as UtilGrap   (tests)
import Agda.Utils.List                        as UtilList   (tests)
import Agda.Utils.Warshall                    as UtilWarsh  (tests)

testSuite :: IO Bool
testSuite = runTests "QuickCheck test suite:"
  [ Irrel.tests
  , CompEnco.tests
  , InteEmac.tests
  , InteGene.tests
  , IntePrec.tests
  , InteRang.tests
  , InteOpti.tests
  , SyntPars.tests
  , SyntPosi.tests
  , TermTerm.tests
  , TermCall.tests
  , TermLex.tests
  , TermMatrix.tests
  , TermRing.tests
  , TermSparse.tests
  , TypeChck.tests
  , UtilEith.tests
  , UtilFile.tests
  , UtilGrap.tests
  , UtilList.tests
  , UtilWarsh.tests
  ]
