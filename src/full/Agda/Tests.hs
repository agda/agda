{-# OPTIONS_GHC -fwarn-missing-signatures #-}

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
import Agda.Termination.CallGraph             as TermCall   (tests)
import Agda.Termination.CallMatrix            as TermCM     (tests)
-- import Agda.Termination.Lexicographic         as TermLex    (tests)
-- import Agda.Termination.Matrix                as TermMatrix (tests)
import Agda.Termination.Order                 as TermOrd    (tests)
import Agda.Termination.Semiring              as TermRing   (tests)
import Agda.Termination.SparseMatrix          as TermSparse (tests)
import Agda.Termination.Termination           as TermTerm   (tests)
import Agda.TypeChecking.Irrelevance          as Irrel      (tests)
import Agda.TypeChecking.Tests                as TypeChck   (tests)
import Agda.TypeChecking.SizedTypes.Tests     as SizedTypes (tests)
import Agda.Utils.Bag                         as UtilBag    (tests)
import Agda.Utils.BiMap                       as UtilBiMap  (tests)
import Agda.Utils.Cluster                     as UtilClust  (tests)
import Agda.Utils.Either                      as UtilEith   (tests)
import Agda.Utils.Favorites                   as UtilFav    (tests)
import Agda.Utils.FileName                    as UtilFile   (tests)
import Agda.Utils.Graph.AdjacencyMap          as UtilGrap   (tests)
import Agda.Utils.Graph.AdjacencyMap.Unidirectional as UtilGraphUni (tests)
import Agda.Utils.List                        as UtilList   (tests)
import Agda.Utils.PartialOrd                  as UtilPOrd   (tests)
import Agda.Utils.Warshall                    as UtilWarsh  (tests)

testSuite :: IO Bool
testSuite = runTests "QuickCheck test suite:"
  [ Irrel.tests
  , SizedTypes.tests
  , UtilFav.tests
  , UtilPOrd.tests
  , CompEnco.tests
  , InteEmac.tests
  , InteGene.tests
  , IntePrec.tests
  , InteRang.tests
  , InteOpti.tests
  , SyntPars.tests
  , SyntPosi.tests
  , TermCall.tests
  , TermCM.tests
--  , TermLex.tests
--  , TermMatrix.tests
  , TermOrd.tests
  , TermRing.tests
  , TermSparse.tests
  , TermTerm.tests
  , TypeChck.tests
  , UtilBag.tests
  , UtilBiMap.tests
  , UtilClust.tests
  , UtilEith.tests
  , UtilFile.tests
  , UtilGrap.tests
  , UtilGraphUni.tests
  , UtilList.tests
  , UtilWarsh.tests
  ]
