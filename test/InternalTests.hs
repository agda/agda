-- | Responsible for running all internal tests.

-- NB. Before adding new importations see the 'Internal
-- test-suite' section in the HACKING file.

module Main ( main ) where

import System.Exit ( exitFailure, exitSuccess )

import InternalTests.Helpers
import Agda.Utils.Monad ( ifM )

import InternalTests.Compiler.MAlonzo.Encode                  as CompEnco     ( tests )
import InternalTests.Interaction.Highlighting.Precise         as IntePrec     ( tests )
import InternalTests.Interaction.Highlighting.Range           as InteRang     ( tests )
import InternalTests.Interaction.Library                      as Library      ( tests )
import InternalTests.Interaction.Options                      as InteOpti     ( tests )
import InternalTests.Syntax.Common                            as SyntCommon   ( tests )
import InternalTests.Syntax.Internal                          as SyntInternal ( tests )
import InternalTests.Syntax.Parser.Parser                     as SyntPars     ( tests )
import InternalTests.Syntax.Position                          as SyntPosi     ( tests )
import InternalTests.Termination.CallGraph                    as TermCall     ( tests )
import InternalTests.Termination.CallMatrix                   as TermCM       ( tests )
import InternalTests.Termination.Order                        as TermOrd      ( tests )
import InternalTests.Termination.Semiring                     as TermRing     ( tests )
import InternalTests.Termination.SparseMatrix                 as TermSparse   ( tests )
import InternalTests.Termination.Termination                  as TermTerm     ( tests )
import InternalTests.TypeChecking                             as TypeChck     ( tests )
import InternalTests.TypeChecking.Free                        as Free         ( tests )
import InternalTests.TypeChecking.Generators                  as Generators   ( tests )
import InternalTests.TypeChecking.Irrelevance                 as Irrel        ( tests )
import InternalTests.TypeChecking.Monad.Base                  as MBase        ( tests )
import InternalTests.TypeChecking.Positivity                  as Positivity   ( tests )
import InternalTests.TypeChecking.Positivity.Occurrence       as Occurrence   ( tests )
import InternalTests.TypeChecking.Rules.LHS.Problem           as LHSProblem   ( tests )
import InternalTests.TypeChecking.SizedTypes                  as SizedTypes   ( tests )
import InternalTests.TypeChecking.Substitute                  as Substitute   ( tests )
import InternalTests.Utils.Bag                                as UtilBag      ( tests )
import InternalTests.Utils.BiMap                              as UtilBiMap    ( tests )
import InternalTests.Utils.Cluster                            as UtilClust    ( tests )
import InternalTests.Utils.Either                             as UtilEith     ( tests )
import InternalTests.Utils.Favorites                          as UtilFav      ( tests )
import InternalTests.Utils.FileName                           as UtilFile     ( tests )
import InternalTests.Utils.Graph.AdjacencyMap.Unidirectional  as UtilGraphUni ( tests )
import InternalTests.Utils.IntSet                             as UtilIntSet   ( tests )
import InternalTests.Utils.List                               as UtilList     ( tests )
import InternalTests.Utils.ListT                              as UtilListT    ( tests )
import InternalTests.Utils.Maybe.Strict                       as UtilMaybeS   ( tests )
import InternalTests.Utils.Monoid                             as UtilMonoid   ( tests )
import InternalTests.Utils.PartialOrd                         as UtilPOrd     ( tests )
import InternalTests.Utils.Permutation                        as UtilPerm     ( tests )
import InternalTests.Utils.Three                              as UtilThree    ( tests )
import InternalTests.Utils.Trie                               as UtilTrie     ( tests )
import InternalTests.Utils.Warshall                           as UtilWarsh    ( tests )

-- Keep this list ordered by the importation order, please!
runAllTests :: IO Bool
runAllTests = runTests "QuickCheck test suite:"
  [ CompEnco.tests
  , IntePrec.tests
  , InteRang.tests
  , Library.tests
  , InteOpti.tests
  , SyntCommon.tests
  , SyntInternal.tests
  , SyntPars.tests
  , SyntPosi.tests
  , TermCall.tests
  , TermCM.tests
  , TermOrd.tests
  , TermRing.tests
  , TermSparse.tests
  , TermTerm.tests
  , TypeChck.tests
  , Free.tests
  , Generators.tests
  , Irrel.tests
  , MBase.tests
  , Positivity.tests
  , Occurrence.tests
  , LHSProblem.tests
  , SizedTypes.tests
  , Substitute.tests
  , UtilBag.tests
  , UtilBiMap.tests
  , UtilClust.tests
  , UtilEith.tests
  , UtilFav.tests
  , UtilFile.tests
  , UtilGraphUni.tests
  , UtilIntSet.tests
  , UtilList.tests
  , UtilListT.tests
  , UtilMaybeS.tests
  , UtilMonoid.tests
  , UtilPOrd.tests
  , UtilPerm.tests
  , UtilThree.tests
  , UtilTrie.tests
  , UtilWarsh.tests
  ]

main :: IO ()
main = ifM runAllTests exitSuccess exitFailure
