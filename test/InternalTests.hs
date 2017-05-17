-- | Responsible for running all internal tests.

-- NB. Before adding new importations see the 'Internal
-- test-suite' section in the HACKING file.

module Main ( main ) where

import System.Exit ( exitFailure, exitSuccess )

import InternalTests.Helpers
import Agda.Utils.Monad ( ifM )

import InternalTests.Compiler.MAlonzo.Encode                  as CompEnco     ( tests )
import InternalTests.Interaction.Highlighting.Emacs           as InteEmac     ( tests )
import InternalTests.Interaction.Highlighting.Generate        as InteGene     ( tests )
import InternalTests.Interaction.Highlighting.Precise         as IntePrec     ( tests )
import InternalTests.Interaction.Highlighting.Range           as InteRang     ( tests )
import InternalTests.Interaction.Options                      as InteOpti     ( tests )
import InternalTests.Syntax.Common                            as SyntCommon   ( tests )
import InternalTests.Syntax.Internal                          as SyntInternal ( tests )
import InternalTests.Syntax.Parser.Parser                     as SyntPars     ( tests )
import InternalTests.Syntax.Position                          as SyntPosi     ( tests )
import InternalTests.Termination.CallGraph                    as TermCall     ( tests )
import InternalTests.Termination.CallMatrix                   as TermCM       ( tests )
import InternalTests.Termination.Order                        as TermOrd      ( tests )
import InternalTests.Termination.Semiring                     as TermRing     ( tests )
import InternalTests.Termination.Termination                  as TermTerm     ( tests )
import InternalTests.Termination.SparseMatrix                 as TermSparse   ( tests )
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
import InternalTests.Utils.List                               as UtilList     ( tests )
import InternalTests.Utils.ListT                              as UtilListT    ( tests )
import InternalTests.Utils.Maybe.Strict                       as UtilMaybeS   ( tests )
import InternalTests.Utils.Monoid                             as UtilMonoid   ( tests )
import InternalTests.Utils.PartialOrd                         as UtilPOrd     ( tests )
import InternalTests.Utils.Permutation                        as UtilPerm     ( tests )
import InternalTests.Utils.Trie                               as UtilTrie     ( tests )
import InternalTests.Utils.Warshall                           as UtilWarsh    ( tests )

runAllTests :: IO Bool
runAllTests = runTests "QuickCheck test suite:"
  [ Free.tests
  , Irrel.tests
  , SizedTypes.tests
  , UtilFav.tests
  , UtilListT.tests
  , UtilPerm.tests
  , UtilPOrd.tests
  , CompEnco.tests
  , InteEmac.tests
  , InteGene.tests
  , IntePrec.tests
  , InteRang.tests
  , InteOpti.tests
  , Substitute.tests
  , SyntPars.tests
  , SyntPosi.tests
  , TermCall.tests
  , TermCM.tests
  , TermOrd.tests
  , TermRing.tests
  , TermSparse.tests
  , TermTerm.tests
  , Positivity.tests
  , Occurrence.tests
  , TypeChck.tests
  , UtilBag.tests
  , UtilBiMap.tests
  , UtilClust.tests
  , UtilEith.tests
  , UtilFile.tests
  , UtilGraphUni.tests
  , UtilList.tests
  , UtilTrie.tests
  , UtilWarsh.tests
  , Generators.tests
  , UtilMonoid.tests
  , LHSProblem.tests
  , MBase.tests
  , SyntInternal.tests
  , SyntCommon.tests
  , UtilMaybeS.tests
  ]

main :: IO ()
main = ifM runAllTests exitSuccess exitFailure
