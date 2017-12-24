-- | Responsible for running all internal tests.

-- NB. Before adding new importations see the 'Internal
-- test-suite' section in the HACKING file.

module Main ( main ) where

import System.Exit ( exitFailure, exitSuccess )

import Internal.Helpers
import Agda.Utils.Monad ( ifM )

import Internal.Compiler.MAlonzo.Encode                  as CompEnco     ( tests )
import Internal.Interaction.Highlighting.Precise         as IntePrec     ( tests )
import Internal.Interaction.Highlighting.Range           as InteRang     ( tests )
import Internal.Interaction.Library                      as Library      ( tests )
import Internal.Interaction.Options                      as InteOpti     ( tests )
import Internal.Syntax.Common                            as SyntCommon   ( tests )
import Internal.Syntax.Internal                          as SyntInternal ( tests )
import Internal.Syntax.Parser.Parser                     as SyntPars     ( tests )
import Internal.Syntax.Position                          as SyntPosi     ( tests )
import Internal.Termination.CallGraph                    as TermCall     ( tests )
import Internal.Termination.CallMatrix                   as TermCM       ( tests )
import Internal.Termination.Order                        as TermOrd      ( tests )
import Internal.Termination.Semiring                     as TermRing     ( tests )
import Internal.Termination.SparseMatrix                 as TermSparse   ( tests )
import Internal.Termination.Termination                  as TermTerm     ( tests )
import Internal.TypeChecking                             as TypeChck     ( tests )
import Internal.TypeChecking.Free                        as Free         ( tests )
import Internal.TypeChecking.Generators                  as Generators   ( tests )
import Internal.TypeChecking.Irrelevance                 as Irrel        ( tests )
import Internal.TypeChecking.Monad.Base                  as MBase        ( tests )
import Internal.TypeChecking.Positivity                  as Positivity   ( tests )
import Internal.TypeChecking.Positivity.Occurrence       as Occurrence   ( tests )
import Internal.TypeChecking.Rules.LHS.Problem           as LHSProblem   ( tests )
import Internal.TypeChecking.SizedTypes                  as SizedTypes   ( tests )
import Internal.TypeChecking.Substitute                  as Substitute   ( tests )
import Internal.Utils.Bag                                as UtilBag      ( tests )
import Internal.Utils.BiMap                              as UtilBiMap    ( tests )
import Internal.Utils.Cluster                            as UtilClust    ( tests )
import Internal.Utils.Either                             as UtilEith     ( tests )
import Internal.Utils.Favorites                          as UtilFav      ( tests )
import Internal.Utils.FileName                           as UtilFile     ( tests )
import Internal.Utils.Graph.AdjacencyMap.Unidirectional  as UtilGraphUni ( tests )
import Internal.Utils.IntSet                             as UtilIntSet   ( tests )
import Internal.Utils.List                               as UtilList     ( tests )
import Internal.Utils.ListT                              as UtilListT    ( tests )
import Internal.Utils.Maybe.Strict                       as UtilMaybeS   ( tests )
import Internal.Utils.Monoid                             as UtilMonoid   ( tests )
import Internal.Utils.PartialOrd                         as UtilPOrd     ( tests )
import Internal.Utils.Permutation                        as UtilPerm     ( tests )
import Internal.Utils.Three                              as UtilThree    ( tests )
import Internal.Utils.Trie                               as UtilTrie     ( tests )
import Internal.Utils.Warshall                           as UtilWarsh    ( tests )

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
