-- | Responsible for running all internal tests.

module Main ( main ) where

import InternalTests.Helpers

import InternalTests.Compiler.MAlonzo.Encode                  as CompEnco     ( tests )
import InternalTests.Interaction.Highlighting.Emacs           as InteEmac     ( tests )
import InternalTests.Interaction.Highlighting.Generate        as InteGene     ( tests )
import InternalTests.Interaction.Highlighting.Precise         as IntePrec     ( tests )
import InternalTests.Interaction.Highlighting.Range           as InteRang     ( tests )
import InternalTests.Interaction.Options                      as InteOpti     ( tests )
import InternalTests.Syntax.Parser.Parser                     as SyntPars     ( tests )
import Agda.Syntax.Position                                   as SyntPosi     ( tests )
import Agda.Termination.CallGraph                             as TermCall     ( tests )
import Agda.Termination.CallMatrix                            as TermCM       ( tests )
import Agda.Termination.Order                                 as TermOrd      ( tests )
import Agda.Termination.Semiring                              as TermRing     ( tests )
import Agda.Termination.SparseMatrix                          as TermSparse   ( tests )
import Agda.Termination.Termination                           as TermTerm     ( tests )
import InternalTests.TypeChecking.Free                        as Free         ( tests )
import InternalTests.TypeChecking.Irrelevance                 as Irrel        ( tests )
import InternalTests.TypeChecking.Positivity                  as Positivity   ( tests )
import Agda.TypeChecking.Positivity.Occurrence                as Occurrence   ( tests )
import Agda.TypeChecking.Tests                                as TypeChck     ( tests )
import InternalTests.TypeChecking.SizedTypes                  as SizedTypes   ( tests )
import Agda.Utils.Bag                                         as UtilBag      ( tests )
import Agda.Utils.BiMap                                       as UtilBiMap    ( tests )
import Agda.Utils.Cluster                                     as UtilClust    ( tests )
import Agda.Utils.Either                                      as UtilEith     ( tests )
import Agda.Utils.Favorites                                   as UtilFav      ( tests )
import Agda.Utils.FileName                                    as UtilFile     ( tests )
import InternalTests.Utils.Graph.AdjacencyMap.Unidirectional  as UtilGraphUni ( tests )
import Agda.Utils.List                                        as UtilList     ( tests )
import Agda.Utils.ListT.Tests                                 as UtilListT    ( tests )
import Agda.Utils.PartialOrd                                  as UtilPOrd     ( tests )
import InternalTests.Utils.Permutation                        as UtilPerm     ( tests )
import InternalTests.Utils.Trie                               as UtilTrie     ( tests )
import InternalTests.Utils.Warshall                           as UtilWarsh    ( tests )

main :: IO Bool
main = runTests "QuickCheck test suite:"
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
  ]
