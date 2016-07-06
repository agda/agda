-- | Responsible for running all internal tests.

module Main (main) where

import Internal.TestHelpers

import Internal.Compiler.MAlonzo.Encode                   as CompEnco     (tests)
import Internal.Interaction.Highlighting.Emacs            as InteEmac     (tests)
import Internal.Interaction.Highlighting.Generate         as InteGene     (tests)
import Internal.Interaction.Highlighting.Precise          as IntePrec     (tests)
import Internal.Interaction.Highlighting.Range            as InteRang     (tests)
import Agda.Interaction.Options                           as InteOpti     (tests)
import Agda.Syntax.Parser.Parser                          as SyntPars     (tests)
import Agda.Syntax.Position                               as SyntPosi     (tests)
import Agda.Termination.CallGraph                         as TermCall     (tests)
import Agda.Termination.CallMatrix                        as TermCM       (tests)
import Agda.Termination.Order                             as TermOrd      (tests)
import Agda.Termination.Semiring                          as TermRing     (tests)
import Agda.Termination.SparseMatrix                      as TermSparse   (tests)
import Agda.Termination.Termination                       as TermTerm     (tests)
import Internal.TypeChecking.Free                         as Free         (tests)
import Agda.TypeChecking.Irrelevance                      as Irrel        (tests)
import Agda.TypeChecking.Positivity.Tests                 as Positivity   (tests)
import Agda.TypeChecking.Positivity.Occurrence            as Occurrence   (tests)
import Agda.TypeChecking.Tests                            as TypeChck     (tests)
import Agda.TypeChecking.SizedTypes.Tests                 as SizedTypes   (tests)
import Agda.Utils.Bag                                     as UtilBag      (tests)
import Agda.Utils.BiMap                                   as UtilBiMap    (tests)
import Agda.Utils.Cluster                                 as UtilClust    (tests)
import Agda.Utils.Either                                  as UtilEith     (tests)
import Agda.Utils.Favorites                               as UtilFav      (tests)
import Agda.Utils.FileName                                as UtilFile     (tests)
import Agda.Utils.Graph.AdjacencyMap.Unidirectional.Tests as UtilGraphUni (tests)
import Agda.Utils.List                                    as UtilList     (tests)
import Agda.Utils.ListT.Tests                             as UtilListT    (tests)
import Agda.Utils.PartialOrd                              as UtilPOrd     (tests)
import Agda.Utils.Permutation.Tests                       as UtilPerm     (tests)
import Agda.Utils.Trie                                    as UtilTrie     (tests)
import Agda.Utils.Warshall                                as UtilWarsh    (tests)

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
