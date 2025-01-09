-- | Responsible for grouping all internal tests.

-- NB. Before adding new importations see the 'Internal
-- test-suite' section in the HACKING file.

module Internal.Tests ( tests ) where

import Internal.Helpers

import qualified Internal.Compiler.MAlonzo.Encode
import qualified Internal.Interaction.Highlighting.Precise
import qualified Internal.Interaction.Highlighting.Range
import qualified Internal.Interaction.Library
import qualified Internal.Interaction.Options
import qualified Internal.Syntax.Common
import qualified Internal.Syntax.Internal
import qualified Internal.Syntax.Internal.Univ
import qualified Internal.Syntax.Position
import qualified Internal.Termination.CallGraph
import qualified Internal.Termination.CallMatrix
import qualified Internal.Termination.Order
import qualified Internal.Termination.Semiring
import qualified Internal.Termination.SparseMatrix
import qualified Internal.Termination.Termination
import qualified Internal.TypeChecking
import qualified Internal.TypeChecking.Free
import qualified Internal.TypeChecking.Generators
import qualified Internal.TypeChecking.Irrelevance
import qualified Internal.TypeChecking.Monad.Base
import qualified Internal.TypeChecking.Positivity
import qualified Internal.TypeChecking.Positivity.Occurrence
import qualified Internal.TypeChecking.Rules.LHS.Problem
import qualified Internal.TypeChecking.SizedTypes
import qualified Internal.TypeChecking.Substitute
import qualified Internal.Utils.AssocList
import qualified Internal.Utils.Bag
import qualified Internal.Utils.BiMap
import qualified Internal.Utils.Cluster
import qualified Internal.Utils.Either
import qualified Internal.Utils.Favorites
import qualified Internal.Utils.FileName
import qualified Internal.Utils.Graph.AdjacencyMap.Unidirectional
import qualified Internal.Utils.IntSet
import qualified Internal.Utils.Lens
import qualified Internal.Utils.List
import qualified Internal.Utils.List1
import qualified Internal.Utils.List2
import qualified Internal.Utils.ListT
import qualified Internal.Utils.Maybe.Strict
import qualified Internal.Utils.Monad
import qualified Internal.Utils.Monoid
import qualified Internal.Utils.PartialOrd
import qualified Internal.Utils.Permutation
import qualified Internal.Utils.RangeMap
import qualified Internal.Utils.SmallSet
import qualified Internal.Utils.Three
import qualified Internal.Utils.Trie

-- Keep this list in the import order, please!
tests :: TestTree
tests = testGroup "Internal" $
  Internal.Compiler.MAlonzo.Encode.tests :
  Internal.Interaction.Highlighting.Precise.tests :
  Internal.Interaction.Highlighting.Range.tests :
  Internal.Interaction.Library.tests :
  Internal.Interaction.Options.tests :
  Internal.Syntax.Common.tests :
  Internal.Syntax.Internal.tests :
  Internal.Syntax.Internal.Univ.tests :
  Internal.Syntax.Position.tests :
  Internal.Termination.CallGraph.tests :
  Internal.Termination.CallMatrix.tests :
  Internal.Termination.Order.tests :
  Internal.Termination.Semiring.tests :
  Internal.Termination.SparseMatrix.tests :
  Internal.Termination.Termination.tests :
  Internal.TypeChecking.tests :
  Internal.TypeChecking.Free.tests :
  Internal.TypeChecking.Generators.tests :
  Internal.TypeChecking.Irrelevance.tests :
  Internal.TypeChecking.Monad.Base.tests :
  Internal.TypeChecking.Positivity.tests :
  Internal.TypeChecking.Positivity.Occurrence.tests :
  Internal.TypeChecking.Rules.LHS.Problem.tests :
  Internal.TypeChecking.SizedTypes.tests :
  Internal.TypeChecking.Substitute.tests :
  Internal.Utils.AssocList.tests :
  Internal.Utils.Bag.tests :
  Internal.Utils.BiMap.tests :
  Internal.Utils.Cluster.tests :
  Internal.Utils.Either.tests :
  Internal.Utils.Favorites.tests :
  Internal.Utils.FileName.tests :
  Internal.Utils.Graph.AdjacencyMap.Unidirectional.tests :
  Internal.Utils.IntSet.tests :
  Internal.Utils.Lens.tests :
  Internal.Utils.List.tests :
  Internal.Utils.List1.tests :
  Internal.Utils.List2.tests :
  Internal.Utils.ListT.tests :
  Internal.Utils.Maybe.Strict.tests :
  Internal.Utils.Monad.tests :
  Internal.Utils.Monoid.tests :
  Internal.Utils.PartialOrd.tests :
  Internal.Utils.Permutation.tests :
  Internal.Utils.RangeMap.tests :
  Internal.Utils.SmallSet.tests :
  Internal.Utils.Three.tests :
  Internal.Utils.Trie.tests :
  []
