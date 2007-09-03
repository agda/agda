-- | Termination checker, based on
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch.
--
-- TODO: Note that we should also check that data type definitions are
-- strictly positive. Furthermore, for inductive-recursive families we
-- may need to do something more clever.

module Termination.Termination
  ( terminates
  , recursionBehaviours
  ) where

import Termination.Lexicographic
import Termination.Utilities
import Termination.CallGraph
import Termination.Matrix
import Control.Arrow
import Test.QuickCheck
import qualified Data.Set as Set
import qualified Data.Array as Array
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Array (Array)

-- | @'terminates' cs@ checks if the functions represented by @cs@
-- terminate. The call graph @cs@ should have one entry ('Call') per
-- recursive function application.
--
-- @'Right' perms@ is returned if the algorithm in the paper referred
-- to above can detect that the functions terminate. Here @perms@
-- contains one permutation (lexicographic ordering) for every
-- function; these permutations witness the termination of the
-- functions. (For more details, see the paper and 'lexOrder'.)
--
-- If termination can not be established, then @'Left' problems@ is
-- returned instead. Here @problems@ contains, for every function, an
-- indication of why termination cannot be established. See 'lexOrder'
-- for further details.
--
-- Note that this function assumes that all data types are strictly
-- positive.

terminates :: (Ord meta, Monoid meta) =>
  CallGraph meta -> Either meta
                           ()
terminates cs = let ccs = complete cs
                in
                  checkIdems $ toList ccs

checkIdems :: (Ord meta,Monoid meta) =>
  [(Call,meta)] -> Either meta
                           ()
checkIdems [] = Right ()
checkIdems ((c,m):xs) = if (checkIdem c) then checkIdems xs else Left m

checkIdem :: Call -> Bool
checkIdem c = let b = target c == source c
                  idem = (c >*< c) == c
                  hasDecr = any isDecr $ Array.elems $ diagonal (mat (cm c))
                  in
                    (not b) || (not idem) || hasDecr

-- matrix is decreasing if any diagonal element is Lt
isDecr :: Order -> Bool
isDecr Lt = True
isDecr (Mat m) = any isDecr $ Array.elems $ diagonal m
isDecr _ = False

-- | Completes the call graph and computes the corresponding recursion
-- behaviours.
--
-- Takes the same kind of input as 'terminates'.
--
-- For every function ('Index') a bunch of arrays is returned. Every
-- array states one way in which the function calls itself (perhaps
-- via other functions); one call path. The merged meta information
-- associated with all the calls in such a call path is paired up with
-- the array. It may be that several different call paths give rise to
-- the same array. In that case the array is returned once; the pieces
-- of meta information associated to the different call paths are
-- merged using 'mappend'.

recursionBehaviours :: (Ord meta, Monoid meta) =>
     CallGraph meta -> [(Index, [(meta, Array Index Order)])]
recursionBehaviours cs = rbs'
  where
  -- Complete the call graph.
  ccs = complete cs
  -- Compute the "recursion behaviours" (matrix diagonals).
  rbs = [ (source c, (callIds, diagonal (mat (cm c))))
        | (c, callIds) <- toList ccs, source c == target c ]
  -- Group them by function name.
  rbs' = map (fst . head &&& map snd) $ groupOn fst rbs

------------------------------------------------------------------------
-- Some examples

-- | The call graph instantiation used by the examples below.

type CG = CallGraph (Set Integer)

-- | Constructs a call graph suitable for use with the 'R' monoid.

buildCallGraph :: [Call] -> CG
buildCallGraph = fromList . flip zip (map Set.singleton [1 ..])
