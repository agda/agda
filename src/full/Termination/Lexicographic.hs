-- | Lexicographic order search, more or less as defined in
--      \"A Predicative Analysis of Structural Recursion\" by
--      Andreas Abel and Thorsten Altenkirch.

-- Note that this module can be optimised by using Data.Sequence
-- instead of ordinary lists. It is unclear if this is necessary,
-- though.

module Termination.Lexicographic
  ( LexOrder
  , RecBehaviour
  , lexOrder
  ) where

import Test.QuickCheck
import Termination.TestHelpers
import Termination.Utilities
import Termination.CallGraph
import Data.List
import Data.Maybe
import Control.Arrow

-- | A lexicographic ordering for the recursion behaviour of a
-- given function is a permutation of the argument indices which can
-- be used to show that the function terminates. See the paper
-- referred to above for more details.

type LexOrder = [Index]

-- | A recursion behaviour expresses how a certain function calls
-- itself (transitively). The outer list contains one element for
-- every (syntactic) recursive call. The @n@-th element in an inner
-- list expresses size changes in the @n@-th argument for a certain
-- recursive call.

type RecBehaviour = [[Order]]

-- | All the inner lists should have the same length.

recBehaviourInvariant :: RecBehaviour -> Bool
recBehaviourInvariant = allEqual . map length

-- | Generates a recursion behaviour.

recBehaviour :: Gen RecBehaviour
recBehaviour = do
  n <- natural :: Gen Integer
  list (listOfLength n arbitrary)

prop_recBehaviour = forAll recBehaviour recBehaviourInvariant

-- | Checks if this argument is well-behaved (all calls decreasing, at
-- least one strictly decreasing).

okArgument :: [Order] -> Bool
okArgument col = any ((==) Lt) col && all ((/=) Unknown) col

-- | Computes a new recursion behaviour by removing all rows for which
-- the @n@-th element is 'Lt', and also completely removing the @n@-th
-- column.

newBehaviour :: Index -> RecBehaviour -> RecBehaviour
newBehaviour n rb =
  catMaybes $
    map (\(o, os) -> if o == Lt then Nothing else Just os) $
      map (extractNthElement n) rb

-- | @'correctLexOrder' rs ps@ checks that the permutation @ps@ really
-- induces a lexicographic ordering which shows that the function
-- represented by the recursion behaviour @rs@ terminates.

correctLexOrder :: RecBehaviour -> LexOrder -> Bool
correctLexOrder []      []        = True
correctLexOrder (_ : _) []        = False
correctLexOrder rb      (p0 : ps) =
  okArgument (transpose rb `genericIndex` p0) &&
  correctLexOrder (newBehaviour p0 rb) ps'
  where
  ps' = map (\p -> if p < p0 then p else p - 1) ps

-- | Tries to compute a lexicographic ordering for the given recursion
-- behaviour. This algorithm should be complete.

lexOrder :: RecBehaviour -> Maybe LexOrder
lexOrder [] = Just []
lexOrder rb = case okArguments of
  []      -> Nothing
  (n : _) -> do
    ps <- lexOrder (newBehaviour n rb)
    return $ n : map (\p -> if p >= n then p + 1 else p) ps
  where
  okArguments = map fst $ filter snd $
                map (id *** okArgument) $
                zip [0 ..] (transpose rb)

prop_lexOrder =
  forAll recBehaviour $ \rb ->
    let mPerm = lexOrder rb
        Just perm = mPerm
    in
    mPerm /= Nothing ==>
      correctLexOrder rb perm

------------------------------------------------------------------------
-- All tests

tests = do
  quickCheck prop_recBehaviour
  quickCheck prop_lexOrder
