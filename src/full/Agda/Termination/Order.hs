{-# LANGUAGE CPP               #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams    #-}

#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
#endif

-- | An Abstract domain of relative sizes, i.e., differences
--   between size of formal function parameter and function argument
--   in recursive call; used in the termination checker.

module Agda.Termination.Order
  ( -- * Structural orderings
    Order(Mat), decr
  , increase, decrease
  , (.*.)
  , supremum, infimum
  , orderSemiring
  , le, lt, unknown, orderMat, collapseO
  , nonIncreasing, decreasing, isDecr
  , NotWorse(..)
  , tests
  ) where

import qualified Data.Foldable as Fold
import Data.List as List hiding (union, insert)

import Agda.Termination.CutOff
import Agda.Termination.SparseMatrix as Matrix hiding (tests)
import Agda.Termination.Semiring (HasZero(..), Semiring)
import qualified Agda.Termination.Semiring as Semiring

import Agda.Utils.PartialOrd hiding (tests)
import Agda.Utils.Pretty
import Agda.Utils.QuickCheck
import Agda.Utils.TestHelpers

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Structural orderings

-- | In the paper referred to above, there is an order R with
-- @'Unknown' '<=' 'Le' '<=' 'Lt'@.
--
-- This is generalized to @'Unknown' '<=' 'Decr k'@ where
-- @Decr 1@ replaces @Lt@ and @Decr 0@ replaces @Le@.
-- A negative decrease means an increase.  The generalization
-- allows the termination checker to record an increase by 1 which
-- can be compensated by a following decrease by 2 which results in
-- an overall decrease.
--
-- However, the termination checker of the paper itself terminates because
-- there are only finitely many different call-matrices.  To maintain
-- termination of the terminator we set a @cutoff@ point which determines
-- how high the termination checker can count.  This value should be
-- set by a global or file-wise option.
--
-- See 'Call' for more information.
--
-- TODO: document orders which are call-matrices themselves.
data Order
  = Decr {-# UNPACK #-} !Int
    -- ^ Decrease of callee argument wrt. caller parameter.
  | Unknown
    -- ^ No relation, infinite increase, or increase beyond termination depth.
  | Mat {-# UNPACK #-} !(Matrix Int Order)
    -- ^ Matrix-shaped order, currently UNUSED.
  deriving (Eq,Ord)

instance Show Order where
  show (Decr k) = show (- k)
  show Unknown  = "."
  show (Mat m)  = "Mat " ++ show m

instance HasZero Order where
  zeroElement = Unknown

-- | Information order: 'Unknown' is least information.
--   The more we decrease, the more information we have.
--
--   When having comparable call-matrices, we keep the lesser one.
--   Call graph completion works toward losing the good calls,
--   tending towards Unknown (the least information).
instance PartialOrd Order where
  comparable o o' = case (o, o') of
    (Unknown, Unknown) -> POEQ
    (Unknown, _      ) -> POLT
    (_      , Unknown) -> POGT
    (Decr k , Decr l ) -> comparableOrd k l
    -- Matrix-shaped orders are no longer supported
    (Mat{}  , _      ) -> __IMPOSSIBLE__
    (_      , Mat{}  ) -> __IMPOSSIBLE__

-- | A partial order, aimed at deciding whether a call graph gets
--   worse during the completion.
--
class NotWorse a where
  notWorse :: a -> a -> Bool

-- | It does not get worse then ``increase''.
--   If we are still decreasing, it can get worse: less decreasing.
instance NotWorse Order where
  o       `notWorse` Unknown = True            -- we are unboundedly increasing
  Unknown `notWorse` Decr k = k < 0            -- we are increasing
  Decr l  `notWorse` Decr k = k < 0 || l >= k  -- we are increasing or
                                               -- we are decreasing, but more
  -- Matrix-shaped orders are no longer supported
  Mat m   `notWorse` o       = __IMPOSSIBLE__
  o       `notWorse` Mat m   = __IMPOSSIBLE__
{-
  Mat m   `notWorse` Mat n   = m `notWorse` n  -- matrices are compared pointwise
  o       `notWorse` Mat n   = o `notWorse` collapse n  -- or collapsed (sound?)
  Mat m   `notWorse` o       = collapse m `notWorse` o
-}

-- | We assume the matrices have the same dimension.
instance (Ord i) => NotWorse (Matrix i Order) where
  m `notWorse` n
    | size m /= size n = __IMPOSSIBLE__
    | otherwise        = Fold.all isTrue $
                           zipMatrices onlym onlyn both trivial m n
    where
      -- If an element is only in @m@, then its 'Unknown' in @n@
      -- so it gotten better at best, in any case, not worse.
      onlym o = True     -- @== o `notWorse` Unknown@
      onlyn o = Unknown `notWorse` o
      both    = notWorse
      isTrue  = id
      trivial = id

-- | Raw increase which does not cut off.
increase :: Int -> Order -> Order
increase i o = case o of
  Unknown -> Unknown
  Decr k  -> Decr $ k - i
  Mat m   -> Mat $ fmap (increase i) m

-- | Raw decrease which does not cut off.
decrease :: Int -> Order -> Order
decrease i o = increase (-i) o

-- | Smart constructor for @Decr k :: Order@ which cuts off too big values.
--
-- Possible values for @k@: @- ?cutoff '<=' k '<=' ?cutoff + 1@.
--
decr :: (?cutoff :: CutOff) => Int -> Order
decr k = case ?cutoff of
  CutOff c | k < -c -> Unknown
           | k > c  -> Decr $ c + 1
  _                 -> Decr k

-- | Smart constructor for matrix shaped orders, avoiding empty and singleton matrices.
orderMat :: Matrix Int Order -> Order
orderMat m | Matrix.isEmpty m  = Decr 0                -- 0x0 Matrix = neutral element
           | otherwise         = case isSingleton m of
                                   Just o -> o         -- 1x1 Matrix
                                   Nothing -> Mat m    -- nxn Matrix

withinCutOff :: (?cutoff :: CutOff) => Int -> Bool
withinCutOff k = case ?cutoff of
  DontCutOff -> True
  CutOff c   -> k >= -c && k <= c + 1

isOrder :: (?cutoff :: CutOff) => Order -> Bool
isOrder (Decr k) = withinCutOff k
isOrder Unknown = True
isOrder (Mat m) = False  -- TODO: extend to matrices

prop_decr :: (?cutoff :: CutOff) => Int -> Bool
prop_decr = isOrder . decr

-- | @le@, @lt@, @decreasing@, @unknown@: for backwards compatibility, and for external use.
le :: Order
le = Decr 0

lt :: Order
lt = Decr 1

unknown :: Order
unknown = Unknown

nonIncreasing :: Order -> Bool
nonIncreasing (Decr k) = k >= 0
nonIncreasing _        = False

decreasing :: Order -> Bool
decreasing (Decr k) = k > 0
decreasing _        = False

-- | Matrix-shaped order is decreasing if any diagonal element is decreasing.
isDecr :: Order -> Bool
isDecr (Mat m) = any isDecr $ diagonal m
isDecr o = decreasing o

instance Pretty Order where
  pretty (Decr 0) = text "="
  pretty (Decr k) = text $ show (0 - k)
  pretty Unknown  = text "?"
  pretty (Mat m)  = text "Mat" <+> pretty m

--instance Ord Order where
--    max = maxO

{- instances cannot have implicit arguments?! GHC manual says:

7.8.3.1. Implicit-parameter type constraints

You can't have an implicit parameter in the context of a class or instance declaration. For example, both these declarations are illegal:

  class (?x::Int) => C a where ...
  instance (?x::a) => Foo [a] where ...

Reason: exactly which implicit parameter you pick up depends on
exactly where you invoke a function. But the ``invocation'' of
instance declarations is done behind the scenes by the compiler, so
it's hard to figure out exactly where it is done. Easiest thing is to
outlaw the offending types.

instance (?cutoff :: CutOff) => Arbitrary Order where
  arbitrary = frequency
    [(20, return Unknown)
    ,(80, elements [- ?cutoff .. ?cutoff + 1] >>= Decr)
    ] -- no embedded matrices generated for now.
-}
instance Arbitrary Order where
  arbitrary = frequency
    [(30, return Unknown)
    ,(70, elements [0,1] >>= return . Decr)
    ] -- no embedded matrices generated for now.

instance CoArbitrary Order where
  coarbitrary (Decr k) = variant 0
  coarbitrary Unknown  = variant 1
  coarbitrary (Mat m)  = variant 2

-- | Multiplication of 'Order's. (Corresponds to sequential
-- composition.)

-- I think this funny pattern matching is because overlapping patterns
-- are producing a warning and thus an error (strict compilation settings)
(.*.) :: (?cutoff :: CutOff) => Order -> Order -> Order
Unknown  .*. _         = Unknown
(Mat m)  .*. Unknown   = Unknown
(Decr k) .*. Unknown   = Unknown
(Decr k) .*. (Decr l)  = decr (k + l)
(Decr 0) .*. (Mat m)   = Mat m
(Decr k) .*. (Mat m)   = (Decr k) .*. (collapse m)
(Mat m1) .*. (Mat m2) = if (okM m1 m2) then
                            Mat $ mul orderSemiring m1 m2
                        else
                            (collapse m1) .*. (collapse m2)
(Mat m) .*. (Decr 0)  = Mat m
(Mat m) .*. (Decr k)  = (collapse m) .*. (Decr k)

{- collapse m

We assume that m codes a permutation:  each row has at most one column
that is not Un.

To collapse a matrix into a single value, we take the best value of
each column and multiply them.  That means if one column is all Un,
i.e., no argument relates to that parameter, than the collapsed value
is also Un.

This makes order multiplication associative.

-}
collapse :: (?cutoff :: CutOff) => Matrix Int Order -> Order
collapse m = -- if not $ Matrix.matrixInvariant m then __IMPOSSIBLE__ else
  case toLists $ Matrix.transpose m of
   [] -> __IMPOSSIBLE__   -- This can never happen if order matrices are generated by the smart constructor
   m' -> foldl1 (.*.) $ map (foldl1 maxO) m'

{- OLD CODE, does not give associative matrix multiplication:
collapse :: (?cutoff :: CutOff) => Matrix Int Order -> Order
collapse m = foldl (.*.) le (Data.Array.elems $ diagonal m)
-}

collapseO :: (?cutoff :: CutOff) => Order -> Order
collapseO (Mat m) = collapse m
collapseO o       = o

okM :: Matrix Int Order -> Matrix Int Order -> Bool
okM m1 m2 = (rows $ size m2) == (cols $ size m1)

-- | The supremum of a (possibly empty) list of 'Order's.
--   More information (i.e., more decrease) is bigger.
--   'Unknown' is no information, thus, smallest.
supremum :: (?cutoff :: CutOff) => [Order] -> Order
supremum = foldr maxO Unknown

-- | @('Order', 'maxO', '.*.')@ forms a semiring, with 'Unknown' as
-- zero and 'Le' as one.

maxO :: (?cutoff :: CutOff) => Order -> Order -> Order
maxO o1 o2 = case (o1,o2) of
               (Decr k, Decr l) -> Decr (max k l) -- cut off not needed, within borders
               (Unknown,_) -> o2
               (_,Unknown) -> o1
               (Mat m1, Mat m2) -> Mat (Matrix.add maxO m1 m2)
               (Mat m,_) -> maxO (collapse m) o2
               (_,Mat m) ->  maxO o1 (collapse m)

-- | The infimum of a (non empty) list of 'Order's.
--  'Unknown' is the least element, thus, dominant.
infimum :: (?cutoff :: CutOff) => [Order] -> Order
infimum (o:l) = foldl' minO o l
infimum []    = __IMPOSSIBLE__

minO :: (?cutoff :: CutOff) => Order -> Order -> Order
minO o1 o2 = case (o1,o2) of
               (Unknown,_) -> Unknown
               (_,Unknown) -> Unknown
               (Decr k, Decr l) -> Decr (min k l) -- cut off not needed, within borders
               (Mat m1, Mat m2) -> if (size m1 == size m2) then
                                       Mat $ Matrix.intersectWith minO m1 m2
                                   else
                                       minO (collapse m1) (collapse m2)
               (Mat m1,_) -> minO (collapse m1) o2
               (_,Mat m2) -> minO o1 (collapse m2)


{- Cannot have implicit arguments in instances.  Too bad!

instance Monoid Order where
  mempty = Unknown
  mappend = maxO

instance (cutoff :: Int) => SemiRing Order where
  multiply = (.*.)
-}

orderSemiring :: (?cutoff :: CutOff) => Semiring Order
orderSemiring =
  Semiring.Semiring { Semiring.add = maxO
                    , Semiring.mul = (.*.)
                    , Semiring.zero = Unknown
--                    , Semiring.one = Le
                    }

prop_orderSemiring :: (?cutoff :: CutOff) => Order -> Order -> Order -> Bool
prop_orderSemiring = Semiring.semiringInvariant orderSemiring

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.Order"
  [ quickCheck' prop_decr
  , quickCheck' prop_orderSemiring
  ]
  where ?cutoff = DontCutOff -- CutOff 2  -- don't cut off in tests!
