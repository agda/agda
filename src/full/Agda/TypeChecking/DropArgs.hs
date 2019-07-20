
module Agda.TypeChecking.DropArgs where

import Control.Arrow (second)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Coverage.SplitTree

import Agda.Utils.Functor
import Agda.Utils.Permutation

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Dropping initial arguments to create a projection-like function
---------------------------------------------------------------------------

-- | When making a function projection-like, we drop the first @n@
--   arguments.
class DropArgs a where
  dropArgs :: Int -> a -> a

instance DropArgs a => DropArgs (Maybe a) where
  dropArgs n = fmap (dropArgs n)

-- | NOTE: This creates telescopes with unbound de Bruijn indices.
instance DropArgs Telescope where
  dropArgs n tel = telFromList $ drop n $ telToList tel

instance DropArgs Permutation where
  dropArgs n (Perm m p) = Perm (m - n) $ map (subtract n) $ drop n p

-- | NOTE: does not work for recursive functions.
instance DropArgs Clause where
  dropArgs n cl =
      cl{ -- Andreas, 2012-09-25: just dropping the front of telescope
          -- makes it ill-formed (unbound indices)
          -- we should let the telescope intact!?
          -- Ulf, 2016-06-23: Indeed. After parameter refinement it's even
          -- worse: the module parameters we want to drop aren't necessarily
          -- the first things in the telescope.
          namedClausePats = drop n $ namedClausePats cl
          -- BUG: need to drop also from recursive calls!!
        }

instance DropArgs FunctionInverse where
  dropArgs n finv = fmap (dropArgs n) finv

-- | Use for dropping initial lambdas in clause bodies.
--   NOTE: does not reduce term, need lambdas to be present.
instance DropArgs Term where
  dropArgs 0 v = v
  dropArgs n v = case v of
    Lam h b -> dropArgs (n - 1) (absBody b)
    _       -> __IMPOSSIBLE__

-- | To drop the first @n@ arguments in a compiled clause,
--   we reduce the split argument indices by @n@ and
--   drop @n@ arguments from the bodies.
--   NOTE: this only works for non-recursive functions, we
--   are not dropping arguments to recursive calls in bodies.
instance DropArgs CompiledClauses where
  dropArgs n cc = case cc of
    Case i br | unArg i < n   -> __IMPOSSIBLE__
              | otherwise     -> Case (i <&> \ j -> j - n) $ fmap (dropArgs n) br
    Done xs t | length xs < n -> __IMPOSSIBLE__
              | otherwise     -> Done (drop n xs) t
    Fail                      -> Fail

instance DropArgs SplitTree where
  dropArgs n (SplittingDone m) = SplittingDone (m - n)
  dropArgs n (SplitAt i ts)    = SplitAt (subtract n <$> i) $ map (second $ dropArgs n) ts

