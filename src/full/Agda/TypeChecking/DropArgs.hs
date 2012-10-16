{-# LANGUAGE CPP, PatternGuards, TypeSynonymInstances, FlexibleInstances #-}
module Agda.TypeChecking.DropArgs where

import Agda.Syntax.Internal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

import Agda.TypeChecking.CompiledClause
-- import Agda.TypeChecking.CompiledClause.Compile

import Agda.Utils.Permutation


#include "../undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Dropping initial arguments to create a projection-like function
---------------------------------------------------------------------------

-- | When making a function projection-like, we drop the first @n@
--   arguments.
class DropArgs a where
  dropArgs :: Int -> a -> a

-- | NOTE: This creates telescopes with unbound de Bruijn indices.
instance DropArgs Telescope where
  dropArgs n tel = telFromList $ drop n $ telToList tel

instance DropArgs Permutation where
  dropArgs n (Perm m p) = Perm (m - n) $ map (subtract n) $ drop n p

-- | NOTE: does not go into the body, so does not work for recursive functions.
instance DropArgs ClauseBody where
  dropArgs 0 b        = b
  dropArgs _ NoBody   = NoBody
  dropArgs n (Bind b) = dropArgs (n - 1) (absBody b)
  dropArgs n Body{}   = __IMPOSSIBLE__

-- | NOTE: does not work for recursive functions.
instance DropArgs Clause where
  dropArgs n cl =
      cl{ clausePerm = dropArgs n $ clausePerm cl
        , clauseTel  = dropArgs n $ clauseTel cl
          -- Andreas, 2012-09-25: just dropping the front of telescope
          -- makes it ill-formed (unbound indices)
          -- we should let the telescope intact!?
        , clausePats = drop n $ clausePats cl
        , clauseBody = dropArgs n $ clauseBody cl -- BUG: need to drop also from recursive calls!!
        }

instance DropArgs FunctionInverse where
  dropArgs n finv = fmap (dropArgs n) finv

{- UNUSED, but don't remove (Andreas, 2012-10-08)
-- | Use for dropping initial lambdas in compiled clause bodies.
--   NOTE: does not reduce term, need lambdas to be present.
instance DropArgs Term where
  dropArgs 0 v = v
  dropArgs n v = case ignoreSharing v of
    Lam h b -> dropArgs (n - 1) (absBody b)
    _       -> __IMPOSSIBLE__
-}

-- | To drop the first @n@ arguments in a compiled clause,
--   we reduce the split argument indices by @n@ and
--   drop @n@ arguments from the bodies.
--   NOTE: this only works for non-recursive functions, we
--   are not dropping arguments to recursive calls in bodies.
instance DropArgs CompiledClauses where
  dropArgs n cc = case cc of
    Case i br | i < n         -> __IMPOSSIBLE__
              | otherwise     -> Case (i - n) $ fmap (dropArgs n) br
    Done xs t | length xs < n -> __IMPOSSIBLE__
              | otherwise     -> Done (drop n xs) t
    Fail                      -> Fail

