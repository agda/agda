{-# LANGUAGE CPP #-}

module Agda.TypeChecking.UniversePolymorphism where

import Control.Applicative
import Control.Monad.Error
import Data.List

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Level
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Builtin
import qualified Agda.Utils.Warshall as W

import Agda.Utils.Impossible

#include "../undefined.h"

mlevel :: MonadTCM tcm => tcm (Maybe Term)
mlevel = liftTCM $ (Just <$> primLevel) `catchError` \_ -> return Nothing

compareLevel :: MonadTCM tcm => Comparison -> Term -> Term -> tcm Constraints
compareLevel cmp u v = do
  reportSDoc "tc.conv.level" 10 $ vcat
    [ text "Comparing levels"
    , nest 2 $ sep [ prettyTCM u <+> prettyTCM cmp
                   , prettyTCM v
                   ]
    ]
  u <- reduce u
  v <- reduce v
  reportSDoc "tc.conv.level" 15 $
      nest 2 $ sep [ text (show u) <+> prettyTCM cmp
                   , text (show v)
                   ]
  let unMax (Max [a]) = a
      unMax _         = __IMPOSSIBLE__
  l1' <- unMax <$> levelView u
  l2' <- unMax <$> levelView v

  let bad = typeError $ UnequalLevel cmp u v

  let c  = min (constant l1') (constant l2')
      l1 = minus l1 c
      l2 = minus l2 c

  case (cmp, l1, l2) of
    (cmp, ClosedLevel n, ClosedLevel m) ->
      case cmp of
        CmpEq  | n == m -> return []
        CmpLeq | n <= m -> return []
        _               -> bad
    (CmpLeq, ClosedLevel 0, _) -> return []
    _ -> buildConstraint $ LevelCmp cmp u v
  where
    constant (ClosedLevel n) = n
    constant (Plus n _)      = n

    minus (ClosedLevel n) m = ClosedLevel (n - m)
    minus (Plus n l) m      = Plus (n - m) l

isLevelConstraint LevelCmp{} = True
isLevelConstraint _          = False

warshallConstraint :: Constraint -> TCM [W.Constraint]
warshallConstraint (LevelCmp cmp a b) = do
  -- produce constraints
  return []
warshallConstraint _ = __IMPOSSIBLE__

solveLevelConstraints :: TCM ()
solveLevelConstraints = do
  cs <- takeConstraints
  let (lcs, rest) = partition (isLevelConstraint . clValue) cs

  lcs <- concat <$> mapM warshallConstraint (map clValue lcs)

  let msol = W.solve lcs

  case msol of
    Nothing  -> typeError $ GenericError "Bad universe levels! No further information provided. You suck!"
    Just sol -> do
      -- do something interesting with the solution
      addConstraints rest
      return ()

