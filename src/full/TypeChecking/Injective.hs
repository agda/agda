{-# OPTIONS_GHC -cpp #-}

{-|

  A term @t@ is injective in a variable @x@ if @t[u/x] = t[v/x]@ implies @u =
  v@.

-}
module TypeChecking.Injective (computeInjectivity) where

import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad.Base

#include "../undefined.h"

computeInjectivity :: MonadTCM tcm => Definition -> tcm Definition
computeInjectivity (Defn t fv def) = Defn t fv <$> injectiveDefn def

injectiveDefn :: MonadTCM tcm => Defn -> tcm Defn
injectiveDefn (Function cs _ a) = do
  is <- injectiveClauses cs
  return $ Function cs is a
injectiveDefn d			= return d

-- | Invariant: Non-empty list of clauses.
injectiveClauses :: MonadTCM tcm => [Clause] -> tcm [Injective]
injectiveClauses [] = __IMPOSSIBLE__
-- If there are multiple clauses we give up.
injectiveClauses (c:_:_) = return $ replicate (nofArgs c) NotInjective
injectiveClauses [Clause ps b] = do
  is <- injectiveBody b
  return $ reorganise (map unArg ps) is

injectiveBody :: MonadTCM tcm => ClauseBody -> tcm [Injective]
injectiveBody b = return $ repeat NotInjective

class Inj a where
  injective :: MonadTCM tcm => Int -> a -> tcm (Map Nat Injective)

instance Inj Term where
  injective n t = return Map.empty

instance Inj a => Inj (Abs a) where
  injective n b = Map.mapKeysMonotonic (subtract 1) . Map.delete 0
		  <$> injective (n + 1) (absBody b)

-- | Transform the injectivity of the pattern variables into the injectivity of
-- the arguments. An argument is injective if all its variables are injective.
reorganise :: [Pattern] -> [Injective] -> [Injective]
reorganise []	    _  = []
reorganise (p : ps) is = i : reorganise ps is1
  where
    (is0, is1) = splitAt (nofPatVars p) is
    i | all (== Injective) is0	= Injective
      | otherwise		= NotInjective

nofPatVars :: Pattern -> Int
nofPatVars p = case p of
  VarP _  -> 1
  ConP _ ps -> sum $ map (nofPatVars . unArg) ps
  LitP _    -> 0
  WildP	    -> 0
  AbsurdP   -> 0

nofArgs :: Clause -> Int
nofArgs (Clause ps _) = length ps

