{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{- |  Non-linear matching of the lhs of a rewrite rule against a
      neutral term.

Given a lhs

  Δ ⊢ lhs : B

and a candidate term

  Γ ⊢ t : A

we seek a substitution Γ ⊢ σ : Δ such that

  Γ ⊢ B[σ] = A   and
  Γ ⊢ lhs[σ] = t : A

-}

module Agda.TypeChecking.Rewriting.NonLinMatch where

import Control.Monad.Trans.Maybe
import Control.Monad.Writer

import Data.Functor
import Data.Traversable
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Agda.Syntax.Common (unArg)
import Agda.Syntax.Internal

import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce

import Agda.Utils.Monad
import Agda.Utils.Singleton

#include "undefined.h"
import Agda.Utils.Impossible

-- | Non-linear (non-constructor) first-order pattern.
data NLPat
  = PVar {-# UNPACK #-} !Int
    -- ^ Matches anything (modulo non-linearity).
  | PWild
    -- ^ Matches anything (e.g. irrelevant terms).
  | PDef QName PElims
    -- ^ Matches @f es@
  | PTerm Term
    -- ^ Matches the term modulo β (ideally βη).
type PElims = [Elim' NLPat]

-- | Turn a term into a non-linear pattern, treating the
--   free variables as pattern variables.

class PatternFrom a b where
  patternFrom :: a -> ReduceM b

instance (Traversable f, PatternFrom a b) => PatternFrom (f a) (f b) where
  patternFrom = traverse patternFrom

instance PatternFrom Term NLPat where
  patternFrom v = do
    v <- etaContract =<< reduce' v
    let done = return $ PTerm v
    case ignoreSharing v of
      Var i [] -> return $ PVar i
      Var{}    -> done
      Lam{}    -> done
      Lit{}    -> done
      Def f es -> PDef f <$> patternFrom es
      Con c vs -> PDef (conName c) <$> patternFrom (Apply <$> vs)
      Pi{}     -> done
      Sort{}   -> done
      Level{}  -> done  -- TODO: unLevel and continue
                        -- requires to refactor unLevel into ReduceM
                        -- should be possible, as the level primitives
                        -- can be assumed to be defined.
      DontCare{} -> return PWild
      MetaV{}    -> __IMPOSSIBLE__
      Shared{}   -> __IMPOSSIBLE__
      ExtLam{}   -> __IMPOSSIBLE__

-- | Non-linear matching returns first an ambiguous substitution,
--   mapping one de Bruijn index to possibly several terms.
newtype AmbSubst = AmbSubst { ambSubst :: IntMap [Term] }

instance Monoid AmbSubst where
  mempty                          = AmbSubst mempty
  AmbSubst m `mappend` AmbSubst n = AmbSubst $ IntMap.unionWith (++) m n

instance Singleton (Int,Term) AmbSubst where
  singleton (i, v) = AmbSubst $ IntMap.singleton i [v]

-- sgSubst :: Int -> Term -> AmbSubst
-- sgSubst i v = AmbSubst $ IntMap.singleton i [v]

-- | Monad for non-linear matching.
type NLM = MaybeT (WriterT NLMOut ReduceM)

type NLMOut = (AmbSubst, PostponedEquations)

type PostponedEquations = [(Term, Term)]

liftRed :: ReduceM a -> NLM a
liftRed = lift . lift

-- | Match a non-linear pattern against a neutral term,
--   returning a substitution.

class AmbMatch a b where
  ambMatch :: a -> b -> NLM ()

instance AmbMatch a b => AmbMatch [a] [b] where
  ambMatch ps vs
    | length ps == length vs = zipWithM_ ambMatch ps vs
    | otherwise              = mzero

instance AmbMatch a b => AmbMatch (Arg a) (Arg b) where
  ambMatch p v = ambMatch (unArg p) (unArg v)

instance AmbMatch a b => AmbMatch (Elim' a) (Elim' b) where
  ambMatch p v =
   case (p, v) of
     (Apply p, Apply v) -> ambMatch p v
     (Proj x , Proj y ) -> unless (x == y) mzero
     (Apply{}, Proj{} ) -> __IMPOSSIBLE__
     (Proj{} , Apply{}) -> __IMPOSSIBLE__

instance AmbMatch NLPat Term where
  ambMatch p v = do
    let yes = return ()
        no  = mzero
    case p of
      PWild  -> yes
      PVar i -> tell (singleton (i, v), mempty)
      PDef f ps -> do
        v <- liftRed $ etaContract =<< reduce' v
        case ignoreSharing v of
          Def f' es
            | f == f'   -> ambMatch ps es
            | otherwise -> no
          Con c vs
            | f == conName c -> ambMatch ps (Apply <$> vs)
            | otherwise -> no
          _ -> no
      PTerm u -> tell (mempty, singleton (u,v))

-- | Untyped βη-equality, does not handle things like empty record types.
equal :: Term -> Term -> ReduceM Bool
equal u v = do
  (u, v) <- etaContract =<< normalise' (u, v)
  return $ u == v

