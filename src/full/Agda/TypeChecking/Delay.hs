------------------------------------------------------------------------
-- | Functions for making things delayed
------------------------------------------------------------------------

module Agda.TypeChecking.Delay where

import Data.Traversable as Trav

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad

import Agda.Utils.Monad

class Undelay a where
  undelay :: MonadTCM tcm => Bool -> a -> tcm a
  -- ^ @undelay x@ sets the 'isUndelayed' field of every subexpression
  -- of type @'Undelay' something@ in @x@ to 'False', with the exception
  -- that it does not descend under coinductive constructors.

  -- TODO: What if a Def can reduce to a coinductive constructor
  -- application (after being undelayed)?

instance Undelay Term where
  undelay t = case t of
    Var i args   -> Var i <$> undelay args
    Lam h t      -> Lam h <$> undelay t
    Lit _	 -> return t
    Def f args   -> Def <$> undelay f <*> undelay args
    Con c args   -> Con c <$> do
      ind <- whatInduction c
      case ind of
        Inductive   -> undelay args
        CoInductive -> return args
    Pi s t	 -> Pi  <$> undelay s <*> undelay t
    Fun s t      -> Fun <$> undelay s <*> undelay t
    Sort _       -> return t
    MetaV x args -> MetaV x <$> undelay args

    -- TODO: How should meta-variables be handled? Undelaying/undelaying
    -- arguments seems wrong (meta might correspond to constructor).
    -- And what if the meta gets instantiated to something containing
    -- a delayed name?

instance Undelay Type where
  undelay (El s t) = El s <$> undelay t

instance Undelay QName where
  undelay = return

instance Undelay a => Undelay (Undelayed a) where
  undelay x = Delayed False <$> undelay (force x)

instance Undelay a => Undelay (Abs a) where
  undelay = Trav.mapM undelay

instance Undelay a => Undelay (Arg a) where
  undelay = Trav.mapM undelay

instance Undelay a => Undelay [a] where
  undelay = Trav.mapM undelay
