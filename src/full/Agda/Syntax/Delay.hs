{-# LANGUAGE Rank2Types #-}

------------------------------------------------------------------------
-- | Functions for making things delayed
------------------------------------------------------------------------

module Agda.Syntax.Delay where

import Agda.Syntax.Common
import Agda.Syntax.Internal

type Delayer = forall a. a -> Delayed a

-- | Creates a 'Delayer' based on the top-most constructor.
delayer :: Delayed a -> Delayer
delayer (Delayed    x) =    Delayed
delayer (NotDelayed x) = NotDelayed

class Delay a where
  delay :: Delayer -> a -> a
  -- ^ Delays every subexpression of type @'Delay' something@ using
  -- the delayer.

-- | Delays the first argument if the second is delayed.
delayedIf :: Delay a => a -> Delayed b -> a
x `delayedIf` Delayed    _ = delay Delayed x
x `delayedIf` NotDelayed _ = x

-- | Delays the second argument if the first is 'CoInductive'.
delayedIfCoinductive :: Delay a => Induction -> a -> a
delayedIfCoinductive Inductive   = id
delayedIfCoinductive CoInductive = delay Delayed

instance Delay Term where
  delay d t = case t of
    Var i args   -> Var i (delay d args)
    Lam h t      -> Lam h (delay d t)
    Lit _	 -> t
    Def f args   -> Def (delay d f) (delay d args)
    Con c args   -> Con c (delay d args)
    Pi s t	 -> Pi  (delay d s) (delay d t)
    Fun s t      -> Fun (delay d s) (delay d t)
    Sort s       -> Sort (delay d s)
    MetaV x args -> MetaV (delay d x) (delay d args)

instance Delay Type where
  delay d (El s t) = El (delay d s) (delay d t)

instance Delay Sort where
  delay d s = case s of
    Type _  -> s
    Prop    -> s
    Lub s t -> Lub (delay d s) (delay d t)
    Suc s   -> Suc (delay d s)
    MetaS x -> MetaS (delay d x)

instance Delay Pattern where
  delay d p = case p of
    VarP _    -> p
    DotP t    -> DotP (delay d t)
    ConP x ps -> ConP x (delay d ps)
    LitP _    -> p

instance Delay MetaId where
  delay d i = i

instance Delay QName where
  delay d = id

instance Delay a => Delay (Delayed a) where
  delay d x = d (delay d (force x))

instance Delay a => Delay (Abs a) where
  delay d = fmap (delay d)

instance Delay a => Delay (Arg a) where
  delay d = fmap (delay d)

instance Delay a => Delay [a] where
  delay d = fmap (delay d)
