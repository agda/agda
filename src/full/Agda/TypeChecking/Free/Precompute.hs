{-# LANGUAGE TypeFamilies #-}
-- | Precompute free variables in a term (and store in 'ArgInfo').
module Agda.TypeChecking.Free.Precompute
  ( PrecomputeFreeVars, precomputeFreeVars
  , precomputedFreeVars, precomputeFreeVars_ ) where

import Control.Monad.Writer
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Traversable (Traversable, traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal



type FV = Writer IntSet

precomputeFreeVars_ :: PrecomputeFreeVars a => a -> a
precomputeFreeVars_ = fst . runWriter . precomputeFreeVars

precomputedFreeVars :: PrecomputeFreeVars a => a -> IntSet
precomputedFreeVars = snd . runWriter . precomputeFreeVars

class PrecomputeFreeVars a where
  precomputeFreeVars :: a -> FV a

  default precomputeFreeVars :: (Traversable c, PrecomputeFreeVars x, a ~ c x) => a -> FV a
  precomputeFreeVars = traverse precomputeFreeVars

-- The instances where things actually happen: Arg, Abs and Term.

maybePrecomputed :: PrecomputeFreeVars a => ArgInfo -> a -> FV (ArgInfo, a)
maybePrecomputed i x =
  case getFreeVariables i of
    KnownFVs fv -> (i, x) <$ tell fv
    UnknownFVs -> do
      (x', fv) <- listen $ precomputeFreeVars x
      return (setFreeVariables (KnownFVs fv) i, x')

instance PrecomputeFreeVars a => PrecomputeFreeVars (Arg a) where
  precomputeFreeVars arg@(Arg i x) = uncurry Arg <$> maybePrecomputed i x

-- Note that we don't store free variables in the Dom. The reason is that the
-- ArgInfo in the Dom tends to get reused during type checking for the argument
-- of that domain type, and it would be tedious and error prone to ensure that
-- we don't accidentally inherit also the free variables. Moreover we don't
-- really need the free variables of the Dom.
instance PrecomputeFreeVars a => PrecomputeFreeVars (Dom a) where

instance PrecomputeFreeVars a => PrecomputeFreeVars (Abs a) where
  precomputeFreeVars (NoAbs x b) = NoAbs x <$> precomputeFreeVars b
  precomputeFreeVars (Abs x b) =
    censor (IntSet.map (subtract 1) . IntSet.delete 0) $
      Abs x <$> precomputeFreeVars b

instance PrecomputeFreeVars Term where
  precomputeFreeVars t =
    case t of
      Var x es -> do
        tell (IntSet.singleton x)
        Var x <$> precomputeFreeVars es
      Lam i b    -> Lam i      <$> precomputeFreeVars b
      Lit{}      -> pure t
      Def f es   -> Def f      <$> precomputeFreeVars es
      Con c i es -> Con c i    <$> precomputeFreeVars es
      Pi a b     -> uncurry Pi <$> precomputeFreeVars (a, b)
      Sort s     -> Sort       <$> precomputeFreeVars s
      Level l    -> Level      <$> precomputeFreeVars l
      MetaV x es -> MetaV x    <$> precomputeFreeVars es
      DontCare t -> DontCare   <$> precomputeFreeVars t
      Dummy{}    -> pure t

-- The other instances are boilerplate.

instance PrecomputeFreeVars Sort where
  precomputeFreeVars s =
    case s of
      Type a     -> Type <$> precomputeFreeVars a
      Prop a     -> Prop <$> precomputeFreeVars a
      Inf        -> pure s
      SizeUniv   -> pure s
      PiSort a s -> uncurry PiSort <$> precomputeFreeVars (a, s)
      UnivSort s -> UnivSort <$> precomputeFreeVars s
      MetaS x es -> MetaS x <$> precomputeFreeVars es
      DefS d es  -> DefS d <$> precomputeFreeVars es
      DummyS{}   -> pure s

instance PrecomputeFreeVars Level where
  precomputeFreeVars (Max n ls) = Max n <$> precomputeFreeVars ls

instance PrecomputeFreeVars PlusLevel where
  precomputeFreeVars (Plus n l) = Plus n <$> precomputeFreeVars l

instance PrecomputeFreeVars LevelAtom where
  precomputeFreeVars l =
    case l of
      MetaLevel x es   -> MetaLevel x <$> precomputeFreeVars es
      BlockedLevel x t -> BlockedLevel x <$> precomputeFreeVars t
      NeutralLevel b t -> NeutralLevel b <$> precomputeFreeVars t
      UnreducedLevel t -> UnreducedLevel <$> precomputeFreeVars t

instance PrecomputeFreeVars Type where
  precomputeFreeVars (El s t) = uncurry El <$> precomputeFreeVars (s, t)

-- Note: don't use default instance, since that bypasses the 'Arg' in 'Apply'.
instance PrecomputeFreeVars a => PrecomputeFreeVars (Elim' a) where
  precomputeFreeVars e =
    case e of
      Apply x      -> Apply <$> precomputeFreeVars x
      IApply a x y -> IApply <$> precomputeFreeVars a <*> precomputeFreeVars x <*> precomputeFreeVars y
      Proj{}       -> pure e

-- The very boilerplate instances

instance PrecomputeFreeVars a => PrecomputeFreeVars [a] where
instance PrecomputeFreeVars a => PrecomputeFreeVars (Maybe a) where

instance (PrecomputeFreeVars a, PrecomputeFreeVars b) => PrecomputeFreeVars (a, b) where
  precomputeFreeVars (x, y) = (,) <$> precomputeFreeVars x <*> precomputeFreeVars y
