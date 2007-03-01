{-# OPTIONS -cpp #-}

module TypeChecking.Patterns.Match where

import Control.Monad
import Data.Monoid

import Syntax.Common
import Syntax.Internal
import Syntax.Literal

import TypeChecking.Reduce
import TypeChecking.Monad
import TypeChecking.Monad.Builtin
import TypeChecking.Primitive

import Utils.Monad

#include "../../undefined.h"

-- | If matching is inconclusive (@DontKnow@) we want to know whether
--   it is due to a particular meta variable.
data Match = Yes [Term] | No | DontKnow (Maybe MetaId)

instance Monoid Match where
    mempty = Yes []

    Yes us     `mappend` Yes vs		  = Yes (us ++ vs)
    Yes _      `mappend` No		  = No
    Yes _      `mappend` DontKnow m	  = DontKnow m
    No	       `mappend` _		  = No

    -- Nothing means blocked by a variable.  In this case no instantiation of
    -- meta-variables will make progress.
    DontKnow _ `mappend` DontKnow Nothing = DontKnow Nothing

    -- One could imagine DontKnow _ `mappend` No = No, but would break the
    -- equivalence to case-trees.
    DontKnow m `mappend` _		  = DontKnow m

matchPatterns :: MonadTCM tcm => [Arg Pattern] -> [Arg Term] -> [Injective] -> tcm (Match, [Arg Term])
matchPatterns ps vs injs =
    do	(ms,vs) <- unzip <$> zipWithM (uncurry matchPattern)
				(zip (ps ++ repeat __IMPOSSIBLE__) injs)
				vs  -- ps and vs should have the same length
	return (mconcat ms, vs)
  where
    injs' = injs ++ repeat Injective

matchPattern :: MonadTCM tcm => Arg Pattern -> Injective -> Arg Term -> tcm (Match, Arg Term)
matchPattern (Arg _   AbsurdP)	  i arg		  = return (DontKnow Nothing, arg)
matchPattern (Arg h' (VarP _))	  i arg@(Arg _ v) = return (Yes [v], arg)
matchPattern (Arg _   WildP)	  i arg		  = return (Yes [], arg)
matchPattern (Arg h' (LitP l))	  i arg@(Arg h v) = do
    v <- reduce v
    case v of
	Lit l'
	    | l == l'	-> return (Yes [], Arg h v)
	    | otherwise	-> return (No, Arg h v)
	MetaV x _	-> return (DontKnow $ Just x, Arg h v)
	BlockedV b	-> return (DontKnow $ Just $ blockingMeta b, Arg h v)
	_		-> return (DontKnow Nothing, Arg h v)
matchPattern (Arg h' (ConP c ps)) i (Arg h v) =
    do	v <- constructorForm =<< reduce v
	case v of
	    Con c' vs
		| c == c'   -> do
		    let (pars, args) = splitAt npars vs
		    (m, vs) <- matchPatterns ps args (repeat i)
		    return (m, Arg h $ Con c' (pars ++ vs))
		| otherwise -> return (No, Arg h v)
		where
		    npars = length vs - length ps
	    MetaV x vs -> return (DontKnow bm, Arg h v)
	      where
		bm = case i of
		  Injective	-> Nothing    -- metas at injective positions aren't blocking
		  NotInjective	-> Just x
	    BlockedV b -> return (DontKnow $ Just $ blockingMeta b, Arg h v)
	    _	       -> return (DontKnow Nothing, Arg h v)

