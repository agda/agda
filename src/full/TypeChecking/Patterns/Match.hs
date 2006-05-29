{-# OPTIONS -cpp #-}

module TypeChecking.Patterns.Match where

import Control.Monad
import Data.Monoid

import Syntax.Common
import Syntax.Internal

import TypeChecking.Reduce
import TypeChecking.Monad

import Utils.Monad

#include "../../undefined.h"

-- | If matching is inconclusive (@DontKnow@) we want to know whether
--   it is due to a particular meta variable.
data Match = Yes [Term] | No | DontKnow (Maybe MetaId)

instance Monoid Match where
    mempty = Yes []

    Yes us     `mappend` Yes vs	    = Yes (us ++ vs)
    Yes _      `mappend` No	    = No
    Yes _      `mappend` DontKnow m = DontKnow m
    No	       `mappend` _	    = No
    DontKnow m `mappend` _	    = DontKnow m	-- sequential

matchPatterns :: [Arg Pattern] -> [Arg Term] -> TCM (Match, [Arg Term])
matchPatterns ps vs =
    do	(ms,vs) <- unzip <$> zipWithM matchPattern
				(ps ++ repeat __IMPOSSIBLE__) -- ps and vs should
				vs			      -- have the same length
	return (mconcat ms, vs)

matchPattern :: Arg Pattern -> Arg Term -> TCM (Match, Arg Term)
matchPattern (Arg h' p) (Arg h v) =
    do	v <- reduce v
	case (p, v) of
	    (AsP _ p, v) ->
		do  (m, arg) <- matchPattern (Arg h' p) (Arg h v)
		    return (m `mappend` Yes [v], arg)
	    (VarP _, v) -> return (Yes [v], Arg h v)
	    (ConP c ps, Con c' vs)
		| c == c'		->
		    do	(m, vs) <- matchPatterns ps (drop npars vs)
			return (m, Arg h $ Con c' vs)
		| otherwise		-> return (No, Arg h v)
		where
		    npars = length vs - length ps
	    (ConP c ps, MetaV x vs) -> return (DontKnow $ Just x, Arg h v)
	    (ConP _ _, BlockedV b)  -> return (DontKnow $ Just $ blockingMeta b, Arg h v)
	    (ConP _ _, _)	    -> return (DontKnow Nothing, Arg h v)

