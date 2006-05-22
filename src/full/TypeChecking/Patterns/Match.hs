{-# OPTIONS -cpp #-}

module TypeChecking.Patterns.Match where

import Data.Monoid

import Syntax.Common
import Syntax.Internal

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

matchPatterns :: [Arg Pattern] -> [Arg Term] -> Match
matchPatterns ps vs = mconcat $ zipWith matchPattern
					(ps ++ repeat __IMPOSSIBLE__)
					vs

matchPattern :: Arg Pattern -> Arg Term -> Match
matchPattern (Arg _ p) (Arg _ v) =
    case (p, v) of
	(VarP _, v) -> Yes [v]
	(ConP c ps, Con c' vs)
	    | c == c'		-> matchPatterns ps (drop npars vs)
	    | otherwise		-> No
	    where
		npars = length vs - length ps
	(ConP c ps, MetaV x vs) -> DontKnow $ Just x
	(ConP _ _, BlockedV b)	-> DontKnow $ Just $ blockingMeta b
	(ConP _ _, _)		-> DontKnow Nothing

