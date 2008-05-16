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
import Utils.Impossible

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

matchPatterns :: MonadTCM tcm => [Arg Pattern] -> [Arg Term] -> tcm (Match, [Arg Term])
matchPatterns ps vs =
    do	(ms,vs) <- unzip <$> zipWithM' matchPattern ps vs
	return (mconcat ms, vs)

matchPattern :: MonadTCM tcm => Arg Pattern -> Arg Term -> tcm (Match, Arg Term)
matchPattern (Arg h' (VarP _))	  arg@(Arg _ v) = return (Yes [v], arg)
matchPattern (Arg _  (DotP _))    arg@(Arg _ v) = return (Yes [v], arg)
matchPattern (Arg h' (LitP l))	  arg@(Arg h v) = do
    v <- reduce v
    case v of
	Lit l'
	    | l == l'	-> return (Yes [], Arg h v)
	    | otherwise	-> return (No, Arg h v)
	MetaV x _	-> return (DontKnow $ Just x, Arg h v)
	BlockedV b	-> return (DontKnow $ Just $ blockingMeta b, Arg h v)
	_		-> return (DontKnow Nothing, Arg h v)
matchPattern (Arg h' (ConP c ps))     (Arg h v) =
    do	v <- constructorForm =<< reduce v
	case v of
	    Con c' vs
		| c == c'   -> do
		    (m, vs) <- matchPatterns ps vs
		    return (m, Arg h $ Con c' vs)
		| otherwise -> return (No, Arg h v)
	    MetaV x vs -> return (DontKnow $ Just x, Arg h v)
	    BlockedV b -> return (DontKnow $ Just $ blockingMeta b, Arg h v)
	    _	       -> return (DontKnow Nothing, Arg h v)

