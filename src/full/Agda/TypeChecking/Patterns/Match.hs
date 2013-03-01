{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Patterns.Match where

import Control.Monad
import Data.Monoid
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Literal

import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Pretty

import Agda.Utils.Monad

#include "../../undefined.h"
import Agda.Utils.Impossible

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

matchPatterns :: [I.Arg Pattern] -> [I.Arg Term] -> TCM (Match, [I.Arg Term])
matchPatterns ps vs = do
    reportSDoc "tc.match" 50 $
      vcat [ text "matchPatterns"
           , nest 2 $ text "ps =" <+> fsep (punctuate comma $ map (text . show) ps)
           , nest 2 $ text "vs =" <+> fsep (punctuate comma $ map prettyTCM vs)
           ]

    (ms,vs) <- unzip <$> zipWithM' matchPattern ps vs
    return (mconcat ms, vs)

matchPattern :: I.Arg Pattern -> I.Arg Term -> TCM (Match, I.Arg Term)
matchPattern (Arg _  (VarP _)) arg@(Arg _ v) = return (Yes [v], arg)
matchPattern (Arg _  (DotP _)) arg@(Arg _ v) = return (Yes [v], arg)
matchPattern (Arg info' (LitP l)) arg@(Arg info v) = do
    w <- reduceB v
    let v = ignoreBlocking w
    case ignoreSharing <$> w of
	NotBlocked (Lit l')
	    | l == l'          -> return (Yes [], Arg info v)
	    | otherwise        -> return (No, Arg info v)
	NotBlocked (MetaV x _) -> return (DontKnow $ Just x, Arg info v)
	Blocked x _            -> return (DontKnow $ Just x, Arg info v)
	_                      -> return (DontKnow Nothing, Arg info v)

{- Andreas, 2012-04-02 NO LONGER UP-TO-DATE
matchPattern (Arg h' r' (ConP c _ ps))     (Arg h Irrelevant v) = do
          -- Andreas, 2010-09-07 matching a record constructor against
          -- something irrelevant will just continue matching against
          -- irrelevant stuff
		(m, vs) <- matchPatterns ps $
                  repeat $ Arg NotHidden Irrelevant $ DontCare __IMPOSSIBLE__
		return (m, Arg h Irrelevant $ Con c vs)
-}

matchPattern (Arg info' (ConP c _ ps))     (Arg info v) =
    do	w <- traverse constructorForm =<< reduceB v
        -- Unfold delayed (corecursive) definitions one step. This is
        -- only necessary if c is a coinductive constructor, but
        -- 1) it does not hurt to do it all the time, and
        -- 2) whatInduction c sometimes crashes because c may point to
        --    an axiom at this stage (if we are checking the
        --    projection functions for a record type).
        w <- case ignoreSharing <$> w of
               NotBlocked (Def f args) ->
                 unfoldDefinition True reduceB (Def f []) f args
                   -- reduceB is used here because some constructors
                   -- are actually definitions which need to be
                   -- unfolded (due to open public).
               _ -> return w
        let v = ignoreBlocking w
	case ignoreSharing <$> w of
          -- Andreas, 2010-09-07 matching a record constructor against
          -- something irrelevant will just continue matching against
          -- irrelevant stuff
          -- NotBlocked (Sort Prop)
          _  | isIrrelevant info -> do
		(m, vs) <- matchPatterns ps $
                  repeat $ setRelevance Irrelevant $ defaultArg $ Sort Prop
		return (m, Arg info $ Con c vs)
	  NotBlocked (Con c' vs)
	    | c == c'             -> do
		(m, vs) <- matchPatterns ps vs
		return (m, Arg info $ Con c' vs)
	    | otherwise           -> return (No, Arg info v)
	  NotBlocked (MetaV x vs) -> return (DontKnow $ Just x, Arg info v)
	  Blocked x _             -> return (DontKnow $ Just x, Arg info v)
          _                       -> return (DontKnow Nothing, Arg info v)
