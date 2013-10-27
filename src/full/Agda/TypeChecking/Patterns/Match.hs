{-# LANGUAGE CPP, DeriveFunctor #-}

module Agda.TypeChecking.Patterns.Match where

-- import Control.Monad
import Data.Monoid
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
-- import Agda.Syntax.Literal

-- import Agda.TypeChecking.Datatypes (getConHead)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad
-- import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Pretty

import Agda.Utils.Monad
import Agda.Utils.Tuple

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | If matching is inconclusive (@DontKnow@) we want to know whether
--   it is due to a particular meta variable.
data Match a = Yes Simplification [a] | No | DontKnow (Maybe MetaId)
  deriving (Functor)

instance Monoid (Match a) where
    mempty = Yes mempty []

    Yes s us   `mappend` Yes s' vs        = Yes (s `mappend` s') (us ++ vs)
    Yes _ _    `mappend` No               = No
    Yes _ _    `mappend` DontKnow m       = DontKnow m
    No	       `mappend` _                = No

    -- Nothing means blocked by a variable.  In this case no instantiation of
    -- meta-variables will make progress.
    DontKnow _ `mappend` DontKnow Nothing = DontKnow Nothing

    -- One could imagine DontKnow _ `mappend` No = No, but would break the
    -- equivalence to case-trees.
    DontKnow m `mappend` _		  = DontKnow m

-- | @matchCopatterns ps es@ matches spine @es@ against copattern spine @ps@.
--
--   Returns 'Yes' and a substitution for the pattern variables
--   (in form of [Term]) if matching was successful.
--
--   Returns 'No' if there was a constructor or projection mismatch.
--
--   Returns 'DontKnow' if an argument could not be evaluated to
--   constructor form because of a blocking meta variable.
--
--   In any case, also returns spine @es@ in reduced form
--   (with all the weak head reductions performed that were necessary
--   to come to a decision).
matchCopatterns :: [I.Arg Pattern] -> [Elim] -> TCM (Match Term, [Elim])
matchCopatterns ps vs = do
    reportSDoc "tc.match" 50 $
      vcat [ text "matchCopatterns"
           , nest 2 $ text "ps =" <+> fsep (punctuate comma $ map (prettyTCM . unArg) ps)
           , nest 2 $ text "vs =" <+> fsep (punctuate comma $ map prettyTCM vs)
           ]
    mapFst mconcat . unzip <$> zipWithM' matchCopattern ps vs

-- | Match a single copattern.
matchCopattern :: I.Arg Pattern -> Elim -> TCM (Match Term, Elim)
matchCopattern (Arg _ (ProjP p)) elim@(Proj q)
  | p == q    = return (Yes YesSimplification [], elim)
  | otherwise = return (No                      , elim)
matchCopattern (Arg _ (ProjP p)) elim@Apply{}
              = return (DontKnow Nothing, elim)
matchCopattern _ elim@Proj{} = return (DontKnow Nothing, elim)
matchCopattern p (Apply v)   = mapSnd Apply <$> matchPattern p v

matchPatterns :: [I.Arg Pattern] -> [I.Arg Term] -> TCM (Match Term, [I.Arg Term])
matchPatterns ps vs = do
    reportSDoc "tc.match" 50 $
      vcat [ text "matchPatterns"
           , nest 2 $ text "ps =" <+> fsep (punctuate comma $ map (text . show) ps)
           , nest 2 $ text "vs =" <+> fsep (punctuate comma $ map prettyTCM vs)
           ]

    (ms,vs) <- unzip <$> zipWithM' matchPattern ps vs
    return (mconcat ms, vs)

-- | Match a single pattern.
matchPattern :: I.Arg Pattern -> I.Arg Term -> TCM (Match Term, I.Arg Term)
matchPattern (Arg _  ProjP{})  _             = __IMPOSSIBLE__
matchPattern (Arg _  (VarP _)) arg@(Arg _ v) = return (Yes NoSimplification [v], arg)
matchPattern (Arg _  (DotP _)) arg@(Arg _ v) = return (Yes NoSimplification [v], arg)
matchPattern (Arg info' (LitP l)) arg@(Arg info v) = do
    w <- reduceB v
    let v = ignoreBlocking w
    case ignoreSharing <$> w of
	NotBlocked (Lit l')
	    | l == l'          -> return (Yes YesSimplification [], Arg info v)
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
               NotBlocked (Def f es) ->
                 unfoldDefinitionE True reduceB (Def f []) f es
                   -- reduceB is used here because some constructors
                   -- are actually definitions which need to be
                   -- unfolded (due to open public).
               _ -> return w
        let v = ignoreBlocking w
	case ignoreSharing <$> w of

{- Andreas, 2013-10-27 the following considered HARMFUL:
          -- Andreas, 2010-09-07 matching a record constructor against
          -- something irrelevant will just continue matching against
          -- irrelevant stuff
          -- NotBlocked (Sort Prop)
          _  | isIrrelevant info -> do
		(m, vs) <- matchPatterns ps $
                  repeat $ setRelevance Irrelevant $ defaultArg $ Sort Prop
                    -- repeat looks very bad here (non-termination!)
		return (m, Arg info $ Con c vs)
-}
	  NotBlocked (Con c' vs)
	    | c == c'            -> do
		(m, vs) <- yesSimplification <$> matchPatterns ps vs
		return (m, Arg info $ Con c' vs)
	    | otherwise           -> return (No, Arg info v) -- NOTE: v the reduced thing(shadowing!). Andreas, 2013-07-03
	  NotBlocked (MetaV x vs) -> return (DontKnow $ Just x, Arg info v)
	  Blocked x _             -> return (DontKnow $ Just x, Arg info v)
          _                       -> return (DontKnow Nothing, Arg info v)

yesSimplification (Yes _ vs, us) = (Yes YesSimplification vs, us)
yesSimplification r              = r
