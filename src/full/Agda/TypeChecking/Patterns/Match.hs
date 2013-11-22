{-# LANGUAGE CPP, DeriveFunctor #-}

module Agda.TypeChecking.Patterns.Match where

import Data.Monoid
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I

import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Pretty

import Agda.Utils.Monad
import Agda.Utils.Size
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
matchCopatterns :: [I.NamedArg Pattern] -> [Elim] -> TCM (Match Term, [Elim])
matchCopatterns ps vs = do
    reportSDoc "tc.match" 50 $
      vcat [ text "matchCopatterns"
           , nest 2 $ text "ps =" <+> fsep (punctuate comma $ map (prettyTCM . namedArg) ps)
           , nest 2 $ text "vs =" <+> fsep (punctuate comma $ map prettyTCM vs)
           ]
    mapFst mconcat . unzip <$> zipWithM' (matchCopattern . namedArg) ps vs

-- | Match a single copattern.
matchCopattern :: Pattern -> Elim -> TCM (Match Term, Elim)
matchCopattern (ProjP p) elim@(Proj q)
  | p == q    = return (Yes YesSimplification [], elim)
  | otherwise = return (No                      , elim)
matchCopattern (ProjP p) elim@Apply{}
              = return (DontKnow Nothing, elim)
matchCopattern _ elim@Proj{} = return (DontKnow Nothing, elim)
matchCopattern p (Apply v)   = mapSnd Apply <$> matchPattern p v

matchPatterns :: [I.NamedArg Pattern] -> [I.Arg Term] -> TCM (Match Term, [I.Arg Term])
matchPatterns ps vs = do
    reportSDoc "tc.match" 50 $
      vcat [ text "matchPatterns"
           , nest 2 $ text "ps =" <+> fsep (punctuate comma $ map (text . show) ps)
           , nest 2 $ text "vs =" <+> fsep (punctuate comma $ map prettyTCM vs)
           ]

    (ms,vs) <- unzip <$> zipWithM' (matchPattern . namedArg) ps vs
    return (mconcat ms, vs)

-- | Match a single pattern.
matchPattern :: Pattern -> I.Arg Term -> TCM (Match Term, I.Arg Term)
matchPattern p u = case (p, u) of
  (ProjP{}, _            ) -> __IMPOSSIBLE__
  (VarP _ , arg@(Arg _ v)) -> return (Yes NoSimplification [v], arg)
  (DotP _ , arg@(Arg _ v)) -> return (Yes NoSimplification [v], arg)
  (LitP l , arg@(Arg _ v)) -> do
    w <- reduceB v
    let arg' = arg $> ignoreBlocking w
    case ignoreSharing <$> w of
	NotBlocked (Lit l')
	    | l == l'          -> return (Yes YesSimplification [] , arg')
	    | otherwise        -> return (No                       , arg')
	NotBlocked (MetaV x _) -> return (DontKnow $ Just x        , arg')
	Blocked x _            -> return (DontKnow $ Just x        , arg')
	_                      -> return (DontKnow Nothing         , arg')

{- Andreas, 2012-04-02 NO LONGER UP-TO-DATE
matchPattern (Arg h' r' (ConP c _ ps))     (Arg h Irrelevant v) = do
          -- Andreas, 2010-09-07 matching a record constructor against
          -- something irrelevant will just continue matching against
          -- irrelevant stuff
		(m, vs) <- matchPatterns ps $
                  repeat $ Arg NotHidden Irrelevant $ DontCare __IMPOSSIBLE__
		return (m, Arg h Irrelevant $ Con c vs)
-}

  -- Case record pattern: always succeed!
  -- This case is necessary if we want to use the clauses before
  -- record pattern translation (e.g., in type-checking definitions by copatterns).
  (ConP con@(ConHead c ds) Just{} ps, arg@(Arg info v))
     -- precondition: con actually comes with the record fields
     | size ds == size ps -> mapSnd (Arg info . Con con) <$> do
         matchPatterns ps $ for ds $ \ d -> Arg info $ v `applyE` [Proj d]
           -- TODO: correct info for projected terms
     | otherwise -> __IMPOSSIBLE__

  -- Case data constructor pattern.
  (ConP c _ ps, Arg info v) ->
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
