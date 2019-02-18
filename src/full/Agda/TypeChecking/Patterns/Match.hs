{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}

-- | Pattern matcher used in the reducer for clauses that
--   have not been compiled to case trees yet.

module Agda.TypeChecking.Patterns.Match where

import Prelude hiding (null)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Monoid
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (getName',builtinHComp)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Datatypes

import Agda.Utils.Empty
import Agda.Utils.Functor (for, ($>))
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- | If matching is inconclusive (@DontKnow@) we want to know whether
--   it is due to a particular meta variable.
data Match a = Yes Simplification (IntMap (Arg a))
             | No
             | DontKnow (Blocked ())
  deriving Functor

instance Null (Match a) where
  empty = Yes empty empty
  null (Yes simpl as) = null simpl && null as
  null _              = False

matchedArgs :: Empty -> Int -> IntMap (Arg a) -> [Arg a]
matchedArgs err n vs = map get [0..n-1]
  where
    get k = fromMaybe (absurd err) $ IntMap.lookup k vs

-- | Builds a proper substitution from an IntMap produced by match(Co)patterns
buildSubstitution :: (DeBruijn a)
                  => Empty -> Int -> IntMap (Arg a) -> Substitution' a
buildSubstitution err n vs = parallelS $ map unArg $ matchedArgs err n vs


-- 'mappend' is UNUSED.
--
-- instance Monoid (Match a) where
--     mempty = Yes mempty []

--     Yes s us   `mappend` Yes s' vs        = Yes (s `mappend` s') (us ++ vs)
--     Yes _ _    `mappend` No               = No
--     Yes _ _    `mappend` DontKnow m       = DontKnow m
--     No         `mappend` _                = No

--     -- @NotBlocked (StuckOn e)@ means blocked by a variable.
--     -- In this case, no instantiation of
--     -- meta-variables will make progress.
--     DontKnow b `mappend` DontKnow b'      = DontKnow $ b `mappend` b'

--     -- One could imagine DontKnow _ `mappend` No = No, but would break the
--     -- equivalence to case-trees.
--     DontKnow m `mappend` _                = DontKnow m

-- | Instead of 'zipWithM', we need to use this lazy version
--   of combining pattern matching computations.

-- Andreas, 2014-05-08, see Issue 1124:
--
-- Due to a bug in TypeChecking.Patterns.Match
-- a failed match of (C n b) against (C O unit)
-- turned into (C n unit).
-- This was because all patterns were matched in
-- parallel, and evaluations of successfull matches
-- (and a record constructor like unit can always
-- be successfully matched) were returned, leading
-- to a reassembly of (C n b) as (C n unit) which is
-- illtyped.

-- Now patterns are matched left to right and
-- upon failure, no further matching is performed.

foldMatch
  :: forall p v . IsProjP p => (p -> v -> ReduceM (Match Term, v))
  -> [p] -> [v] -> ReduceM (Match Term, [v])
foldMatch match = loop where
  loop :: [p] -> [v] -> ReduceM (Match Term, [v])
  loop ps0 vs0 = do
    case (ps0, vs0) of
      ([], []) -> return (empty, [])
      (p : ps, v : vs) -> do
        (r, v') <- match p v
        case r of
          No | Just{} <- isProjP p -> return (No, v' : vs)
          No         -> do
            -- Issue 2964: Even when the first pattern doesn't match we should
            -- continue to the next patterns (and potentially block on them)
            -- because the splitting order in the case tree may not be
            -- left-to-right.
            (r', _vs') <- loop ps vs
            -- Issue 2968: do not use vs' here, because it might
            -- contain ill-typed terms due to eta-expansion at wrong
            -- type.
            let vs1 = v' : vs
            case r' of
              Yes s' us' -> return (No         , vs1)
              No         -> return (No         , vs1)
              DontKnow m -> return (DontKnow m , vs1)
          DontKnow m -> return (DontKnow m, v' : vs)
          Yes s us   -> do
            (r', vs') <- loop ps vs
            let vs1 = v' : vs'
            case r' of
              Yes s' us' -> return (Yes (s `mappend` s') (us `mappend` us'), vs1)
              No         -> return (No                                     , vs1)
              DontKnow m -> return (DontKnow m                             , vs1)
      _ -> __IMPOSSIBLE__


-- TODO refactor matchPattern* to work with Elim instead.
mergeElim :: Elim -> Arg Term -> Elim
mergeElim Apply{} arg = Apply arg
mergeElim (IApply x y _) arg = IApply x y (unArg arg)
mergeElim Proj{} _ = __IMPOSSIBLE__

mergeElims :: [Elim] -> [Arg Term] -> [Elim]
mergeElims = zipWith mergeElim

-- | @matchCopatterns ps es@ matches spine @es@ against copattern spine @ps@.
--
--   Returns 'Yes' and a substitution for the pattern variables
--   (in form of IntMap Term) if matching was successful.
--
--   Returns 'No' if there was a constructor or projection mismatch.
--
--   Returns 'DontKnow' if an argument could not be evaluated to
--   constructor form because of a blocking meta variable.
--
--   In any case, also returns spine @es@ in reduced form
--   (with all the weak head reductions performed that were necessary
--   to come to a decision).
matchCopatterns :: [NamedArg DeBruijnPattern]
                -> [Elim]
                -> ReduceM (Match Term, [Elim])
matchCopatterns ps vs = do
  traceSDoc "tc.match" 50
    (vcat [ "matchCopatterns"
          , nest 2 $ "ps =" <+> fsep (punctuate comma $ map (prettyTCM . namedArg) ps)
          , nest 2 $ "vs =" <+> fsep (punctuate comma $ map prettyTCM vs)
          ]) $ do
  -- Buggy, see issue 1124:
  -- mapFst mconcat . unzip <$> zipWithM' (matchCopattern . namedArg) ps vs
  foldMatch (matchCopattern . namedArg) ps vs

-- | Match a single copattern.
matchCopattern :: DeBruijnPattern
               -> Elim
               -> ReduceM (Match Term, Elim)
matchCopattern pat@ProjP{} elim@(Proj _ q) = do
  ProjP _ p <- normaliseProjP pat
  q         <- getOriginalProjection q
  return $ if p == q then (Yes YesSimplification empty, elim)
                     else (No,                          elim)
-- The following two cases are not impossible, see #2964
matchCopattern ProjP{} elim@Apply{}   = return (No , elim)
matchCopattern _       elim@Proj{}    = return (No , elim)
matchCopattern p       (Apply v) = mapSnd Apply <$> matchPattern p v
matchCopattern p       e@(IApply x y r) = mapSnd (mergeElim e) <$> matchPattern p (defaultArg r)

matchPatterns :: [NamedArg DeBruijnPattern]
              -> [Arg Term]
              -> ReduceM (Match Term, [Arg Term])
matchPatterns ps vs = do
  reportSDoc "tc.match" 20 $
     vcat [ "matchPatterns"
          , nest 2 $ "ps =" <+> prettyTCMPatternList ps
          , nest 2 $ "vs =" <+> fsep (punctuate comma $ map prettyTCM vs)
          ]

  traceSDoc "tc.match" 50
    (vcat [ "matchPatterns"
          , nest 2 $ "ps =" <+> fsep (punctuate comma $ map (text . show) ps)
          , nest 2 $ "vs =" <+> fsep (punctuate comma $ map prettyTCM vs)
          ]) $ do
  -- Buggy, see issue 1124:
  -- (ms,vs) <- unzip <$> zipWithM' (matchPattern . namedArg) ps vs
  -- return (mconcat ms, vs)
  foldMatch (matchPattern . namedArg) ps vs

-- | Match a single pattern.
matchPattern :: DeBruijnPattern
             -> Arg Term
             -> ReduceM (Match Term, Arg Term)
matchPattern p u = case (p, u) of
  (ProjP{}, _            ) -> __IMPOSSIBLE__
  (IApplyP _ _ _ x , arg ) -> return (Yes NoSimplification entry, arg)
    where entry = singleton (dbPatVarIndex x, arg)
  (VarP _ x , arg          ) -> return (Yes NoSimplification entry, arg)
    where entry = singleton (dbPatVarIndex x, arg)
  (DotP _ _ , arg@(Arg _ v)) -> return (Yes NoSimplification empty, arg)
  (LitP l , arg@(Arg _ v)) -> do
    w <- reduceB' v
    let arg' = arg $> ignoreBlocking w
    case w of
      NotBlocked _ (Lit l')
          | l == l'            -> return (Yes YesSimplification empty , arg')
          | otherwise          -> return (No                          , arg')
      NotBlocked _ (MetaV x _) -> return (DontKnow $ Blocked x ()     , arg')
      Blocked x _              -> return (DontKnow $ Blocked x ()     , arg')
      NotBlocked r t           -> return (DontKnow $ NotBlocked r' () , arg')
        where r' = stuckOn (Apply arg') r

  -- Case constructor pattern.
  (ConP c cpi ps, Arg info v) -> do
    if isNothing $ conPRecord cpi then fallback c ps (Arg info v) else do
    isEtaRecordCon (conName c) >>= \case
      Nothing -> fallback c ps (Arg info v)
      Just fs -> do
        -- Case: Eta record constructor.
        -- This case is necessary if we want to use the clauses before
        -- record pattern translation (e.g., in type-checking definitions by copatterns).
        unless (size fs == size ps) __IMPOSSIBLE__
        mapSnd (Arg info . Con c (fromConPatternInfo cpi) . map Apply) <$> do
          matchPatterns ps $ for fs $ \ (Arg ai f) -> Arg ai $ v `applyE` [Proj ProjSystem f]
    where
    isEtaRecordCon :: QName -> ReduceM (Maybe [Arg QName])
    isEtaRecordCon c = do
      (theDef <$> getConstInfo c) >>= \case
        Constructor{ conData = d } -> do
          (theDef <$> getConstInfo d) >>= \case
            r@Record{ recFields = fs } | YesEta <- recEtaEquality r -> return $ Just fs
            _ -> return Nothing
        _ -> __IMPOSSIBLE__
  (DefP o q ps, v) -> do
    let f (Def q' vs) | q == q' = Just (Def q, vs)
        f _                     = Nothing
    fallback' f ps v
 where
    -- Default: not an eta record constructor.
  fallback c ps v = do
    isMatchable <- isMatchable'
    let f (Con c' ci' vs) | c == c' = Just (Con c' ci',vs)
        f _                         = Nothing
    fallback' f ps v

  -- Regardless of blocking, constructors and a properly applied @hcomp@
  -- can be matched on.
  isMatchable' = do
    mhcomp <- getName' builtinHComp
    return $ \ r ->
      case ignoreBlocking r of
        t@Con{} -> Just t
        t@(Def q [l,a,phi,u,u0]) | Just q == mhcomp
                -> Just t
        _       -> Nothing

  -- DefP hcomp and ConP matching.
  fallback' mtc ps (Arg info v) = do
        isMatchable <- isMatchable'

        w <- reduceB' v
        -- Unfold delayed (corecursive) definitions one step. This is
        -- only necessary if c is a coinductive constructor, but
        -- 1) it does not hurt to do it all the time, and
        -- 2) whatInduction c sometimes crashes because c may point to
        --    an axiom at this stage (if we are checking the
        --    projection functions for a record type).
{-
        w <- case w of
               NotBlocked r (Def f es) ->   -- Andreas, 2014-06-12 TODO: r == ReallyNotBlocked sufficient?
                 unfoldDefinitionE True reduceB' (Def f []) f es
                   -- reduceB is used here because some constructors
                   -- are actually definitions which need to be
                   -- unfolded (due to open public).
               _ -> return w
-}
        -- Jesper, 23-06-2016: Note that unfoldCorecursion may destroy
        -- constructor forms, so we only call constructorForm after.
        w <- traverse constructorForm =<< case w of
               NotBlocked r u -> unfoldCorecursion u  -- Andreas, 2014-06-12 TODO: r == ReallyNotBlocked sufficient?
               _ -> return w
        let v = ignoreBlocking w
            arg = Arg info v  -- the reduced argument

        case w of
          b | Just t <- isMatchable b ->
            case mtc t of
              Just (bld, vs) -> do
                (m, vs1) <- yesSimplification <$> matchPatterns ps (fromMaybe __IMPOSSIBLE__ $ allApplyElims vs)
                return (m, Arg info $ bld (mergeElims vs vs1))
              Nothing
                                    -> return (No                          , arg)
          NotBlocked _ (MetaV x vs) -> return (DontKnow $ Blocked x ()     , arg)
          Blocked x _               -> return (DontKnow $ Blocked x ()     , arg)
          NotBlocked r _            -> return (DontKnow $ NotBlocked r' () , arg)
            where r' = stuckOn (Apply arg) r

-- ASR (08 November 2014). The type of the function could be
--
-- @(Match Term, [Arg Term]) -> (Match Term, [Arg Term])@.
yesSimplification :: (Match a, b) -> (Match a, b)
yesSimplification (Yes _ vs, us) = (Yes YesSimplification vs, us)
yesSimplification r              = r
