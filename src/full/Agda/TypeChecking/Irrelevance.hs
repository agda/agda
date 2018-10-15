{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

{-| Irrelevant function types.
-}
module Agda.TypeChecking.Irrelevance where

import Control.Arrow (first, second)
import Control.Monad.Reader

import qualified Data.Map as Map

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute.Class

import Agda.Utils.Lens
import Agda.Utils.Monad

#include "undefined.h"
import Agda.Utils.Impossible

-- | data 'Relevance'
--   see "Agda.Syntax.Common".

-- * Operations on 'Dom'.

-- | Prepare parts of a parameter telescope for abstraction in constructors
--   and projections.
hideAndRelParams :: Dom a -> Dom a
hideAndRelParams = hideOrKeepInstance . mapRelevance nonStrictToIrr

-- | Used to modify context when going into a @rel@ argument.
inverseApplyRelevance :: Relevance -> Dom a -> Dom a
inverseApplyRelevance rel = mapRelevance (rel `inverseComposeRelevance`)

-- | Compose two relevance flags.
--   This function is used to update the relevance information
--   on pattern variables @a@ after a match against something @rel@.
applyRelevance :: Relevance -> Dom a -> Dom a
applyRelevance rel = mapRelevance (rel `composeRelevance`)

-- * Operations on 'Context'.

-- | Modify the context whenever going from the l.h.s. (term side)
--   of the typing judgement to the r.h.s. (type side).
workOnTypes :: TCM a -> TCM a
workOnTypes cont = do
  allowed <- optExperimentalIrrelevance <$> pragmaOptions
  verboseBracket "tc.irr" 20 "workOnTypes" $ workOnTypes' allowed cont

-- | Internal workhorse, expects value of --experimental-irrelevance flag
--   as argument.
workOnTypes' :: Bool -> TCM a -> TCM a
workOnTypes' experimental =
  modifyContext (map $ mapRelevance f) .
  localTC (\ e -> e { envWorkingOnTypes = True })
  where
    f | experimental = irrToNonStrict . nonStrictToRel
      | otherwise    = nonStrictToRel

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
--
--   Also allow the use of irrelevant definitions.
applyRelevanceToContext :: (MonadTCM tcm) => Relevance -> tcm a -> tcm a
applyRelevanceToContext rel =
  case rel of
    Relevant -> id
    _        -> localTC
      $ over eContext     (map $ inverseApplyRelevance rel)
      . over eLetBindings (Map.map . fmap . second $ inverseApplyRelevance rel)
                                                  -- enable local  irr. defs
      . over eRelevance   (composeRelevance rel)  -- enable global irr. defs

-- | Like 'applyRelevanceToContext', but only act on context if
--   @--irrelevant-projections@.
--   See issue #2170.
applyRelevanceToContextFunBody :: (MonadTCM tcm) => Relevance -> tcm a -> tcm a
applyRelevanceToContextFunBody rel cont
  | rel == Relevant = cont
  | otherwise = do
    ifM (optIrrelevantProjections <$> pragmaOptions)
      {-then-} (applyRelevanceToContext rel cont)
      {-else-} (localTC (over eRelevance $ composeRelevance rel) cont)
               -- just enable global irr. defs

-- | Wake up irrelevant variables and make them relevant. This is used
--   when type checking terms in a hole, in which case you want to be able to
--   (for instance) infer the type of an irrelevant variable. In the course
--   of type checking an irrelevant function argument 'applyRelevanceToContext'
--   is used instead, which also sets the context relevance to 'Irrelevant'.
--   This is not the right thing to do when type checking interactively in a
--   hole since it also marks all metas created during type checking as
--   irrelevant (issue #2568).
wakeIrrelevantVars :: TCM a -> TCM a
wakeIrrelevantVars = localTC
  $ over eContext     (map                     $ inverseApplyRelevance Irrelevant)
  . over eLetBindings (Map.map . fmap . second $ inverseApplyRelevance Irrelevant)

-- | Check whether something can be used in a position of the given relevance.
--
--   Used in unifier (@unifyStep Solution{}@).
--
class UsableRelevance a where
  usableRel :: Relevance -> a -> TCM Bool

instance UsableRelevance Term where
  usableRel rel u = case u of
    Var i vs -> do
      irel <- getRelevance <$> typeOfBV' i
      let ok = irel `moreRelevant` rel
      reportSDoc "tc.irr" 50 $
        "Variable" <+> prettyTCM (var i) <+>
        text ("has relevance " ++ show irel ++ ", which is " ++
              (if ok then "" else "NOT ") ++ "more relevant than " ++ show rel)
      return ok `and2M` usableRel rel vs
    Def f vs -> do
      frel <- relOfConst f
      return (frel `moreRelevant` rel) `and2M` usableRel rel vs
    Con c _ vs -> usableRel rel vs
    Lit l    -> return True
    Lam _ v  -> usableRel rel v
    Pi a b   -> usableRel rel (a,b)
    Sort s   -> usableRel rel s
    Level l  -> return True
    MetaV m vs -> do
      mrel <- getMetaRelevance <$> lookupMeta m
      return (mrel `moreRelevant` rel) `and2M` usableRel rel vs
    DontCare _ -> return $ isIrrelevant rel
    Dummy{}  -> return True

instance UsableRelevance a => UsableRelevance (Type' a) where
  usableRel rel (El _ t) = usableRel rel t

instance UsableRelevance Sort where
  usableRel rel s = case s of
    Type l -> usableRel rel l
    Prop l -> usableRel rel l
    Inf    -> return True
    SizeUniv -> return True
    PiSort s1 s2 -> usableRel rel (s1,s2)
    UnivSort s -> usableRel rel s
    MetaS x es -> usableRel rel es
    DummyS{} -> return True

instance UsableRelevance Level where
  usableRel rel (Max ls) = usableRel rel ls

instance UsableRelevance PlusLevel where
  usableRel rel ClosedLevel{} = return True
  usableRel rel (Plus _ l)    = usableRel rel l

instance UsableRelevance LevelAtom where
  usableRel rel l = case l of
    MetaLevel m vs -> do
      mrel <- getMetaRelevance <$> lookupMeta m
      return (mrel `moreRelevant` rel) `and2M` usableRel rel vs
    NeutralLevel _ v -> usableRel rel v
    BlockedLevel _ v -> usableRel rel v
    UnreducedLevel v -> usableRel rel v

instance UsableRelevance a => UsableRelevance [a] where
  usableRel rel = andM . map (usableRel rel)

instance (UsableRelevance a, UsableRelevance b) => UsableRelevance (a,b) where
  usableRel rel (a,b) = usableRel rel a `and2M` usableRel rel b

instance UsableRelevance a => UsableRelevance (Elim' a) where
  usableRel rel (Apply a) = usableRel rel a
  usableRel rel (Proj _ p) = do
    prel <- relOfConst p
    return $ prel `moreRelevant` rel
  usableRel rel (IApply x y v) = allM [x,y,v] $ usableRel rel

instance UsableRelevance a => UsableRelevance (Arg a) where
  usableRel rel (Arg info u) =
    let rel' = getRelevance info
    in  usableRel (rel `composeRelevance` rel') u

instance UsableRelevance a => UsableRelevance (Dom a) where
  usableRel rel (Dom _ _ u) = usableRel rel u

instance (Subst t a, UsableRelevance a) => UsableRelevance (Abs a) where
  usableRel rel abs = underAbstraction_ abs $ \u -> usableRel rel u
