{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NondecreasingIndentation #-}

{-| Compile-time irrelevance.

In type theory with compile-time irrelevance à la Pfenning (LiCS 2001),
variables in the context are annotated with relevance attributes.
@@
  Γ = r₁x₁:A₁, ..., rⱼxⱼ:Aⱼ
@@
To handle irrelevant projections, we also record the current relevance
attribute in the judgement.  For instance, this attribute is equal to
to 'Irrelevant' if we are in an irrelevant position, like an
irrelevant argument.
@@
  Γ ⊢r t : A
@@
Only relevant variables can be used:
@@

  (Relevant x : A) ∈ Γ
  --------------------
  Γ  ⊢r  x  :  A
@@
Irrelevant global declarations can only be used if @r = Irrelevant@.

When we enter a @r'@-relevant function argument, we compose the @r@ with @r'@
and (left-)divide the attributes in the context by @r'@.
@@
  Γ  ⊢r  t  :  (r' x : A) → B      r' \ Γ  ⊢(r'·r)  u  :  A
  ---------------------------------------------------------
  Γ  ⊢r  t u  :  B[u/x]
@@
No surprises for abstraction:
@@

  Γ, (r' x : A)  ⊢r  :  B
  -----------------------------
  Γ  ⊢r  λxt  :  (r' x : A) → B
@@

This is different for runtime irrelevance (erasure) which is ``flat'',
meaning that once one is in an irrelevant context, all new assumptions will
be usable, since they are turned relevant once entering the context.
See Conor McBride (WadlerFest 2016), for a type system in this spirit:

We use such a rule for runtime-irrelevance:
@@
  Γ, (q \ q') x : A  ⊢q  t  :  B
  ------------------------------
  Γ  ⊢q  λxt  :  (q' x : A) → B
@@

Conor's system is however set up differently, with a very different
variable rule:

@@

  (q x : A) ∈ Γ
  --------------
  Γ  ⊢q  x  :  A

  Γ, (q·p) x : A  ⊢q  t  :  B
  -----------------------------
  Γ  ⊢q  λxt  :  (p x : A) → B

  Γ  ⊢q  t  :  (p x : A) → B       Γ'  ⊢qp  u  :  A
  -------------------------------------------------
  Γ + Γ'  ⊢q  t u  :  B[u/x]
@@


-}

module Agda.TypeChecking.Irrelevance where

import Control.Arrow (second)

import qualified Data.Map as Map

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute.Class

import Agda.Utils.Function
import Agda.Utils.Lens
import Agda.Utils.Monad

-- | data 'Relevance'
--   see "Agda.Syntax.Common".

-- * Operations on 'Dom'.

-- | Prepare parts of a parameter telescope for abstraction in constructors
--   and projections.
hideAndRelParams :: Dom a -> Dom a
hideAndRelParams = hideOrKeepInstance . mapRelevance nonStrictToIrr

-- * Operations on 'Context'.

-- | Modify the context whenever going from the l.h.s. (term side)
--   of the typing judgement to the r.h.s. (type side).
workOnTypes :: (MonadTCEnv m, HasOptions m, MonadDebug m)
            => m a -> m a
workOnTypes cont = do
  allowed <- optExperimentalIrrelevance <$> pragmaOptions
  verboseBracket "tc.irr" 60 "workOnTypes" $ workOnTypes' allowed cont

-- | Internal workhorse, expects value of --experimental-irrelevance flag
--   as argument.
workOnTypes' :: (MonadTCEnv m) => Bool -> m a -> m a
workOnTypes' experimental
  = modifyContextInfo (mapRelevance f)
  . applyQuantityToContext zeroQuantity
  . typeLevelReductions
  . localTC (\ e -> e { envWorkingOnTypes = True })
  where
    f | experimental = irrToNonStrict
      | otherwise    = id

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
--
--   Also allow the use of irrelevant definitions.
applyRelevanceToContext :: (MonadTCEnv tcm, LensRelevance r) => r -> tcm a -> tcm a
applyRelevanceToContext thing =
  case getRelevance thing of
    Relevant -> id
    rel      -> applyRelevanceToContextOnly   rel
              . applyRelevanceToJudgementOnly rel

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
--
--   Precondition: @Relevance /= Relevant@
applyRelevanceToContextOnly :: (MonadTCEnv tcm) => Relevance -> tcm a -> tcm a
applyRelevanceToContextOnly rel = localTC
  $ over eContext     (map $ inverseApplyRelevance rel)
  . over eLetBindings (Map.map . fmap . second $ inverseApplyRelevance rel)

-- | Apply relevance @rel@ the the relevance annotation of the (typing/equality)
--   judgement.  This is part of the work done when going into a @rel@-context.
--
--   Precondition: @Relevance /= Relevant@
applyRelevanceToJudgementOnly :: (MonadTCEnv tcm) => Relevance -> tcm a -> tcm a
applyRelevanceToJudgementOnly = localTC . over eRelevance . composeRelevance

-- | Like 'applyRelevanceToContext', but only act on context if
--   @--irrelevant-projections@.
--   See issue #2170.
applyRelevanceToContextFunBody :: (MonadTCM tcm, LensRelevance r) => r -> tcm a -> tcm a
applyRelevanceToContextFunBody thing cont =
  case getRelevance thing of
    Relevant -> cont
    rel -> applyWhenM (optIrrelevantProjections <$> pragmaOptions)
      (applyRelevanceToContextOnly rel) $    -- enable local irr. defs only when option
      applyRelevanceToJudgementOnly rel cont -- enable global irr. defs alway

-- | (Conditionally) wake up erased variables and make them unrestricted.
--   For instance,
--   in an erased function argument otherwise erased variables
--   may be used, so they are awoken before type checking the argument.
--
--   Also allow the use of erased definitions.
applyQuantityToContext :: (MonadTCEnv tcm, LensQuantity q) => q -> tcm a -> tcm a
applyQuantityToContext thing =
  case getQuantity thing of
    Quantity1{} -> id
    q         -> applyQuantityToContextOnly   q
               . applyQuantityToJudgementOnly q

-- | (Conditionally) wake up erased variables and make them unrestricted.
--   For instance,
--   in an erased function argument otherwise erased variables
--   may be used, so they are awoken before type checking the argument.
--
--   Precondition: @Quantity /= Quantity1@
applyQuantityToContextOnly :: (MonadTCEnv tcm) => Quantity -> tcm a -> tcm a
applyQuantityToContextOnly q = localTC
  $ over eContext     (map $ inverseApplyQuantity q)
  . over eLetBindings (Map.map . fmap . second $ inverseApplyQuantity q)

-- | Apply quantity @q@ the the quantity annotation of the (typing/equality)
--   judgement.  This is part of the work done when going into a @q@-context.
--
--   Precondition: @Quantity /= Quantity1@
applyQuantityToJudgementOnly :: (MonadTCEnv tcm) => Quantity -> tcm a -> tcm a
applyQuantityToJudgementOnly = localTC . over eQuantity . composeQuantity

-- | Apply inverse composition with the given cohesion to the typing context.
applyCohesionToContext :: (MonadTCEnv tcm, LensCohesion m) => m -> tcm a -> tcm a
applyCohesionToContext thing =
  case getCohesion thing of
    m | m == mempty -> id
      | otherwise   -> applyCohesionToContextOnly   m
                       -- Cohesion does not apply to the judgment.

applyCohesionToContextOnly :: (MonadTCEnv tcm) => Cohesion -> tcm a -> tcm a
applyCohesionToContextOnly q = localTC
  $ over eContext     (map $ inverseApplyCohesion q)
  . over eLetBindings (Map.map . fmap . second $ inverseApplyCohesion q)

-- | Can we split on arguments of the given cohesion?
splittableCohesion :: (HasOptions m, LensCohesion a) => a -> m Bool
splittableCohesion a = do
  let c = getCohesion a
  pure (usableCohesion c) `and2M` (pure (c /= Flat) `or2M` do optFlatSplit <$> pragmaOptions)

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
--
--   Also allow the use of irrelevant definitions.
applyModalityToContext :: (MonadTCEnv tcm, LensModality m) => m -> tcm a -> tcm a
applyModalityToContext thing =
  case getModality thing of
    m | m == mempty -> id
      | otherwise   -> applyModalityToContextOnly   m
                     . applyModalityToJudgementOnly m

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
--
--   Precondition: @Modality /= Relevant@
applyModalityToContextOnly :: (MonadTCEnv tcm) => Modality -> tcm a -> tcm a
applyModalityToContextOnly m = localTC
  $ over eContext     (map $ inverseApplyModality m)
  . over eLetBindings (Map.map . fmap . second $ inverseApplyModality m)

-- | Apply modality @m@ the the modality annotation of the (typing/equality)
--   judgement.  This is part of the work done when going into a @m@-context.
--
--   Precondition: @Modality /= Relevant@
applyModalityToJudgementOnly :: (MonadTCEnv tcm) => Modality -> tcm a -> tcm a
applyModalityToJudgementOnly = localTC . over eModality . composeModality

-- | Like 'applyModalityToContext', but only act on context (for Relevance) if
--   @--irrelevant-projections@.
--   See issue #2170.
applyModalityToContextFunBody :: (MonadTCM tcm, LensModality r) => r -> tcm a -> tcm a
applyModalityToContextFunBody thing cont = do
    ifM (optIrrelevantProjections <$> pragmaOptions)
      {-then-} (applyModalityToContext m cont)                -- enable global irr. defs always
      {-else-} (applyRelevanceToContextFunBody (getRelevance m)
               $ applyCohesionToContext (getCohesion m)
               $ applyQuantityToContext (getQuantity m) cont) -- enable local irr. defs only when option
  where
    m = getModality thing

-- | Wake up irrelevant variables and make them relevant. This is used
--   when type checking terms in a hole, in which case you want to be able to
--   (for instance) infer the type of an irrelevant variable. In the course
--   of type checking an irrelevant function argument 'applyRelevanceToContext'
--   is used instead, which also sets the context relevance to 'Irrelevant'.
--   This is not the right thing to do when type checking interactively in a
--   hole since it also marks all metas created during type checking as
--   irrelevant (issue #2568).
wakeIrrelevantVars :: (MonadTCEnv tcm) => tcm a -> tcm a
wakeIrrelevantVars
  = applyRelevanceToContextOnly Irrelevant
  . applyQuantityToContextOnly  zeroQuantity

-- | Check whether something can be used in a position of the given relevance.
--
--   This is a substitute for double-checking that only makes sure
--   relevances are correct.  See issue #2640.
--
--   Used in unifier (@ unifyStep Solution{}@).
--
--   At the moment, this implements McBride-style irrelevance,
--   where Pfenning-style would be the most accurate thing.
--   However, these two notions only differ how they handle
--   bound variables in a term.  Here, we are only concerned
--   in the free variables, used meta-variables, and used
--   (irrelevant) definitions.
--
class UsableRelevance a where
  usableRel :: Relevance -> a -> TCM Bool

instance UsableRelevance Term where
  usableRel rel u = case u of
    Var i vs -> do
      irel <- getRelevance <$> domOfBV i
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
    DontCare v -> usableRel rel v -- TODO: allow irrelevant things to be used in DontCare position?
    Dummy{}  -> return True

instance UsableRelevance a => UsableRelevance (Type' a) where
  usableRel rel (El _ t) = usableRel rel t

instance UsableRelevance Sort where
  usableRel rel s = case s of
    Type l -> usableRel rel l
    Prop l -> usableRel rel l
    Inf    -> return True
    SizeUniv -> return True
    PiSort a s -> usableRel rel (a,s)
    UnivSort s -> usableRel rel s
    MetaS x es -> usableRel rel es
    DefS d es  -> usableRel rel $ Def d es
    DummyS{} -> return True

instance UsableRelevance Level where
  usableRel rel (Max _ ls) = usableRel rel ls

instance UsableRelevance PlusLevel where
  usableRel rel (Plus _ l) = usableRel rel l

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
  usableRel rel Dom{unDom = u} = usableRel rel u

instance (Subst t a, UsableRelevance a) => UsableRelevance (Abs a) where
  usableRel rel abs = underAbstraction_ abs $ \u -> usableRel rel u

-- | Check whether something can be used in a position of the given modality.
--
--   This is a substitute for double-checking that only makes sure
--   modalities are correct.  See issue #2640.
--
--   Used in unifier (@ unifyStep Solution{}@).
--
--   This uses McBride-style modality checking.
--   It does not differ from Pfenning-style if we
--   are only interested in the modality of the
--   free variables, used meta-variables, and used
--   definitions.
--
class UsableModality a where
  usableMod :: Modality -> a -> TCM Bool

instance UsableModality Term where
  usableMod mod u = case u of
    Var i vs -> do
      imod <- getModality <$> domOfBV i
      let ok = imod `moreUsableModality` mod
      reportSDoc "tc.irr" 50 $
        "Variable" <+> prettyTCM (var i) <+>
        text ("has modality " ++ show imod ++ ", which is a " ++
              (if ok then "" else "NOT ") ++ "more usable modality than " ++ show mod)
      return ok `and2M` usableMod mod vs
    Def f vs -> do
      fmod <- modalityOfConst f
      let ok = fmod `moreUsableModality` mod
      reportSDoc "tc.irr" 50 $
        "Definition" <+> prettyTCM (Def f []) <+>
        text ("has modality " ++ show fmod ++ ", which is a " ++
              (if ok then "" else "NOT ") ++ "more usable modality than " ++ show mod)
      return ok `and2M` usableMod mod vs
    Con c _ vs -> usableMod mod vs
    Lit l    -> return True
    Lam _ v  -> usableMod mod v
    Pi a b   -> usableMod mod (a,b)
    Sort s   -> usableMod mod s
    Level l  -> return True
    MetaV m vs -> do
      mmod <- getMetaModality <$> lookupMeta m
      let ok = mmod `moreUsableModality` mod
      reportSDoc "tc.irr" 50 $
        "Metavariable" <+> prettyTCM (MetaV m []) <+>
        text ("has modality " ++ show mmod ++ ", which is a " ++
              (if ok then "" else "NOT ") ++ "more usable modality than " ++ show mod)
      return ok `and2M` usableMod mod vs
    DontCare v -> usableMod mod v
    Dummy{}  -> return True

instance UsableRelevance a => UsableModality (Type' a) where
  usableMod mod (El _ t) = usableRel (getRelevance mod) t

instance UsableModality Sort where
  usableMod mod s = usableRel (getRelevance mod) s
  -- usableMod mod s = case s of
  --   Type l -> usableMod mod l
  --   Prop l -> usableMod mod l
  --   Inf    -> return True
  --   SizeUniv -> return True
  --   PiSort a s -> usableMod mod (a,s)
  --   UnivSort s -> usableMod mod s
  --   MetaS x es -> usableMod mod es
  --   DummyS{} -> return True

instance UsableModality Level where
  usableMod mod (Max _ ls) = usableRel (getRelevance mod) ls

-- instance UsableModality PlusLevel where
--   usableMod mod ClosedLevel{} = return True
--   usableMod mod (Plus _ l)    = usableMod mod l

-- instance UsableModality LevelAtom where
--   usableMod mod l = case l of
--     MetaLevel m vs -> do
--       mmod <- getMetaModality <$> lookupMeta m
--       return (mmod `moreUsableModality` mod) `and2M` usableMod mod vs
--     NeutralLevel _ v -> usableMod mod v
--     BlockedLevel _ v -> usableMod mod v
--     UnreducedLevel v -> usableMod mod v

instance UsableModality a => UsableModality [a] where
  usableMod mod = andM . map (usableMod mod)

instance (UsableModality a, UsableModality b) => UsableModality (a,b) where
  usableMod mod (a,b) = usableMod mod a `and2M` usableMod mod b

instance UsableModality a => UsableModality (Elim' a) where
  usableMod mod (Apply a) = usableMod mod a
  usableMod mod (Proj _ p) = do
    pmod <- modalityOfConst p
    return $ pmod `moreUsableModality` mod
  usableMod mod (IApply x y v) = allM [x,y,v] $ usableMod mod

instance UsableModality a => UsableModality (Arg a) where
  usableMod mod (Arg info u) =
    let mod' = getModality info
    in  usableMod (mod `composeModality` mod') u

instance UsableModality a => UsableModality (Dom a) where
  usableMod mod Dom{unDom = u} = usableMod mod u

instance (Subst t a, UsableModality a) => UsableModality (Abs a) where
  usableMod mod abs = underAbstraction_ abs $ \u -> usableMod mod u


-- * Propositions

-- | Is a type a proposition?  (Needs reduction.)

isPropM :: (LensSort a, PrettyTCM a, MonadReduce m, MonadDebug m) => a -> m Bool
isPropM a = do
  traceSDoc "tc.prop" 80 ("Is " <+> prettyTCM a <+> "of sort" <+> prettyTCM (getSort a) <+> "in Prop?") $ do
  reduce (getSort a) <&> \case
    Prop{} -> True
    _      -> False

isIrrelevantOrPropM :: (LensRelevance a, LensSort a, PrettyTCM a, MonadReduce m, MonadDebug m) => a -> m Bool
isIrrelevantOrPropM x = return (isIrrelevant x) `or2M` isPropM x
