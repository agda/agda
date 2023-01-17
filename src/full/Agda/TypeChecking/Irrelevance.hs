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

import Control.Monad.Except

import qualified Data.Map as Map

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Concrete.Pretty

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute.Class

import Agda.Utils.Function
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.WithDefault
import qualified Agda.Utils.Null as Null

-- | data 'Relevance'
--   see "Agda.Syntax.Common".

-- * Operations on 'Dom'.

-- | Prepare parts of a parameter telescope for abstraction in constructors
--   and projections.
hideAndRelParams :: (LensHiding a, LensRelevance a) => a -> a
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
  = (if experimental
     then modifyContextInfo (mapRelevance irrToNonStrict)
     else id)
  . applyQuantityToJudgement zeroQuantity
  . typeLevelReductions
  . localTC (\ e -> e { envWorkingOnTypes = True })

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
  . over eLetBindings (Map.map . fmap . onLetBindingType $ inverseApplyRelevance rel)

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

-- | Apply the quantity to the quantity annotation of the
-- (typing/equality) judgement.
--
-- Precondition: The quantity must not be @'Quantity1' something@.
applyQuantityToJudgement ::
  (MonadTCEnv tcm, LensQuantity q) => q -> tcm a -> tcm a
applyQuantityToJudgement =
  localTC . over eQuantity . composeQuantity . getQuantity

-- | Apply inverse composition with the given cohesion to the typing context.
applyCohesionToContext :: (MonadTCEnv tcm, LensCohesion m) => m -> tcm a -> tcm a
applyCohesionToContext thing =
  case getCohesion thing of
    m | m == unitCohesion -> id
      | otherwise         -> applyCohesionToContextOnly   m
                             -- Cohesion does not apply to the judgment.

applyCohesionToContextOnly :: (MonadTCEnv tcm) => Cohesion -> tcm a -> tcm a
applyCohesionToContextOnly q = localTC
  $ over eContext     (map $ inverseApplyCohesion q)
  . over eLetBindings (Map.map . fmap . onLetBindingType $ inverseApplyCohesion q)

-- | Can we split on arguments of the given cohesion?
splittableCohesion :: (HasOptions m, LensCohesion a) => a -> m Bool
splittableCohesion a = do
  let c = getCohesion a
  pure (usableCohesion c) `and2M` (pure (c /= Flat) `or2M` do collapseDefault . optFlatSplit <$> pragmaOptions)

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
--
--   Also allow the use of irrelevant definitions.
--
--   This function might also do something for other modalities.
applyModalityToContext :: (MonadTCEnv tcm, LensModality m) => m -> tcm a -> tcm a
applyModalityToContext thing =
  case getModality thing of
    m | m == unitModality -> id
      | otherwise         -> applyModalityToContextOnly   m
                           . applyModalityToJudgementOnly m

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the
--   argument.
--
--   This function might also do something for other modalities, but
--   not for quantities.
--
--   Precondition: @Modality /= Relevant@
applyModalityToContextOnly :: (MonadTCEnv tcm) => Modality -> tcm a -> tcm a
applyModalityToContextOnly m = localTC
  $ over eContext (map $ inverseApplyModalityButNotQuantity m)
  . over eLetBindings
      (Map.map . fmap . onLetBindingType $ inverseApplyModalityButNotQuantity m)

-- | Apply the relevance and quantity components of the modality to
-- the modality annotation of the (typing/equality) judgement.
--
-- Precondition: The relevance component must not be 'Relevant'.
applyModalityToJudgementOnly :: (MonadTCEnv tcm) => Modality -> tcm a -> tcm a
applyModalityToJudgementOnly m =
  localTC $ over eRelevance (composeRelevance (getRelevance m)) .
            over eQuantity  (composeQuantity  (getQuantity m))

-- | Like 'applyModalityToContext', but only act on context (for Relevance) if
--   @--irrelevant-projections@.
--   See issue #2170.
applyModalityToContextFunBody :: (MonadTCM tcm, LensModality r) => r -> tcm a -> tcm a
applyModalityToContextFunBody thing cont = do
    ifM (optIrrelevantProjections <$> pragmaOptions)
      {-then-} (applyModalityToContext m cont)                -- enable global irr. defs always
      {-else-} (applyRelevanceToContextFunBody (getRelevance m)
               $ applyCohesionToContext (getCohesion m)
               $ applyQuantityToJudgement (getQuantity m) cont) -- enable local irr. defs only when option
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
--
--   Also set the current quantity to 0.
wakeIrrelevantVars :: (MonadTCEnv tcm) => tcm a -> tcm a
wakeIrrelevantVars
  = applyRelevanceToContextOnly Irrelevant
  . applyQuantityToJudgement zeroQuantity

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
  usableRel
    :: (ReadTCState m, HasConstInfo m, MonadTCEnv m, MonadAddContext m, MonadDebug m)
    => Relevance -> a -> m Bool

instance UsableRelevance Term where
  usableRel rel = \case
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
      mrel <- getRelevance <$> lookupMetaModality m
      return (mrel `moreRelevant` rel) `and2M` usableRel rel vs
    DontCare v -> usableRel rel v -- TODO: allow irrelevant things to be used in DontCare position?
    Dummy{}  -> return True

instance UsableRelevance a => UsableRelevance (Type' a) where
  usableRel rel (El _ t) = usableRel rel t

instance UsableRelevance Sort where
  usableRel rel = \case
    Type l -> usableRel rel l
    Prop l -> usableRel rel l
    Inf f n -> return True
    SSet l -> usableRel rel l
    SizeUniv -> return True
    LockUniv -> return True
    IntervalUniv -> return True
    PiSort a s1 s2 -> usableRel rel (a,s1,s2)
    FunSort s1 s2 -> usableRel rel (s1,s2)
    UnivSort s -> usableRel rel s
    MetaS x es -> usableRel rel es
    DefS d es  -> usableRel rel $ Def d es
    DummyS{} -> return True

instance UsableRelevance Level where
  usableRel rel (Max _ ls) = usableRel rel ls

instance UsableRelevance PlusLevel where
  usableRel rel (Plus _ l) = usableRel rel l

instance UsableRelevance a => UsableRelevance [a] where
  usableRel rel = andM . map (usableRel rel)

instance (UsableRelevance a, UsableRelevance b) => UsableRelevance (a,b) where
  usableRel rel (a,b) = usableRel rel a `and2M` usableRel rel b

instance (UsableRelevance a, UsableRelevance b, UsableRelevance c) => UsableRelevance (a,b,c) where
  usableRel rel (a,b,c) = usableRel rel a `and2M` usableRel rel b `and2M` usableRel rel c

instance UsableRelevance a => UsableRelevance (Elim' a) where
  usableRel rel (Apply a) = usableRel rel a
  usableRel rel (Proj _ p) = do
    prel <- relOfConst p
    return $ prel `moreRelevant` rel
  usableRel rel (IApply x y v) = usableRel rel v

instance UsableRelevance a => UsableRelevance (Arg a) where
  usableRel rel (Arg info u) =
    let rel' = getRelevance info
    in  usableRel (rel `composeRelevance` rel') u

instance UsableRelevance a => UsableRelevance (Dom a) where
  usableRel rel Dom{unDom = u} = usableRel rel u

instance (Subst a, UsableRelevance a) => UsableRelevance (Abs a) where
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
  usableMod
    :: (ReadTCState m, HasConstInfo m, MonadTCEnv m, MonadAddContext m, MonadDebug m, MonadReduce m, MonadError Blocker m)
    => Modality -> a -> m Bool

instance UsableModality Term where
  usableMod mod u = do
   case u of
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
    Con c o vs -> do
      cmod <- modalityOfConst (conName c)
      let ok = cmod `moreUsableModality` mod
      reportSDoc "tc.irr" 50 $
        "The constructor" <+> prettyTCM (Con c o []) <+>
        text ("has the modality " ++ show cmod ++ ", which is " ++
              (if ok then "" else "NOT ") ++
              "more usable than the modality " ++ show mod ++ ".")
      return ok `and2M` usableMod mod vs
    Lit l    -> return True
    Lam info v  -> usableModAbs info mod v
    -- Even if Pi contains Type, here we check it as a constructor for terms in the universe.
    Pi a b   -> usableMod domMod (unEl $ unDom a) `and2M` usableModAbs (getArgInfo a) mod (unEl <$> b)
      where
        domMod = mapQuantity (composeQuantity $ getQuantity a) $
                 mapCohesion (composeCohesion $ getCohesion a) mod
    -- Andrea 15/10/2020 not updating these cases yet, but they are quite suspicious,
    -- do we have special typing rules for Sort and Level?
    Sort s   -> usableMod mod s
    Level l  -> return True
    MetaV m vs -> do
      mmod <- lookupMetaModality m
      let ok = mmod `moreUsableModality` mod
      reportSDoc "tc.irr" 50 $
        "Metavariable" <+> prettyTCM (MetaV m []) <+>
        text ("has modality " ++ show mmod ++ ", which is a " ++
              (if ok then "" else "NOT ") ++ "more usable modality than " ++ show mod)
      (return ok `and2M` usableMod mod vs) `or2M` do
        u <- instantiate u
        caseMaybe (isMeta u) (usableMod mod u) $ \ m -> throwError (UnblockOnMeta m)
    DontCare v -> usableMod mod v
    Dummy{}  -> return True

usableModAbs :: (Subst a, MonadAddContext m, UsableModality a,
                       ReadTCState m, HasConstInfo m, MonadReduce m, MonadError Blocker m) =>
                      ArgInfo -> Modality -> Abs a -> m Bool
usableModAbs info mod abs = underAbstraction (setArgInfo info $ __DUMMY_DOM__) abs $ \ u -> usableMod mod u

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

instance UsableModality a => UsableModality [a] where
  usableMod mod = andM . map (usableMod mod)

instance (UsableModality a, UsableModality b) => UsableModality (a,b) where
  usableMod mod (a,b) = usableMod mod a `and2M` usableMod mod b

instance UsableModality a => UsableModality (Elim' a) where
  usableMod mod (Apply a) = usableMod mod a
  usableMod mod (Proj _ p) = do
    pmod <- modalityOfConst p
    return $ pmod `moreUsableModality` mod
  usableMod mod (IApply x y v) = usableMod mod v

instance UsableModality a => UsableModality (Arg a) where
  usableMod mod (Arg info u) =
    let mod' = getModality info
    in  usableMod (mod `composeModality` mod') u

instance UsableModality a => UsableModality (Dom a) where
  usableMod mod Dom{unDom = u} = usableMod mod u

usableAtModality'
  :: MonadConstraint TCM
  -- Note: This weird-looking constraint is to trick GHC into accepting
  -- that an instance of MonadConstraint TCM will exist, even if we
  -- can't import the module in which it is defined.
  => Maybe Sort -> WhyCheckModality -> Modality -> Term -> TCM ()
usableAtModality' ms why mod t =
  catchConstraint (UsableAtModality why ms mod t) $ do
    whenM (maybe (pure True) isFibrant ms) $ do
      res <- runExceptT $ usableMod mod t
      case res of
        Right b -> unless b $
          typeError . GenericDocError =<< formatWhy
        Left blocker -> patternViolation blocker
  where
    formatWhy = do
      compatible <- collapseDefault . optCubicalCompatible <$> pragmaOptions
      cubical <- isJust . optCubical <$> pragmaOptions
      let
        context
          | cubical    = "in Cubical Agda,"
          | compatible = "to maintain compatibility with Cubical Agda,"
          | otherwise  = "when --without-K is enabled,"

        explanation what
          | cubical || compatible =
            [ ""
            , fsep ( "Note:":pwords context
                  ++ pwords what ++ pwords "must be usable at the modality"
                  ++ pwords "in which the function was defined, since it will be"
                  ++ pwords "used for computing transports"
                  )
            , ""
            ]
          | otherwise = []

      case why of
        IndexedClause ->
          vcat $
            ( fsep ( pwords "This clause has target type"
                  ++ [prettyTCM t]
                  ++ pwords "which is not usable at the required modality"
                  ++ [pure (attributesForModality mod) <> "."]
                   )
            : explanation "the target type")

        -- Arguments sometimes need to be transported too:
        IndexedClauseArg forced the_arg ->
          vcat $
            ( fsep (pwords "The argument" ++ [prettyTCM the_arg] ++ pwords "has type")
            : nest 2 (prettyTCM t)
            : fsep ( pwords "which is not usable at the required modality"
                  ++ [pure (attributesForModality mod) <> "."] )
            : explanation "this argument's type")

        -- Note: if a generated clause is modality-incorrect, that's a
        -- bug in the LHS modality check
        GeneratedClause ->
          __IMPOSSIBLE_VERBOSE__ . show =<<
                   prettyTCM t
              <+> "is not usable at the required modality"
              <+> pure (attributesForModality mod)
        _ -> prettyTCM t <+> "is not usable at the required modality"
         <+> pure (attributesForModality mod)


usableAtModality :: MonadConstraint TCM => WhyCheckModality -> Modality -> Term -> TCM ()
usableAtModality = usableAtModality' Nothing


-- * Propositions

-- | Is a type a proposition?  (Needs reduction.)

isPropM
  :: (LensSort a, PrettyTCM a, PureTCM m, MonadBlock m)
  => a -> m Bool
isPropM a = do
  traceSDoc "tc.prop" 80 ("Is " <+> prettyTCM a <+> "of sort" <+> prettyTCM (getSort a) <+> "in Prop?") $ do
  abortIfBlocked (getSort a) <&> \case
    Prop{} -> True
    _      -> False

isIrrelevantOrPropM
  :: (LensRelevance a, LensSort a, PrettyTCM a, PureTCM m, MonadBlock m)
  => a -> m Bool
isIrrelevantOrPropM x = return (isIrrelevant x) `or2M` isPropM x

-- * Fibrant types

-- | Is a type fibrant (i.e. Type, Prop)?

isFibrant
  :: (LensSort a, PureTCM m, MonadBlock m)
  => a -> m Bool
isFibrant a = abortIfBlocked (getSort a) <&> \case
  Type{}     -> True
  Prop{}     -> True
  Inf f _    -> f == IsFibrant
  SSet{}     -> False
  SizeUniv{} -> False
  LockUniv{} -> False
  IntervalUniv{} -> False
  PiSort{}   -> False
  FunSort{}  -> False
  UnivSort{} -> False
  MetaS{}    -> False
  DefS{}     -> False
  DummyS{}   -> False


-- | Cofibrant types are those that could be the domain of a fibrant
--   pi type. (Notion by C. Sattler).
isCoFibrantSort :: (LensSort a, PureTCM m, MonadBlock m) => a -> m Bool
isCoFibrantSort a = abortIfBlocked (getSort a) <&> \case
  Type{}     -> True
  Prop{}     -> True
  Inf f _    -> f == IsFibrant
  SSet{}     -> False
  SizeUniv{} -> False
  LockUniv{} -> True
  IntervalUniv{} -> True
  PiSort{}   -> False
  FunSort{}  -> False
  UnivSort{} -> False
  MetaS{}    -> False
  DefS{}     -> False
  DummyS{}   -> False
