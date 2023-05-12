{-# LANGUAGE NondecreasingIndentation  #-}

{- | The occurs check for unification.  Does pruning on the fly.

  When hitting a meta variable:

  - Compute flex/rigid for its arguments.
  - Compare to allowed variables.
  - Mark arguments with rigid occurrences of disallowed variables for deletion.
  - Attempt to delete marked arguments.
  - We don't need to check for success, we can just continue occurs checking.
-}

module Agda.TypeChecking.MetaVars.Occurs where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader

import Data.Foldable (traverse_)
import Data.Functor
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)

import qualified Agda.Benchmarking as Bench

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Lazy
import Agda.TypeChecking.Free.Reduce
import Agda.TypeChecking.Level
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Records
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Telescope

import Agda.Utils.Either
import Agda.Utils.Lens
import Agda.Utils.List (downFrom)
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * MetaOccursCheck: going into definitions to exclude cyclic solutions

{- To address issue 585 (meta var occurrences in mutual defs)

data B : Set where
  inn : A -> B

out : B -> A
out (inn a) = a

postulate
  P : (y : A) (z : Unit -> B) → Set
  p : (x : Unit -> B) → P (out (x unit)) x

mutual
  d : Unit -> B
  d unit = inn _           -- Y

  g : P (out (d unit)) d
  g = p _             -- X

-- Agda solves  d unit = inn (out (d unit))
--
-- out (X unit) = out (d unit) = out (inn Y) = Y
-- X = d

When doing the occurs check on d, we need to look at the definition of
d to discover that it mentions X.

To this end, we extend the state by names of definitions that have to
be checked when they occur.  At the beginning, this is initialized
with the names in the current mutual block.  Each time we encounter a
name in the list during occurs check, we delete it (if check is
successful).  This way, we do not duplicate work.

-}

modifyOccursCheckDefs :: (Set QName -> Set QName) -> TCM ()
modifyOccursCheckDefs f = stOccursCheckDefs `modifyTCLens` f

-- | Set the names of definitions to be looked at
--   to the defs in the current mutual block.
initOccursCheck :: MetaVariable -> TCM ()
initOccursCheck mv = modifyOccursCheckDefs . const =<<
  if (miMetaOccursCheck (mvInfo mv) == DontRunMetaOccursCheck)
   then do
     reportSLn "tc.meta.occurs" 20 $
       "initOccursCheck: we do not look into definitions"
     return Set.empty
   else do
     reportSLn "tc.meta.occurs" 20 $
       "initOccursCheck: we look into the following definitions:"
     mb <- asksTC envMutualBlock
     case mb of
       Nothing -> do
         reportSLn "tc.meta.occurs" 20 $ "(none)"
         return Set.empty
       Just b  -> do
         ds <- mutualNames <$> lookupMutualBlock b
         reportSDoc "tc.meta.occurs" 20 $ sep $ map prettyTCM $ Set.toList ds
         return ds


-- | Is a def in the list of stuff to be checked?
defNeedsChecking :: QName -> TCM Bool
defNeedsChecking d = Set.member d <$> useTC stOccursCheckDefs

-- | Remove a def from the list of defs to be looked at.
tallyDef :: QName -> TCM ()
tallyDef d = modifyOccursCheckDefs $ Set.delete d

---------------------------------------------------------------------------
-- * OccursM monad and its services

-- | Extra environment for the occurs check.  (Complements 'FreeEnv'.)
data OccursExtra = OccursExtra
  { occUnfold  :: UnfoldStrategy
  , occVars    :: VarMap          -- ^ The allowed variables with their variance.
  , occMeta    :: MetaId          -- ^ The meta we want to solve.
  , occCxtSize :: Nat             -- ^ The size of the typing context upon invocation.
  }

type OccursCtx  = FreeEnv' () OccursExtra AllowedVar
type OccursM    = ReaderT OccursCtx TCM

-- ** Modality handling.

-- | The passed modality is the one of the current context.
type AllowedVar = Modality -> All

instance IsVarSet () AllowedVar where
  withVarOcc o f = f . composeModality (getModality o)

-- | Check whether a free variable is allowed in the context as
--   specified by the modality.
variableCheck :: VarMap -> Maybe Variable -> AllowedVar
variableCheck xs mi q = All $
  -- Bound variables are always allowed to occur:
  caseMaybe mi True $ \ i ->
    -- Free variables not listed in @xs@ are forbidden:
    caseMaybe (lookupVarMap i xs) False $ \ o ->
      -- For listed variables it holds:
      -- The ascribed modality @o@ must be submodality of the
      -- modality @q@ of the current context.
      -- E.g. irrelevant variables (ascribed, lhs) can only
      -- be used in irrelevant position (rhs).
      getModality o `moreUsableModality` q

-- | Occurs check fails if a defined name is not available
--   since it was declared in irrelevant or erased context.
definitionCheck :: QName -> OccursM ()
definitionCheck d = do
  cxt <- ask
  let irr = isIrrelevant cxt
      er  = hasQuantity0 cxt
      m   = occMeta $ feExtra cxt
  -- Anything goes if we are both irrelevant and erased.
  -- Otherwise, have to check the modality of the defined name.
  unless (irr && er) $ getConstInfo' d >>= \case
   Left _ -> do
    -- Andreas, 2021-07-29.
    -- The definition is not in scope.
    -- This shouldn't happen, but does so in issue #5492.
    -- Let's bail out...
    patternViolation' alwaysUnblock 35 $
      unwords ["occursCheck: definition", prettyShow d, "not in scope" ]
   Right def -> do
    let dmod = getModality def
    unless (irr || usableRelevance dmod) $ do
      reportSDoc "tc.meta.occurs" 35 $ hsep
        [ "occursCheck: definition"
        , prettyTCM d
        , "has relevance"
        , text . show $ getRelevance dmod
        ]
      abort neverUnblock $ MetaIrrelevantSolution m $ Def d []
    unless (er || usableQuantity dmod) $ do
      reportSDoc "tc.meta.occurs" 35 $ hsep
        [ "occursCheck: definition"
        , prettyTCM d
        , "has quantity"
        , text . show $ getQuantity dmod
        ]
      abort neverUnblock $ MetaErasedSolution m $ Def d []

metaCheck :: MetaId -> OccursM MetaId
metaCheck m = do
  cxt <- ask
  let rel = getRelevance cxt
      qnt = getQuantity cxt
      m0  = occMeta $ feExtra cxt

  -- Check for loop
  --   don't fail hard on this, since we might still be on the top-level
  --   after some killing (Issue 442)
  --
  -- Andreas, 2013-02-18  Issue 795 demonstrates that a recursive
  -- occurrence of a meta could be solved by the identity.
  --   ? (Q A) = Q (? A)
  -- So, do not throw an error.
  -- I guess the error was there from times when occurrence check
  -- was done after the "lhs=linear variables" check, but now
  -- occurrence check comes first.
  -- WAS:
  -- when (m == m') $ if ctx == Top then patternViolation else
  --   abort ctx $ MetaOccursInItself m'
  when (m == m0) $ patternViolation' neverUnblock 50 $ "occursCheck failed: Found " ++ prettyShow m

  mv <- lookupLocalMeta m
  let mmod = getModality mv
      mmod' = setRelevance rel $ setQuantity qnt $ mmod
  if (mmod `moreUsableModality` mmod') then return m else do
    reportSDoc "tc.meta.occurs" 35 $ hsep
      [ "occursCheck: meta variable"
      , prettyTCM m
      , "has relevance"
      , text . show $ getRelevance mmod
      , "and quantity"
      , text . show $ getQuantity mmod
      ]
    allowAssign <- asksTC envAssignMetas
    -- Jesper, 2020-11-10: if we encounter a metavariable that is
    -- unusable because of its modality (e.g. irrelevant or erased) we
    -- try to *promote* the meta to the required modality, by creating
    -- a new meta with that modality and solving the old one with
    -- it. Don't do this if the meta occurs in a flexible or unguarded
    -- position:
    -- - If it is in a flexible position, it could disappear when
    --   another meta is solved, so promotion is maybe not necessary.
    -- - If it is in a top-level position, we can instead solve the
    --   equation by instantiating the other way around, so promotion
    --   is not necessary.
    let fail reason = do
          reportSDoc "tc.meta.occurs" 20 $ "Meta occurs check found bad relevance"
          reportSDoc "tc.meta.occurs" 20 $ "aborting because" <+> reason
          patternViolation $ unblockOnMeta m
    when (mvFrozen mv == Frozen)             $ fail "meta is frozen"
    unless (isOpenMeta $ mvInstantiation mv) $ fail "meta is already solved"
    unless allowAssign                       $ fail "assigning metas is not allowed here"
    when (isFlexible cxt)                    $ fail "occurrence is flexible"
    when (isUnguarded cxt)                   $ fail "occurrence is unguarded"

    reportSDoc "tc.meta.occurs" 20 $ "Promoting meta" <+> prettyTCM m <+> "to modality" <+> prettyTCM mmod'
    updateMetaVar m $ \ mv -> mv { mvInfo = setModality mmod' $ mvInfo mv }
    etaExpandListeners m
    wakeupConstraints m
    return m

-- | Construct a test whether a de Bruijn index is allowed
--   or needs to be pruned.
allowedVars :: OccursM (Nat -> Bool)
allowedVars = do
  -- @n@ is the number of binders we have stepped under.
  n  <- liftM2 (-) getContextSize (asks (occCxtSize . feExtra))
  xs <- asks (theVarMap . occVars . feExtra)
  -- Bound variables are allowed, and those mentioned in occVars.
  return $ \ i -> i < n || (i - n) `IntMap.member` xs

-- ** Unfolding during occurs check.

-- | Unfold definitions during occurs check?
--   This effectively runs the occurs check on the normal form.
data UnfoldStrategy = YesUnfold | NoUnfold
  deriving (Eq, Show)

defArgs :: OccursM a -> OccursM a
defArgs m = asks (occUnfold . feExtra) >>= \case
  NoUnfold  -> flexibly m
  YesUnfold -> weakly m

-- | For a path constructor `c : ... -> Path D a b`, we have that e.g. `c es i0` reduces to `a`.
--   So we have to consider its arguments as flexible when we do not actually unfold.
conArgs :: Elims -> OccursM a -> OccursM a
conArgs es m = asks (occUnfold . feExtra) >>= \case
  YesUnfold -> m
  NoUnfold | null [ () | IApply{} <- es ]
            -> m
  NoUnfold  -> flexibly m

unfoldB :: (Instantiate t, Reduce t) => t -> OccursM (Blocked t)
unfoldB v = do
  unfold <- asks $ occUnfold . feExtra
  rel    <- asks feModality
  case unfold of
    YesUnfold | not (isIrrelevant rel) -> reduceB v
    _                                  -> notBlocked <$> instantiate v

unfold :: (Instantiate t, Reduce t) => t -> OccursM t
unfold v = asks (occUnfold . feExtra) >>= \case
  NoUnfold  -> instantiate v
  YesUnfold -> reduce v

-- ** Managing rigidiy during occurs check.

-- | Leave the strongly rigid position.
weakly :: OccursM a -> OccursM a
weakly = local $ over lensFlexRig $ composeFlexRig WeaklyRigid

strongly :: OccursM a -> OccursM a
strongly = local $ over lensFlexRig $ \case
  WeaklyRigid -> StronglyRigid
  Unguarded   -> StronglyRigid
  ctx -> ctx

flexibly :: OccursM a -> OccursM a
flexibly = local $ set lensFlexRig $ Flexible ()

-- ** Error throwing during occurs check.

patternViolation' :: MonadTCM m => Blocker -> Int -> String -> m a
patternViolation' unblock n err = liftTCM $ do
  reportSLn "tc.meta.occurs" n err
  patternViolation unblock

abort :: Blocker -> TypeError -> OccursM a
abort unblock err = do
  ctx <- ask
  lift $ do
    if | isIrrelevant ctx                    -> soft
       | StronglyRigid <- ctx ^. lensFlexRig -> hard
       | otherwise -> soft
  where
  hard = typeError err -- here, throw an uncatchable error (unsolvable constraint)
  soft = patternViolation' unblock 70 (show err) -- throws a PatternErr, which leads to delayed constraint

---------------------------------------------------------------------------
-- * Implementation of the occurs check.

-- | Extended occurs check.
class Occurs t where
  occurs :: t -> TypeOf t -> OccursM t
  metaOccurs :: MetaId -> t -> TCM ()  -- raise exception if meta occurs in t

  default metaOccurs :: (Foldable f, Occurs a, f a ~ t) => MetaId -> t -> TCM ()
  metaOccurs = traverse_ . metaOccurs

occurs_ :: (Occurs t, TypeOf t ~ ()) => t -> OccursM t
occurs_ t = occurs t ()

metaOccurs2 :: (Occurs a, Occurs b) => MetaId -> a -> b -> TCM ()
metaOccurs2 m x y = metaOccurs m x >> metaOccurs m y

metaOccurs3 :: (Occurs a, Occurs b, Occurs c) => MetaId -> a -> b -> c -> TCM ()
metaOccurs3 m x y z = metaOccurs m x >> metaOccurs m y >> metaOccurs m z

-- | When assigning @m xs := v@, check that @m@ does not occur in @v@
--   and that the free variables of @v@ are contained in @xs@.
occursCheck
  :: MetaId -> VarMap -> Term -> CompareAs -> TCM Term
occursCheck m xs v cmpAs = Bench.billTo [ Bench.Typing, Bench.OccursCheck ] $ do
  mv <- lookupLocalMeta m
  n  <- getContextSize
  ty <- case cmpAs of
    AsTermsOf ty -> return ty
    AsSizes      -> sizeType
    AsTypes      -> return $ sort __DUMMY_SORT__
  reportSDoc "tc.meta.occurs" 65 $ "occursCheck" <+> pretty m <+> text (show xs)
  let initEnv unf = FreeEnv
        {  feExtra = OccursExtra
          { occUnfold  = unf
          , occVars    = xs
          , occMeta    = m
          , occCxtSize = n
          }
        , feFlexRig   = StronglyRigid -- ? Unguarded
        , feModality  = getModality mv
        , feSingleton = variableCheck xs
        }
  initOccursCheck mv
  nicerErrorMessage $ do
    -- First try without normalising the term
    (occurs v ty `runReaderT` initEnv NoUnfold) `catchError` \err -> do
      -- If first run is inconclusive, try again with normalization
      -- (unless metavariable is irrelevant, in which case the
      -- constraint will anyway be dropped)
      case err of
        PatternErr{} | not (isIrrelevant $ getModality mv) -> do
          initOccursCheck mv
          occurs v ty `runReaderT` initEnv YesUnfold
        _ -> throwError err

  where
    -- Produce nicer error messages
    nicerErrorMessage :: TCM a -> TCM a
    nicerErrorMessage f = f `catchError` \ err -> case err of
      TypeError _ _ cl -> case clValue cl of
        MetaOccursInItself{} ->
          typeError . GenericDocError =<<
            fsep [ text "Refuse to construct infinite term by instantiating"
                 , prettyTCM m
                 , "to"
                 , prettyTCM =<< instantiateFull v
                 ]
        MetaCannotDependOn _ i ->
          ifM (isSortMeta m `and2M` (not <$> hasUniversePolymorphism))
          ( typeError . GenericDocError =<<
            fsep [ text "Cannot instantiate the metavariable"
                 , prettyTCM m
                 , "to"
                 , prettyTCM v
                 , "since universe polymorphism is disabled"
                 ]
          ) {- else -}
          ( typeError . GenericDocError =<<
              fsep [ text "Cannot instantiate the metavariable"
                   , prettyTCM m
                   , "to solution"
                   , prettyTCM v
                   , "since it contains the variable"
                   , enterClosure cl $ \_ -> prettyTCM (Var i [])
                   , "which is not in scope of the metavariable"
                   ]
            )
        MetaIrrelevantSolution _ _ ->
          typeError . GenericDocError =<<
            fsep [ text "Cannot instantiate the metavariable"
                 , prettyTCM m
                 , "to solution"
                 , prettyTCM v
                 , "since (part of) the solution was created in an irrelevant context"
                 ]
        MetaErasedSolution _ _ ->
          typeError . GenericDocError =<<
            fsep [ text "Cannot instantiate the metavariable"
                 , prettyTCM m
                 , "to solution"
                 , prettyTCM v
                 , "since (part of) the solution was created in an erased context"
                 ]
        _ -> throwError err
      _ -> throwError err

instance Occurs Term where
  occurs v ty = do
    vb  <- unfoldB v
    singTy <- runBlocked $ isSingletonType ty
    let tyBlock = fromLeft (const neverUnblock) singTy
        block = unblockOnEither (getBlocker vb) tyBlock
        -- On a failure, we should retry when any meta that is blocking
        -- either the term or the type is solved.
        flexIfBlocked = if
          -- In the metavariable case we should not yet become flexible
          -- because otherwise pruning won't fire.
          | MetaV{} <- ignoreBlocking vb -> addOrUnblocker block
          | block /= neverUnblock -> flexibly . addOrUnblocker block
          -- Re #3594, do not fail hard when Underapplied:
          -- the occurrence could be computed away after eta expansion.
          | NotBlocked{blockingStatus = Underapplied} <- vb -> flexibly
          | otherwise -> id
    v <- reduceProjectionLike $ ignoreBlocking vb
    ifJust (fromRight (const Nothing) singTy) return $ do
    flexIfBlocked $ do
        ctx <- ask
        let m = occMeta . feExtra $ ctx
        reportSDoc "tc.meta.occurs" 45 $
          text ("occursCheck " ++ prettyShow m ++ " (" ++ show (feFlexRig ctx) ++ ") of ") <+> prettyTCM v <+> ":" <+> prettyTCM ty
        reportSDoc "tc.meta.occurs" 70 $
          nest 2 $ pretty v
        case v of
          Var i es   -> do
            allowed <- getAll . ($ unitModality) <$> variable i
            a <- typeOfBV i
            if allowed then Var i <$> weakly (occurs es (a, Var i)) else do
              -- if the offending variable is of singleton type,
              -- eta-expand it away
              reportSDoc "tc.meta.occurs" 35 $ "offending variable: " <+> prettyTCM (var i)
              t <-  typeOfBV i
              reportSDoc "tc.meta.occurs" 35 $ nest 2 $ "of type " <+> prettyTCM t
              isST <- isSingletonType t
              reportSDoc "tc.meta.occurs" 35 $ nest 2 $ "(after singleton test)"
              case isST of
                -- not a singleton type
                Nothing ->
                  -- #4480: Only hard fail if the variable is not in scope. Wrong modality/relevance
                  -- could potentially be salvaged by eta expansion.
                  ifM (($ i) <$> allowedVars) -- vv TODO: neverUnblock is not correct! What could trigger this eta expansion though?
                      (patternViolation' neverUnblock 70 $ "Disallowed var " ++ show i ++ " due to modality/relevance")
                      (strongly $ abort neverUnblock $ MetaCannotDependOn m i)
                -- is a singleton type with unique inhabitant sv
                (Just sv) -> return $ sv `applyE` es
          Lam h f     -> do
            ab <- shouldBePiOrPath ty
            Lam h <$> occurs f ab
          Level l     -> Level <$> occurs_ l
          Lit l       -> return v
          Dummy{}     -> return v
          DontCare v  -> dontCare <$> do underRelevance Irrelevant $ occurs v ty
          Def d es    -> do
            definitionCheck d
            Def d <$> occDef d es
          Con c ci vs -> do
            definitionCheck (conName c)
            reportSDoc "tc.meta.occurs" 45 $ "occursCheck: constructor at type" <+> prettyTCM ty
            let fail = do
                  reportSDoc "impossible" 10 $ vcat
                    [ "Bad type for constructor" <+> prettyTCM c <+> ":"
                    , nest 2 $ prettyTCM ty
                    ]
                  -- Jesper, 2023-03-01: this should really be __IMPOSSIBLE__, but
                  -- currently it is not due to primPOr.
                  -- (see https://github.com/agda/agda/issues/5837#issuecomment-1448757002)
                  patternViolation neverUnblock
            (_, ct) <- fromMaybeM fail (getConType c ty)
            Con c ci <$> conArgs vs (occurs vs (ct , Con c ci))  -- if strongly rigid, remain so, except with unreduced IApply arguments.
          Pi a b      -> Pi <$> occurs_ a <*> occurs b a
          Sort s      -> Sort <$> do underRelevance NonStrict $ occurs_ s
          MetaV m' es -> do
            m' <- metaCheck m'
            mt <- metaType m'
            -- The arguments of a meta are in a flexible position
            (MetaV m' <$> do flexibly $ occurs es (mt, MetaV m')) `catchError` \ err -> do
                ctx <- ask
                reportSDoc "tc.meta.kill" 25 $ vcat
                  [ text $ "error during flexible occurs check, we are " ++ show (ctx ^. lensFlexRig)
                  , text $ show err
                  ]
                case err of
                  -- On pattern violations try to remove offending
                  -- flexible occurrences (if not already in a flexible context)
                  PatternErr{} | not (isFlexible ctx) -> do
                    reportSLn "tc.meta.kill" 20 $
                      "oops, pattern violation for " ++ prettyShow m'
                    -- Andreas, 2014-03-02, see issue 1070:
                    -- Do not prune when meta is projected!
                    caseMaybe (allApplyElims es) (throwError err) $ \ vs -> do
                      killResult <- lift . prune m' vs =<< allowedVars
                      if (killResult == PrunedEverything) then do
                        -- after successful pruning, restart occurs check
                        reportSDoc "tc.meta.prune" 40 $ "Pruned everything"
                        v' <- instantiate (MetaV m' es)
                        occurs v' ty
                      else throwError err
                  _ -> throwError err
          where
            -- a data or record type constructor propagates strong occurrences
            -- since e.g. x = List x is unsolvable
            occDef d vs = do
              m   <- asks (occMeta . feExtra)
              lift $ metaOccurs m d
              dt <- computeDefType d vs
              ifM (liftTCM $ isJust <$> isDataOrRecordType d)
                {-then-} (occurs vs (dt, Def d))
                {-else-} (defArgs $ occurs vs (dt, Def d))

  metaOccurs m v = do
    v <- instantiate v
    case v of
      Var i vs   -> metaOccurs m vs
      Lam h f    -> metaOccurs m f
      Level l    -> metaOccurs m l
      Lit l      -> return ()
      Dummy{}    -> return ()
      DontCare v -> metaOccurs m v
      Def d vs   -> metaOccurs2 m d vs
      Con c _ vs -> metaOccurs m vs
      Pi a b     -> metaOccurs2 m a b
      Sort s     -> metaOccurs m s              -- vv m is already an unblocker
      MetaV m' vs | m == m'   -> patternViolation' neverUnblock 50 $ "Found occurrence of " ++ prettyShow m
                  | otherwise -> addOrUnblocker (unblockOnMeta m') $ metaOccurs m vs

instance Occurs QName where
  occurs d = __IMPOSSIBLE__

  metaOccurs m d = whenM (defNeedsChecking d) $ do
    tallyDef d
    reportSDoc "tc.meta.occurs" 30 $ "Checking for occurrences in " <+> prettyTCM d
    metaOccursQName m d

metaOccursQName :: MetaId -> QName -> TCM ()
metaOccursQName m x = metaOccurs m . theDef =<< do
  ignoreAbstractMode $ getConstInfo x
  -- Andreas, 2019-05-03, issue #3742:
  -- ignoreAbstractMode necessary, as abstract
  -- constructors are also called up.

instance Occurs Defn where
  occurs def = __IMPOSSIBLE__

  metaOccurs m Axiom{}                      = return ()
  metaOccurs m DataOrRecSig{}               = return ()
  metaOccurs m Function{ funClauses = cls } = traverse_ (metaOccurs m) cls
  -- since a datatype is isomorphic to the sum of its constructor types
  -- we check the constructor types
  metaOccurs m Datatype{ dataCons = cs }    = mapM_ (metaOccursQName m) cs
  metaOccurs m Record{ recConHead = c }     = metaOccursQName m $ conName c
  metaOccurs m Constructor{}                = return ()
  metaOccurs m Primitive{}                  = return ()
  metaOccurs m PrimitiveSort{}              = __IMPOSSIBLE__
  metaOccurs m AbstractDefn{}               = __IMPOSSIBLE__
  metaOccurs m GeneralizableVar{}           = __IMPOSSIBLE__

instance Occurs Clause where
  occurs cl = __IMPOSSIBLE__

  metaOccurs m cl = whenJust (clauseBody cl) $ metaOccurs m

instance Occurs Level where
  occurs (Max n as) _ = Max n <$> traverse occurs_ as

  metaOccurs m (Max _ as) =
    addOrUnblocker (unblockOnAnyMetaIn as) $ traverse_ (metaOccurs m) as
    -- TODO: Should only be blocking metas in as. But any meta that can
    --       let the Max make progress needs to be included. For instance,
    --       _1 ⊔ _2 = _1 should unblock on _2, even though _1 is the meta
    --       failing occurs check.

instance Occurs PlusLevel where
  occurs (Plus n l) _ = do
    lt <- levelType'
    Plus n <$> occurs l lt

  metaOccurs m (Plus n l) = metaOccurs m l

instance Occurs Type where
  occurs (El s v) _ = El <$> occurs_ s <*> occurs v (sort s)

  metaOccurs m (El s v) = metaOccurs2 m s v

instance Occurs Sort where
  occurs s _ = do
    unfold s >>= \case
      PiSort a s1 s2 -> do
        s1' <- flexibly $ occurs_ s1
        a'  <- (a $>) <$> do flexibly $ occurs (unDom a) (sort s1')
        s2' <- mapAbstraction (El s1' <$> a') (flexibly . underBinder . occurs_) s2
        return $ PiSort a' s1' s2'
      FunSort s1 s2 -> FunSort <$> flexibly (occurs_ s1) <*> flexibly (occurs_ s2)
      Univ u a   -> Univ u <$> occurs_ a
      s@Inf{}    -> return s
      s@SizeUniv -> return s
      s@LockUniv -> return s
      s@LevelUniv -> return s
      s@IntervalUniv -> return s
      UnivSort s -> UnivSort <$> do flexibly $ occurs_ s
      MetaS x es -> do
        MetaV x es <- occurs (MetaV x es) (sort $ univSort s)
        return $ MetaS x es
      DefS x es -> do
        Def x es <- occurs (Def x es) (sort $ univSort s)
        return $ DefS x es
      DummyS{}   -> return s

  metaOccurs m s = do
    s <- instantiate s
    case s of
      PiSort a s1 s2 -> do
        metaOccurs m a
        metaOccurs m s1
        metaOccurs m (absBody s2)
      FunSort s1 s2 -> metaOccurs2 m s1 s2
      Univ _ a   -> metaOccurs m a
      Inf _ _    -> return ()
      SizeUniv   -> return ()
      LockUniv   -> return ()
      LevelUniv  -> return ()
      IntervalUniv -> return ()
      UnivSort s -> metaOccurs m s
      MetaS x es -> metaOccurs m $ MetaV x es
      DefS d es  -> metaOccurs m $ Def d es
      DummyS{}   -> return ()

instance Occurs Elims where
  occurs []     _      = return []
  occurs (e:es) (t,hd) = do
    (e',t') <- case e of
      (Proj o f)     -> do
        definitionCheck f
        t' <- shouldBeProjectible (hd []) t o f
        return (e, t')
      (Apply u)      -> do
        (a,b) <- shouldBePi t
        u' <- occurs u a
        return (Apply u' , absApp b (unArg u'))
      (IApply x y u) -> do
        (a, b) <- shouldBePiOrPath t -- TODO: using shouldBePath here causes errors in cubical library
        izero <- primIZero
        ione  <- primIOne
        x' <- occurs x (b `absApp` izero)
        y' <- occurs y (b `absApp` ione)
        u' <- occurs u (unDom a)
        return (IApply x' y' u' , b `absApp` u')
    (e':) <$> occurs es (t' , hd . (e':))

  metaOccurs m es = forM_ es $ \case
    Proj{} -> return ()
    Apply a -> metaOccurs m a
    IApply x y a -> metaOccurs3 m x y a

instance Occurs (Abs Term) where
  occurs (NoAbs s x) (a,b) = NoAbs s <$> occurs x (strengthen __IMPOSSIBLE__ $ absBody b)
  occurs x (a,b) = mapAbstraction a (\body -> underBinder $ occurs body (absBody b)) x

  metaOccurs m (Abs   _ x) = metaOccurs m x
  metaOccurs m (NoAbs _ x) = metaOccurs m x

instance Occurs (Abs Type) where
  occurs (NoAbs s x) _ = NoAbs s <$> occurs_ x
  occurs x a = mapAbstraction a (\body -> underBinder $ occurs_ body) x

  metaOccurs m (Abs   _ x) = metaOccurs m x
  metaOccurs m (NoAbs _ x) = metaOccurs m x

instance Occurs a => Occurs (Arg a) where
  occurs (Arg info v) t = Arg info <$> do underModality info $ occurs v (unDom t)
  metaOccurs m = metaOccurs m . unArg

instance Occurs a => Occurs (Dom a) where
  occurs :: Occurs a => Dom a -> TypeOf (Dom a) -> OccursM (Dom a)
  occurs v t = traverse (`occurs` t) v

---------------------------------------------------------------------------
-- * Pruning: getting rid of flexible occurrences.

-- | @prune m' vs xs@ attempts to remove all arguments from @vs@ whose
--   free variables are not contained in @xs@.
--   If successful, @m'@ is solved by the new, pruned meta variable and we
--   return @True@ else @False@.
--
--   Issue 1147:
--   If any of the meta args @vs@ is matchable, e.g., is a constructor term,
--   we cannot prune, because the offending variables could be removed by
--   reduction for a suitable instantiation of the meta variable.
prune
  :: (PureTCM m, MonadMetaSolver m)
  => MetaId         -- ^ Meta to prune.
  -> Args           -- ^ Arguments to meta variable.
  -> (Nat -> Bool)  -- ^ Test for allowed variable (de Bruijn index).
  -> m PruneResult
prune m' vs xs = do
  caseEitherM (runExceptT $ mapM ((hasBadRigid xs) . unArg) vs)
    (const $ return PrunedNothing) $ \ kills -> do
    reportSDoc "tc.meta.kill" 10 $ vcat
      [ "attempting kills"
      , nest 2 $ vcat
        [ "m'    =" <+> pretty m'
        -- , "xs    =" <+> prettyList (map (prettyTCM . var) xs)  -- no longer printable
        , "vs    =" <+> prettyList (map prettyTCM vs)
        , "kills =" <+> text (show kills)
        ]
      ]
    killArgs kills m'

-- | @hasBadRigid xs v = Just True@ iff one of the rigid variables in @v@ is not in @xs@.
--   Actually we can only prune if a bad variable is in the head. See issue 458.
--   Or in a non-eliminateable position (see succeed/PruningNonMillerPattern).
--
--   @hasBadRigid xs v = Nothing@ means that
--   we cannot prune at all as one of the meta args is matchable.
--   (See issue 1147.)
hasBadRigid
  :: PureTCM m
  => (Nat -> Bool)      -- ^ Test for allowed variable (de Bruijn index).
  -> Term               -- ^ Argument of meta variable.
  -> ExceptT () m Bool  -- ^ Exception if argument is matchable.
hasBadRigid xs t = do
  -- We fail if we encounter a matchable argument.
  let failure = throwError ()
  tb <- reduceB t
  let t = ignoreBlocking tb
  case t of
    Var x _      -> return $ not $ xs x
    -- Issue 1153: A lambda has to be considered matchable.
    -- Lam _ v    -> hasBadRigid (0 : map (+1) xs) (absBody v)
    Lam _ v      -> failure
    DontCare v   -> hasBadRigid xs v
    -- The following types of arguments cannot be eliminated by a pattern
    -- match: data, record, Pi, levels, sorts
    -- Thus, their offending rigid variables are bad.
    v@(Def f es) -> ifNotM (isNeutral tb f es) failure $ {- else -} do
      lift $ es `rigidVarsNotContainedIn` xs
    -- Andreas, 2012-05-03: There is room for further improvement.
    -- We could also consider a defined f which is not blocked by a meta.
    Pi a b       -> lift $ (a,b) `rigidVarsNotContainedIn` xs
    Level v      -> lift $ v `rigidVarsNotContainedIn` xs
    Sort s       -> lift $ s `rigidVarsNotContainedIn` xs
    -- Since constructors can be eliminated by pattern-matching,
    -- offending variables under a constructor could be removed by
    -- the right instantiation of the meta variable.
    -- Thus, they are not rigid.
    Con c _ es | Just args <- allApplyElims es -> do
      ifM (isEtaCon (conName c))
        -- in case of a record con, we can in principle prune
        -- (but not this argument; the meta could become a projection!)
        (and <$> mapM (hasBadRigid xs . unArg) args)  -- not andM, we need to force the exceptions!
        failure
    Con c _ es | otherwise -> failure
    Lit{}        -> failure -- matchable
    MetaV{}      -> failure -- potentially matchable
    Dummy{}      -> return False

-- | Check whether a term @Def f es@ is finally stuck.
--   Currently, we give only a crude approximation.
isNeutral :: (HasConstInfo m) => Blocked t -> QName -> Elims -> m Bool
isNeutral b f es = do
  let yes = return True
      no  = return False
  def <- getConstInfo f
  if not (null $ defMatchable def) then no else do
  case theDef def of
    AbstractDefn{} -> yes
    Axiom{}    -> yes
    Datatype{} -> yes
    Record{}   -> yes
    Function{} -> case b of
      NotBlocked StuckOn{}   _ -> yes
      NotBlocked AbsurdMatch _ -> yes
      _                        -> no
    GeneralizableVar{} -> __IMPOSSIBLE__
    _          -> no

-- | Check whether any of the variables (given as de Bruijn indices)
--   occurs *definitely* in the term in a rigid position.
--   Reduces the term successively to remove variables in dead subterms.
--   This fixes issue 1386.
rigidVarsNotContainedIn
  :: (PureTCM m, AnyRigid a)
  => a
  -> (Nat -> Bool)   -- ^ Test for allowed variable (de Bruijn index).
  -> m Bool
rigidVarsNotContainedIn v is = do
  n0 <- getContextSize
  let -- allowed variables as de Bruijn levels
      levels = is . (n0-1 -)
      -- test if index is forbidden by converting it to level
      test i = do
        n <- getContextSize
        -- get de Bruijn level for i
        let l = n-1 - i
            -- If l >= n0 then it is a bound variable and can be
            -- ignored.  Otherwise, it has to be in the allowed levels.
            forbidden = l < n0 && not (levels l)
        when forbidden $
          reportSLn "tc.meta.kill" 20 $
            "found forbidden de Bruijn level " ++ show l
        return forbidden
  anyRigid test v

-- | Collect the *definitely* rigid variables in a monoid.
--   We need to successively reduce the expression to do this.

class AnyRigid a where
  anyRigid :: (PureTCM tcm)
           => (Nat -> tcm Bool) -> a -> tcm Bool

instance AnyRigid Term where
  anyRigid f t = do
    b <- reduceB t
    case ignoreBlocking b of
      -- Upon entry, we are in rigid position, thus,
      -- bound variables are rigid ones.
      Var i es   -> f i `or2M` anyRigid f es
      Lam _ t    -> anyRigid f t
      Lit{}      -> return False
      Def _ es   -> case b of
        -- If the definition is blocked by a meta, its arguments
        -- may be in flexible positions.
        Blocked{}                   -> return False
        -- If the definition is incomplete, arguments might disappear
        -- by reductions that come with more clauses, thus, these
        -- arguments are not rigid.
        NotBlocked (MissingClauses _) _ -> return False
        -- _        -> mempty -- breaks: ImproveInertRHS, Issue442, PruneRecord, PruningNonMillerPattern
        _        -> anyRigid f es
      Con _ _ ts -> anyRigid f ts
      Pi a b     -> anyRigid f (a,b)
      Sort s     -> anyRigid f s
      Level l    -> anyRigid f l
      MetaV{}    -> return False
      DontCare{} -> return False
      Dummy{}    -> return False

instance AnyRigid Type where
  anyRigid f (El s t) = anyRigid f (s,t)

instance AnyRigid Sort where
  anyRigid f s =
    case s of
      Univ _ l   -> anyRigid f l
      Inf _ _    -> return False
      SizeUniv   -> return False
      LockUniv   -> return False
      LevelUniv  -> return False
      IntervalUniv -> return False
      PiSort a s1 s2 -> return False
      FunSort s1 s2 -> return False
      UnivSort s -> anyRigid f s
      MetaS{}    -> return False
      DefS{}     -> return False
      DummyS{}   -> return False

instance AnyRigid Level where
  anyRigid f (Max _ ls) = anyRigid f ls

instance AnyRigid PlusLevel where
  anyRigid f (Plus _ l)    = anyRigid f l

instance (Subst a, AnyRigid a) => AnyRigid (Abs a) where
  anyRigid f b = underAbstraction_ b $ anyRigid f

instance AnyRigid a => AnyRigid (Arg a) where
  anyRigid f a =
    case getRelevance a of
      -- Irrelevant arguments are definitionally equal to
      -- values, so the variables there are not considered
      -- "definitely rigid".
      Irrelevant -> return False
      _          -> anyRigid f $ unArg a

instance AnyRigid a => AnyRigid (Dom a) where
  anyRigid f dom = anyRigid f $ unDom dom

instance AnyRigid a => AnyRigid (Elim' a) where
  anyRigid f (Apply a)      = anyRigid f a
  anyRigid f (IApply x y a) = anyRigid f (x,(y,a))
  anyRigid f Proj{}         = return False

instance AnyRigid a => AnyRigid [a] where
  anyRigid f xs = anyM xs $ anyRigid f

instance (AnyRigid a, AnyRigid b) => AnyRigid (a,b) where
  anyRigid f (a,b) = anyRigid f a `or2M` anyRigid f b


data PruneResult
  = NothingToPrune   -- ^ the kill list is empty or only @False@s
  | PrunedNothing    -- ^ there is no possible kill (because of type dep.)
  | PrunedSomething  -- ^ managed to kill some args in the list
  | PrunedEverything -- ^ all prescribed kills where performed
    deriving (Eq, Show)

-- | @killArgs [k1,...,kn] X@ prunes argument @i@ from metavar @X@ if @ki==True@.
--   Pruning is carried out whenever > 0 arguments can be pruned.
killArgs :: (MonadMetaSolver m) => [Bool] -> MetaId -> m PruneResult
killArgs kills _
  | not (or kills) = return NothingToPrune  -- nothing to kill
killArgs kills m = do
  mv <- lookupLocalMeta m
  allowAssign <- asksTC envAssignMetas
  if mvFrozen mv == Frozen || not allowAssign then return PrunedNothing else do
      -- Andreas 2011-04-26, we allow pruning in MetaV and MetaS
      let a = jMetaType $ mvJudgement mv
      TelV tel b <- telView' <$> instantiateFull a
      let args         = zip (telToList tel) (kills ++ repeat False)
      (kills', a') <- killedType args b
      dbg kills' a a'
      -- If there is any prunable argument, perform the pruning
      if not (any unArg kills') then return PrunedNothing else do
        addContext tel $ performKill kills' m a'
        -- Only successful if all occurrences were killed
        -- Andreas, 2011-05-09 more precisely, check that at least
        -- the in 'kills' prescribed kills were carried out
        return $ if (and $ zipWith implies kills $ map unArg kills')
                   then PrunedEverything
                   else PrunedSomething
  where
    implies :: Bool -> Bool -> Bool
    implies False _ = True
    implies True  x = x
    dbg kills' a a' =
      reportSDoc "tc.meta.kill" 10 $ vcat
        [ "after kill analysis"
        , nest 2 $ vcat
          [ "metavar =" <+> prettyTCM m
          , "kills   =" <+> text (show kills)
          , "kills'  =" <+> prettyList (map prettyTCM kills')
          , "oldType =" <+> prettyTCM a
          , "newType =" <+> prettyTCM a'
          ]
        ]

-- | @killedType [((x1,a1),k1)..((xn,an),kn)] b = ([k'1..k'n],t')@
--   (ignoring @Dom@).  Let @t' = (xs:as) -> b@.
--   Invariant: @k'i == True@ iff @ki == True@ and pruning the @i@th argument from
--   type @b@ is possible without creating unbound variables.
--   @t'@ is type @t@ after pruning all @k'i==True@.
killedType :: (MonadReduce m) => [(Dom (ArgName, Type), Bool)] -> Type -> m ([Arg Bool], Type)
killedType args b = do

  let n = length args
  let iargs = zip (downFrom n) args

  -- Turn list of bools into an IntSet containing the variables we want to kill
  -- (indices relative to b).
  let tokill = IntSet.fromList [ i | (i, (_, True)) <- iargs ]

  -- First, check the free variables of b to see if they prevent any kills.
  (tokill, b) <- reallyNotFreeIn tokill b

  -- Then recurse over the telescope (right-to-left), building up the final type.
  (killed, b) <- go (reverse $ map fst args) tokill b

  -- Turn the IntSet of killed variables into the list of Arg Bool's to return.
  let kills = [ Arg (getArgInfo dom) (IntSet.member i killed)
              | (i, (dom, _)) <- iargs ]
  return (kills, b)
  where
    down = IntSet.map pred
    up   = IntSet.map succ

    -- go Δ xs B
    -- Invariants:
    --   - Δ ⊢ B
    --   - Δ is represented as a list in right-to-left order
    --   - xs are deBruijn indices into Δ
    --   - xs ∩ FV(B) = Ø
    -- Result: (ys, Δ' → B')
    --    where Δ' ⊆ Δ  (possibly reduced to remove dependencies, see #3177)
    --          ys ⊆ xs are the variables that were dropped from Δ
    --          B' = strengthen ys B
    go :: (MonadReduce m) => [Dom (ArgName, Type)] -> IntSet -> Type -> m (IntSet, Type)
    go [] xs b | IntSet.null xs = return (xs, b)
               | otherwise      = __IMPOSSIBLE__
    go (arg : args) xs b  -- go (Δ (x : A)) xs B, (x = deBruijn index 0)
      | IntSet.member 0 xs = do
          -- Case x ∈ xs. We know x ∉ FV(B), so we can safely drop x from the
          -- telescope. Drop x from xs (and shift indices) and recurse with
          -- `strengthen x B`.
          let ys = down (IntSet.delete 0 xs)
          (ys, b) <- go args ys $ strengthen impossible b
          -- We need to return a set of killed variables relative to Δ (x : A), so
          -- shift ys and add x back in.
          return (IntSet.insert 0 $ up ys, b)
      | otherwise = do
          -- Case x ∉ xs. We either can't or don't want to get rid of x. In
          -- this case we have to check A for potential dependencies preventing
          -- us from killing variables in xs.
          let xs'       = down xs -- Shift to make relative to Δ ⊢ A
              (name, a) = unDom arg
          (ys, a) <- reallyNotFreeIn xs' a
          -- Recurse on Δ, ys, and (x : A') → B, where A reduces to A' and ys ⊆ xs'
          -- not free in A'. We already know ys not free in B.
          (zs, b) <- go args ys $ mkPi ((name, a) <$ arg) b
          -- Shift back up to make it relative to Δ (x : A) again.
          return (up zs, b)

reallyNotFreeIn :: (MonadReduce m) => IntSet -> Type -> m (IntSet, Type)
reallyNotFreeIn xs a | IntSet.null xs = return (xs, a) -- Shortcut
reallyNotFreeIn xs a = do
  let fvs      = freeVars a
      anywhere = allVars fvs
      rigid    = IntSet.unions [stronglyRigidVars fvs, unguardedVars fvs]
      nonrigid = IntSet.difference anywhere rigid
      hasNo    = IntSet.disjoint xs
  if hasNo nonrigid
    then
       -- No non-rigid occurrences. We can't do anything about the rigid
       -- occurrences so drop those and leave `a` untouched.
       return (IntSet.difference xs rigid, a)
    else do
      -- If there are non-rigid occurrences we need to reduce a to see if
      -- we can get rid of them (#3177).
      (fvs, a) <- forceNotFree (IntSet.difference xs rigid) a
      let xs = IntMap.keysSet $ IntMap.filter (== NotFree) fvs
      return (xs, a)

-- | Instantiate a meta variable with a new one that only takes
--   the arguments which are not pruneable.
performKill
  :: MonadMetaSolver m
  => [Arg Bool]    -- ^ Arguments to old meta var in left to right order
                   --   with @Bool@ indicating whether they can be pruned.
  -> MetaId        -- ^ The old meta var to receive pruning.
  -> Type          -- ^ The pruned type of the new meta var.
  -> m ()
performKill kills m a = do
  mv <- lookupLocalMeta m
  when (mvFrozen mv == Frozen) __IMPOSSIBLE__
  -- Arity of the old meta.
  let n = size kills
  -- The permutation of the new meta picks the arguments
  -- which are not pruned in left to right order
  -- (de Bruijn level order).
  let perm = Perm n
             [ i | (i, Arg _ False) <- zip [0..] kills ]
      -- The permutation for the old meta might range over a prefix of the arguments
      oldPerm = liftP (max 0 $ n - m) p
        where p = mvPermutation mv
              m = size p
      judg = case mvJudgement mv of
        HasType{ jComparison = cmp } -> HasType __IMPOSSIBLE__ cmp a
        IsSort{}  -> IsSort  __IMPOSSIBLE__ a
  m' <- newMeta Instantiable (mvInfo mv) (mvPriority mv) (composeP perm oldPerm) judg
  -- Andreas, 2010-10-15 eta expand new meta variable if necessary
  etaExpandMetaSafe m'
  let -- Arguments to new meta (de Bruijn indices)
      -- in left to right order.
      vars = [ Arg info (var i)
             | (i, Arg info False) <- zip (downFrom n) kills ]
      u       = MetaV m' $ map Apply vars
      -- Arguments to the old meta (just arg infos and name hints)
      -- in left to right order.
      tel     = map ("v" <$) kills
  dbg m' u
  assignTerm m tel u  -- m tel := u
  where
    dbg m' u = reportSDoc "tc.meta.kill" 10 $ vcat
      [ "actual killing"
      , nest 2 $ vcat
        [ "new meta:" <+> pretty m'
        , "kills   :" <+> prettyList_ (map (text . show . unArg) kills)
        , "inst    :" <+> pretty m <+> ":=" <+> prettyTCM u
        ]
      ]
