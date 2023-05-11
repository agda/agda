{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Reduce
 -- Meta instantiation
 ( Instantiate, instantiate', instantiate, instantiateWhen
 -- Recursive meta instantiation
 , InstantiateFull, instantiateFull', instantiateFull
 , instantiateFullExceptForDefinitions
 -- Check for meta (no reduction)
 , IsMeta, isMeta
 -- Reduction and blocking
 , Reduce, reduce', reduceB', reduce, reduceB, reduceWithBlocker, reduceIApply'
 , reduceDefCopy, reduceDefCopyTCM
 , reduceHead
 , slowReduceTerm
 , unfoldCorecursion, unfoldCorecursionE
 , unfoldDefinitionE, unfoldDefinitionStep
 , unfoldInlined
 , appDef', appDefE'
 , abortIfBlocked, ifBlocked, isBlocked, fromBlocked
 -- Simplification
 , Simplify, simplify, simplifyBlocked'
 -- Normalization
 , Normalise, normalise', normalise
 , slowNormaliseArgs
 ) where

import Control.Monad ( (>=>), void )

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Data.Foldable
import Data.Traversable
import Data.HashMap.Strict (HashMap)
import qualified Data.Set as Set

import Agda.Interaction.Options

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Scope.Base (Scope)
import Agda.Syntax.Literal

import {-# SOURCE #-} Agda.TypeChecking.Irrelevance (isPropM)
import {-# SOURCE #-} Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Monad hiding ( enterClosure, constructorForm )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.EtaContract

import Agda.TypeChecking.Reduce.Monad

import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Match
import {-# SOURCE #-} Agda.TypeChecking.Patterns.Match
import {-# SOURCE #-} Agda.TypeChecking.Pretty
import {-# SOURCE #-} Agda.TypeChecking.Rewriting
import {-# SOURCE #-} Agda.TypeChecking.Reduce.Fast
import {-# SOURCE #-} Agda.TypeChecking.Opacity

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size
import Agda.Utils.Tuple
import qualified Agda.Utils.SmallSet as SmallSet

import Agda.Utils.Impossible

instantiate :: (Instantiate a, MonadReduce m) => a -> m a
instantiate = liftReduce . instantiate'

instantiateFull :: (InstantiateFull a, MonadReduce m) => a -> m a
instantiateFull = liftReduce . instantiateFull'

-- | A variant of 'instantiateFull' that only instantiates those
-- meta-variables that satisfy the predicate.

instantiateWhen ::
  (InstantiateFull a, MonadReduce m) =>
  (MetaId -> ReduceM Bool) ->
  a -> m a
instantiateWhen p =
  liftReduce .
  localR (\env -> env { redPred = Just p }) .
  instantiateFull'

reduce :: (Reduce a, MonadReduce m) => a -> m a
reduce = liftReduce . reduce'

reduceB :: (Reduce a, MonadReduce m) => a -> m (Blocked a)
reduceB = liftReduce . reduceB'

-- Reduce a term and also produce a blocker signifying when
-- this reduction should be retried.
reduceWithBlocker :: (Reduce a, IsMeta a, MonadReduce m) => a -> m (Blocker, a)
reduceWithBlocker a = ifBlocked a
  (\b a' -> return (b, a'))
  (\_ a' -> return (neverUnblock, a'))

normalise :: (Normalise a, MonadReduce m) => a -> m a
normalise = liftReduce . normalise'

-- UNUSED
-- -- | Normalise the given term but also preserve blocking tags
-- --   TODO: implement a more efficient version of this.
-- normaliseB :: (MonadReduce m, Reduce t, Normalise t) => t -> m (Blocked t)
-- normaliseB = normalise >=> reduceB

simplify :: (Simplify a, MonadReduce m) => a -> m a
simplify = liftReduce . simplify'

-- | Meaning no metas left in the instantiation.
isFullyInstantiatedMeta :: MetaId -> TCM Bool
isFullyInstantiatedMeta m = do
  inst <- lookupMetaInstantiation m
  case inst of
    InstV inst -> noMetas <$> instantiateFull (instBody inst)
    _ -> return False

-- | Blocking on all blockers.
blockAll :: (Functor f, Foldable f) => f (Blocked a) -> Blocked (f a)
blockAll bs = blockedOn block $ fmap ignoreBlocking bs
  where block = unblockOnAll $ foldMap (Set.singleton . blocker) bs
        blocker NotBlocked{}  = alwaysUnblock
        blocker (Blocked b _) = b

-- | Blocking on any blockers.
blockAny :: (Functor f, Foldable f) => f (Blocked a) -> Blocked (f a)
blockAny bs = blockedOn block $ fmap ignoreBlocking bs
  where block = case foldMap blocker bs of
                  [] -> alwaysUnblock -- no blockers
                  bs -> unblockOnAny $ Set.fromList bs
        blocker NotBlocked{}  = []
        blocker (Blocked b _) = [b]

-- | Instantiate something.
--   Results in an open meta variable or a non meta.
--   Doesn't do any reduction, and preserves blocking tags (when blocking meta
--   is uninstantiated).
class Instantiate t where
  instantiate' :: t -> ReduceM t

  default instantiate' :: (t ~ f a, Traversable f, Instantiate a) => t -> ReduceM t
  instantiate' = traverse instantiate'

instance Instantiate t => Instantiate [t]
instance Instantiate t => Instantiate (Map k t)
instance Instantiate t => Instantiate (Maybe t)
instance Instantiate t => Instantiate (Strict.Maybe t)

instance Instantiate t => Instantiate (Abs t)
instance Instantiate t => Instantiate (Arg t)
instance Instantiate t => Instantiate (Elim' t)
instance Instantiate t => Instantiate (Tele t)
instance Instantiate t => Instantiate (IPBoundary' t)

instance (Instantiate a, Instantiate b) => Instantiate (a,b) where
    instantiate' (x,y) = (,) <$> instantiate' x <*> instantiate' y

instance (Instantiate a, Instantiate b,Instantiate c) => Instantiate (a,b,c) where
    instantiate' (x,y,z) = (,,) <$> instantiate' x <*> instantiate' y <*> instantiate' z

-- | Run the second computation if the 'redPred' predicate holds for
-- the given meta-variable (or if the predicate is not defined), and
-- otherwise the first computation.

ifPredicateDoesNotHoldFor ::
  MetaId -> ReduceM a -> ReduceM a -> ReduceM a
ifPredicateDoesNotHoldFor m doesNotHold holds = do
  pred <- redPred <$> askR
  case pred of
    Nothing -> holds
    Just p  -> ifM (p m) holds doesNotHold

instance Instantiate Term where
  instantiate' t@(MetaV x es) = ifPredicateDoesNotHoldFor x (return t) $ do
    blocking <- view stInstantiateBlocking <$> getTCState

    m <- lookupMeta x
    case m of
      Just (Left rmv) -> cont (rmvInstantiation rmv)

      Just (Right mv) -> case mvInstantiation mv of
         InstV inst -> cont inst

         _ | Just m' <- mvTwin mv, blocking ->
           instantiate' (MetaV m' es)

         Open -> return t

         OpenInstance -> return t

         BlockedConst u
           | blocking  -> instantiate' . unBrave $
                          BraveTerm u `applyE` es
           | otherwise -> return t

         PostponedTypeCheckingProblem _ -> return t

      Nothing -> __IMPOSSIBLE_VERBOSE__
                   ("Meta-variable not found: " ++ prettyShow x)
    where
    cont i = instantiate' inst
      where
      -- A slight complication here is that the meta might be underapplied,
      -- in which case we have to build the lambda abstraction before
      -- applying the substitution, or overapplied in which case we need to
      -- fall back to applyE.
      (es1, es2) = splitAt (length (instTel i)) es
      vs1 = reverse $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es1
      rho = vs1 ++# wkS (length vs1) idS
            -- really should be .. ++# emptyS but using wkS makes it reduce to idS
            -- when applicable
      -- specification:
      -- inst == foldr mkLam (instBody i) (instTel i) `applyE` es
      inst =
        applySubst rho
          (foldr mkLam (instBody i) $ drop (length es1) (instTel i))
          `applyE` es2

  instantiate' (Level l) = levelTm <$> instantiate' l
  instantiate' (Sort s) = Sort <$> instantiate' s
  instantiate' t = return t

instance Instantiate t => Instantiate (Type' t) where
  instantiate' (El s t) = El <$> instantiate' s <*> instantiate' t

instance Instantiate Level where
  instantiate' (Max m as) = levelMax m <$> instantiate' as

-- Use Traversable instance
instance Instantiate t => Instantiate (PlusLevel' t)

instance Instantiate a => Instantiate (Blocked a) where
  instantiate' v@NotBlocked{} = return v
  instantiate' v@(Blocked b u) = instantiate' b >>= \ case
    b | b == alwaysUnblock -> notBlocked <$> instantiate' u
      | otherwise          -> return $ Blocked b u

instance Instantiate Blocker where
  instantiate' (UnblockOnAll bs) = unblockOnAll . Set.fromList <$> mapM instantiate' (Set.toList bs)
  instantiate' (UnblockOnAny bs) = unblockOnAny . Set.fromList <$> mapM instantiate' (Set.toList bs)
  instantiate' b@(UnblockOnMeta x) =
    ifM (isInstantiatedMeta x) (return alwaysUnblock) (return b)
  instantiate' b@UnblockOnProblem{} = return b
  instantiate' b@UnblockOnDef{} = return b

instance Instantiate Sort where
  instantiate' = \case
    MetaS x es -> instantiate' (MetaV x es) >>= \case
      Sort s'      -> return s'
      MetaV x' es' -> return $ MetaS x' es'
      Def d es'    -> return $ DefS d es'
      _            -> __IMPOSSIBLE__
    s -> return s

instance (Instantiate t, Instantiate e) => Instantiate (Dom' t e) where
    instantiate' (Dom i n b tac x) = Dom i n b <$> instantiate' tac <*> instantiate' x

instance Instantiate a => Instantiate (Closure a) where
    instantiate' cl = do
        x <- enterClosure cl instantiate'
        return $ cl { clValue = x }

instance Instantiate Constraint where
  instantiate' (ValueCmp cmp t u v) = do
    (t,u,v) <- instantiate' (t,u,v)
    return $ ValueCmp cmp t u v
  instantiate' (ValueCmpOnFace cmp p t u v) = do
    ((p,t),u,v) <- instantiate' ((p,t),u,v)
    return $ ValueCmpOnFace cmp p t u v
  instantiate' (ElimCmp cmp fs t v as bs) =
    ElimCmp cmp fs <$> instantiate' t <*> instantiate' v <*> instantiate' as <*> instantiate' bs
  instantiate' (LevelCmp cmp u v)   = uncurry (LevelCmp cmp) <$> instantiate' (u,v)
  instantiate' (SortCmp cmp a b)    = uncurry (SortCmp cmp) <$> instantiate' (a,b)
  instantiate' (UnBlock m)          = return $ UnBlock m
  instantiate' (FindInstance m cs)  = FindInstance m <$> mapM instantiate' cs
  instantiate' (IsEmpty r t)        = IsEmpty r <$> instantiate' t
  instantiate' (CheckSizeLtSat t)   = CheckSizeLtSat <$> instantiate' t
  instantiate' c@CheckFunDef{}      = return c
  instantiate' (HasBiggerSort a)    = HasBiggerSort <$> instantiate' a
  instantiate' (HasPTSRule a b)     = uncurry HasPTSRule <$> instantiate' (a,b)
  instantiate' (CheckLockedVars a b c d) =
    CheckLockedVars <$> instantiate' a <*> instantiate' b <*> instantiate' c <*> instantiate' d
  instantiate' (UnquoteTactic t h g) = UnquoteTactic <$> instantiate' t <*> instantiate' h <*> instantiate' g
  instantiate' (CheckDataSort q s)  = CheckDataSort q <$> instantiate' s
  instantiate' c@CheckMetaInst{}    = return c
  instantiate' (CheckType t)        = CheckType <$> instantiate' t
  instantiate' (UsableAtModality cc ms mod t) = flip (UsableAtModality cc) mod <$> instantiate' ms <*> instantiate' t

instance Instantiate CompareAs where
  instantiate' (AsTermsOf a) = AsTermsOf <$> instantiate' a
  instantiate' AsSizes       = return AsSizes
  instantiate' AsTypes       = return AsTypes

instance Instantiate Candidate where
  instantiate' (Candidate q u t ov) = Candidate q <$> instantiate' u <*> instantiate' t <*> pure ov

instance Instantiate EqualityView where
  instantiate' (OtherType t)            = OtherType
    <$> instantiate' t
  instantiate' (IdiomType t)            = IdiomType
    <$> instantiate' t
  instantiate' (EqualityType s eq l t a b) = EqualityType
    <$> instantiate' s
    <*> return eq
    <*> mapM instantiate' l
    <*> instantiate' t
    <*> instantiate' a
    <*> instantiate' b

---------------------------------------------------------------------------
-- * Reduction to weak head normal form.
---------------------------------------------------------------------------

-- | Is something (an elimination of) a meta variable?
--   Does not perform any reductions.

class IsMeta a where
  isMeta :: a -> Maybe MetaId

instance IsMeta Term where
  isMeta (MetaV m _) = Just m
  isMeta _           = Nothing

instance IsMeta a => IsMeta (Sort' a) where
  isMeta (MetaS m _) = Just m
  isMeta _           = Nothing

instance IsMeta a => IsMeta (Type'' t a) where
  isMeta = isMeta . unEl

instance IsMeta a => IsMeta (Elim' a) where
  isMeta Proj{}    = Nothing
  isMeta IApply{}  = Nothing
  isMeta (Apply a) = isMeta a

instance IsMeta a => IsMeta (Arg a) where
  isMeta = isMeta . unArg

instance IsMeta a => IsMeta (Level' a) where
  isMeta (Max 0 [l]) = isMeta l
  isMeta _           = Nothing

instance IsMeta a => IsMeta (PlusLevel' a) where
  isMeta (Plus 0 l)  = isMeta l
  isMeta _           = Nothing

instance IsMeta CompareAs where
  isMeta (AsTermsOf a) = isMeta a
  isMeta AsSizes       = Nothing
  isMeta AsTypes       = Nothing

-- | Case on whether a term is blocked on a meta (or is a meta).
--   That means it can change its shape when the meta is instantiated.
ifBlocked
  :: (Reduce t, IsMeta t, MonadReduce m)
  => t -> (Blocker -> t -> m a) -> (NotBlocked -> t -> m a) -> m a
ifBlocked t blocked unblocked = do
  t <- reduceB t
  case t of
    Blocked m t     -> blocked m t
    NotBlocked nb t -> case isMeta t of -- #4899: MetaS counts as NotBlocked at the moment
      Just m    -> blocked (unblockOnMeta m) t
      Nothing   -> unblocked nb t

-- | Throw pattern violation if blocked or a meta.
abortIfBlocked :: (MonadReduce m, MonadBlock m, IsMeta t, Reduce t) => t -> m t
abortIfBlocked t = ifBlocked t (const . patternViolation) (const return)

isBlocked
  :: (Reduce t, IsMeta t, MonadReduce m)
  => t -> m (Maybe Blocker)
isBlocked t = ifBlocked t (\m _ -> return $ Just m) (\_ _ -> return Nothing)

-- | Throw a pattern violation if the argument is @Blocked@,
--   otherwise return the value embedded in the @NotBlocked@.
fromBlocked :: MonadBlock m => Blocked a -> m a
fromBlocked (Blocked b _) = patternViolation b
fromBlocked (NotBlocked _ x) = return x

class Reduce t where
  reduce'  :: t -> ReduceM t
  reduceB' :: t -> ReduceM (Blocked t)

  reduce'  t = ignoreBlocking <$> reduceB' t
  reduceB' t = notBlocked <$> reduce' t

instance Reduce Type where
    reduce'  (El s t) = workOnTypes $ El s <$> reduce' t
    reduceB' (El s t) = workOnTypes $ fmap (El s) <$> reduceB' t

instance Reduce Sort where
    reduceB' s = do
      s <- instantiate' s
      let done | MetaS x _ <- s = return $ blocked x s
               | otherwise      = return $ notBlocked s
      case s of
        PiSort a s1 s2 -> reduceB' (s1 , s2) >>= \case
          Blocked b (s1',s2') -> return $ Blocked b $ PiSort a s1' s2'
          NotBlocked _ (s1',s2') -> do
            -- Jesper, 2022-10-12: do instantiateFull here because
            -- `piSort'` does checking of free variables, and if we
            -- don't instantiate we might end up blocking on a solved
            -- metavariable.
            s2' <- instantiateFull s2'
            case piSort' a s1' s2' of
              Left b -> return $ Blocked b $ PiSort a s1' s2'
              Right s -> reduceB' s
        FunSort s1 s2 -> reduceB' (s1 , s2) >>= \case
          Blocked b (s1',s2') -> return $ Blocked b $ FunSort s1' s2'
          NotBlocked _ (s1',s2') -> do
            case funSort' s1' s2' of
              Left b -> return $ Blocked b $ FunSort s1' s2'
              Right s -> reduceB' s
        UnivSort s1 -> reduceB' s1 >>= \case
          Blocked b s1' -> return $ Blocked b $ UnivSort s1'
          NotBlocked _ s1' -> case univSort' s1' of
            Left b -> return $ Blocked b $ UnivSort s1'
            Right s -> reduceB' s
        Univ u l   -> notBlocked . Univ u <$> reduce l
        Inf f n    -> done
        SizeUniv   -> done
        LockUniv   -> done
        LevelUniv  -> do
          levelUniverseEnabled <- isLevelUniverseEnabled
          if levelUniverseEnabled
          then done
          else return $ notBlocked (mkType 0)
        IntervalUniv -> done
        MetaS x es -> done
        DefS d es  -> done -- postulated sorts do not reduce
        DummyS{}   -> done

instance Reduce Elim where
  reduce' (Apply v) = Apply <$> reduce' v
  reduce' (Proj o f)= pure $ Proj o f
  reduce' (IApply x y v) = IApply <$> reduce' x <*> reduce' y <*> reduce' v

instance Reduce Level where
  reduce'  (Max m as) = levelMax m <$> mapM reduce' as
  reduceB' (Max m as) = fmap (levelMax m) . blockAny <$> traverse reduceB' as

instance Reduce PlusLevel where
  reduceB' (Plus n l) = fmap (Plus n) <$> reduceB' l

instance (Subst a, Reduce a) => Reduce (Abs a) where
  reduceB' b@(Abs x _) = fmap (Abs x) <$> underAbstraction_ b reduceB'
  reduceB' (NoAbs x v) = fmap (NoAbs x) <$> reduceB' v

-- Lists are never blocked
instance Reduce t => Reduce [t] where
    reduce' = traverse reduce'

-- Maybes are never blocked
instance Reduce t => Reduce (Maybe t) where
    reduce' = traverse reduce'

instance Reduce t => Reduce (Arg t) where
    reduce' a = case getRelevance a of
      Irrelevant -> return a             -- Don't reduce' irr. args!?
                                         -- Andreas, 2018-03-03, caused #2989.
      _          -> traverse reduce' a

    reduceB' t = traverse id <$> traverse reduceB' t

instance Reduce t => Reduce (Dom t) where
    reduce' = traverse reduce'
    reduceB' t = traverse id <$> traverse reduceB' t

instance (Reduce a, Reduce b) => Reduce (a,b) where
    reduce' (x,y)  = (,) <$> reduce' x <*> reduce' y
    reduceB' (x,y) = do
      x <- reduceB' x
      y <- reduceB' y
      let blk = void x `mappend` void y
          xy  = (ignoreBlocking x , ignoreBlocking y)
      return $ blk $> xy

instance (Reduce a, Reduce b,Reduce c) => Reduce (a,b,c) where
    reduce' (x,y,z) = (,,) <$> reduce' x <*> reduce' y <*> reduce' z
    reduceB' (x,y,z) = do
      x <- reduceB' x
      y <- reduceB' y
      z <- reduceB' z
      let blk = void x `mappend` void y `mappend` void z
          xyz = (ignoreBlocking x , ignoreBlocking y , ignoreBlocking z)
      return $ blk $> xyz

reduceIApply :: ReduceM (Blocked Term) -> [Elim] -> ReduceM (Blocked Term)
reduceIApply = reduceIApply' reduceB'

reduceIApply' :: (Term -> ReduceM (Blocked Term)) -> ReduceM (Blocked Term) -> [Elim] -> ReduceM (Blocked Term)
reduceIApply' red d (IApply x y r : es) = do
  view <- intervalView'
  r <- reduceB' r
  -- We need to propagate the blocking information so that e.g.
  -- we postpone "someNeutralPath ?0 = a" rather than fail.
  case view (ignoreBlocking r) of
   IZero -> red (applyE x es)
   IOne  -> red (applyE y es)
   _     -> fmap (<* r) (reduceIApply' red d es)
reduceIApply' red d (_ : es) = reduceIApply' red d es
reduceIApply' _   d [] = d

instance Reduce DeBruijnPattern where
  reduceB' (DotP o v) = fmap (DotP o) <$> reduceB' v
  reduceB' p          = return $ notBlocked p

instance Reduce Term where
  reduceB' = {-# SCC "reduce'<Term>" #-} maybeFastReduceTerm

shouldTryFastReduce :: ReduceM Bool
shouldTryFastReduce = optFastReduce <$> pragmaOptions

maybeFastReduceTerm :: Term -> ReduceM (Blocked Term)
maybeFastReduceTerm v = do
  let tryFast = case v of
                  Def{}   -> True
                  Con{}   -> True
                  MetaV{} -> True
                  _       -> False
  if not tryFast then slowReduceTerm v
                 else
    case v of
      MetaV x _ -> ifM (isOpen x) (return $ blocked x v) (maybeFast v)
      _         -> maybeFast v
  where
    isOpen x = isOpenMeta <$> lookupMetaInstantiation x
    maybeFast v = ifM shouldTryFastReduce (fastReduce v) (slowReduceTerm v)

slowReduceTerm :: Term -> ReduceM (Blocked Term)
slowReduceTerm v = do
    v <- instantiate' v
    let done | MetaV x _ <- v = return $ blocked x v
             | otherwise      = return $ notBlocked v
        iapp = reduceIApply done
    case v of
--    Andreas, 2012-11-05 not reducing meta args does not destroy anything
--    and seems to save 2% sec on the standard library
--      MetaV x args -> notBlocked . MetaV x <$> reduce' args
      MetaV x es -> iapp es
      Def f es   -> flip reduceIApply es $ unfoldDefinitionE False reduceB' (Def f []) f es
      Con c ci es -> do
          -- Constructors can reduce' when they come from an
          -- instantiated module.
          -- also reduce when they are path constructors
          v <- flip reduceIApply es
                 $ unfoldDefinitionE False reduceB' (Con c ci []) (conName c) es
          traverse reduceNat v
      Sort s   -> done
      Level l  -> ifM (SmallSet.member LevelReductions <$> asksTC envAllowedReductions)
                    {- then -} (fmap levelTm <$> reduceB' l)
                    {- else -} done
      Pi _ _   -> done
      Lit _    -> done
      Var _ es  -> iapp es
      Lam _ _  -> done
      DontCare _ -> done
      Dummy{}    -> done
    where
      -- NOTE: reduceNat can traverse the entire term.
      reduceNat v@(Con c ci []) = do
        mz  <- getBuiltin' builtinZero
        case v of
          _ | Just v == mz  -> return $ Lit $ LitNat 0
          _                 -> return v
      reduceNat v@(Con c ci [Apply a]) | visible a && isRelevant a = do
        ms  <- getBuiltin' builtinSuc
        case v of
          _ | Just (Con c ci []) == ms -> inc <$> reduce' (unArg a)
          _                         -> return v
          where
            inc = \case
              Lit (LitNat n) -> Lit $ LitNat $ n + 1
              w              -> Con c ci [Apply $ defaultArg w]
      reduceNat v = return v

-- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
-- need also to instantiate metas, see Issue 826.
unfoldCorecursionE :: Elim -> ReduceM (Blocked Elim)
unfoldCorecursionE (Proj o p)           = notBlocked . Proj o <$> getOriginalProjection p
unfoldCorecursionE (Apply (Arg info v)) = fmap (Apply . Arg info) <$>
  unfoldCorecursion v
unfoldCorecursionE (IApply x y r) = do -- TODO check if this makes sense
   [x,y,r] <- mapM unfoldCorecursion [x,y,r]
   return $ IApply <$> x <*> y <*> r

unfoldCorecursion :: Term -> ReduceM (Blocked Term)
unfoldCorecursion v = do
  v <- instantiate' v
  case v of
    Def f es -> unfoldDefinitionE True unfoldCorecursion (Def f []) f es
    _ -> slowReduceTerm v

-- | If the first argument is 'True', then a single delayed clause may
-- be unfolded.
unfoldDefinition ::
  Bool -> (Term -> ReduceM (Blocked Term)) ->
  Term -> QName -> Args -> ReduceM (Blocked Term)
unfoldDefinition unfoldDelayed keepGoing v f args =
  unfoldDefinitionE unfoldDelayed keepGoing v f (map Apply args)

unfoldDefinitionE ::
  Bool -> (Term -> ReduceM (Blocked Term)) ->
  Term -> QName -> Elims -> ReduceM (Blocked Term)
unfoldDefinitionE unfoldDelayed keepGoing v f es = do
  r <- unfoldDefinitionStep unfoldDelayed v f es
  case r of
    NoReduction v    -> return v
    YesReduction _ v -> keepGoing v

unfoldDefinition' ::
  Bool -> (Simplification -> Term -> ReduceM (Simplification, Blocked Term)) ->
  Term -> QName -> Elims -> ReduceM (Simplification, Blocked Term)
unfoldDefinition' unfoldDelayed keepGoing v0 f es = do
  r <- unfoldDefinitionStep unfoldDelayed v0 f es
  case r of
    NoReduction v       -> return (NoSimplification, v)
    YesReduction simp v -> keepGoing simp v

unfoldDefinitionStep :: Bool -> Term -> QName -> Elims -> ReduceM (Reduced (Blocked Term) Term)
unfoldDefinitionStep unfoldDelayed v0 f es =
  {-# SCC "reduceDef" #-} do
  traceSDoc "tc.reduce" 90 ("unfoldDefinitionStep v0" <+> pretty v0) $ do
  info <- getConstInfo f
  rewr <- instantiateRewriteRules =<< getRewriteRulesFor f
  allowed <- asksTC envAllowedReductions
  prp <- runBlocked $ isPropM $ defType info
  defOk <- shouldReduceDef f
  let def = theDef info
      v   = v0 `applyE` es
      -- Non-terminating functions
      -- (i.e., those that failed the termination check)
      -- and delayed definitions
      -- are not unfolded unless explicitly permitted.
      dontUnfold = or
        [ defNonterminating info && SmallSet.notMember NonTerminatingReductions allowed
        , defTerminationUnconfirmed info && SmallSet.notMember UnconfirmedReductions allowed
        , defDelayed info == Delayed && not unfoldDelayed
        , prp == Right True
        , isIrrelevant info
        , not defOk
        ]
      copatterns = defCopatternLHS info
  case def of
    Constructor{conSrcCon = c} -> do
      let hd = Con (c `withRangeOf` f) ConOSystem
      rewrite (NotBlocked ReallyNotBlocked ()) hd rewr es
    Primitive{primAbstr = ConcreteDef, primName = x, primClauses = cls} -> do
      pf <- fromMaybe __IMPOSSIBLE__ <$> getPrimitive' x
      if FunctionReductions `SmallSet.member` allowed
        then reducePrimitive x v0 f es pf dontUnfold
                             cls (defCompiled info) rewr
        else noReduction $ notBlocked v
    PrimitiveSort{ primSortSort = s } -> yesReduction NoSimplification $ Sort s `applyE` es

    _  -> do
      if or
          [ RecursiveReductions `SmallSet.member` allowed
          , isJust (isProjection_ def) && ProjectionReductions `SmallSet.member` allowed
              -- Includes projection-like and irrelevant projections.
              -- Note: irrelevant projections lead to @dontUnfold@ and
              -- so are not actually unfolded.
          , isInlineFun def && InlineReductions `SmallSet.member` allowed
          , definitelyNonRecursive_ def && or
            [ copatterns && CopatternReductions `SmallSet.member` allowed
            , FunctionReductions `SmallSet.member` allowed
            ]
          ]
        then
          reduceNormalE v0 f (map notReduced es) dontUnfold
                       (defClauses info) (defCompiled info) rewr
        else noReduction $ notBlocked v  -- Andrea(s), 2014-12-05 OK?

  where
    noReduction    = return . NoReduction
    yesReduction s = return . YesReduction s
    reducePrimitive x v0 f es pf dontUnfold cls mcc rewr
      | length es < ar
                  = noReduction $ NotBlocked Underapplied $ v0 `applyE` es -- not fully applied
      | otherwise = {-# SCC "reducePrimitive" #-} do
          let (es1,es2) = splitAt ar es
              args1     = fromMaybe __IMPOSSIBLE__ $ mapM isApplyElim es1
          r <- primFunImplementation pf args1 (length es2)
          case r of
            NoReduction args1' -> do
              let es1' = map (fmap Apply) args1'
              if null cls && null rewr then do
                noReduction $ applyE (Def f []) <$> do
                  blockAll $ map mredToBlocked es1' ++ map notBlocked es2
               else
                reduceNormalE v0 f (es1' ++ map notReduced es2) dontUnfold cls mcc rewr
            YesReduction simpl v -> yesReduction simpl $ v `applyE` es2
      where
          ar  = primFunArity pf

          mredToBlocked :: IsMeta t => MaybeReduced t -> Blocked t
          mredToBlocked (MaybeRed NotReduced  e) = notBlocked e
          mredToBlocked (MaybeRed (Reduced b) e) = e <$ b

    reduceNormalE :: Term -> QName -> [MaybeReduced Elim] -> Bool -> [Clause] -> Maybe CompiledClauses -> RewriteRules -> ReduceM (Reduced (Blocked Term) Term)
    reduceNormalE v0 f es dontUnfold def mcc rewr = {-# SCC "reduceNormal" #-} do
      traceSDoc "tc.reduce" 90 ("reduceNormalE v0 =" <+> pretty v0) $ do
      case (def,rewr) of
        _ | dontUnfold -> traceSLn "tc.reduce" 90 "reduceNormalE: don't unfold (non-terminating or delayed)" $
                          defaultResult -- non-terminating or delayed
        ([],[])        -> traceSLn "tc.reduce" 90 "reduceNormalE: no clauses or rewrite rules" $ do
          -- no definition for head
          blk <- defBlocked <$> getConstInfo f
          noReduction $ blk $> vfull
        (cls,rewr)     -> do
          ev <- appDefE_ f v0 cls mcc rewr es
          debugReduce ev
          return ev
      where
      defaultResult = noReduction $ NotBlocked ReallyNotBlocked vfull
      vfull         = v0 `applyE` map ignoreReduced es
      debugReduce ev = verboseS "tc.reduce" 90 $ do
        case ev of
          NoReduction v -> do
            reportSDoc "tc.reduce" 90 $ vcat
              [ "*** tried to reduce " <+> pretty f
              , "    es =  " <+> sep (map (pretty . ignoreReduced) es)
              -- , "*** tried to reduce " <+> pretty vfull
              , "    stuck on" <+> pretty (ignoreBlocking v)
              ]
          YesReduction _simpl v -> do
            reportSDoc "tc.reduce"  90 $ "*** reduced definition: " <+> pretty f
            reportSDoc "tc.reduce"  95 $ "    result" <+> pretty v

-- | Specialized version to put in boot file.
reduceDefCopyTCM :: QName -> Elims -> TCM (Reduced () Term)
reduceDefCopyTCM = reduceDefCopy

-- | Reduce a non-primitive definition if it is a copy linking to another def.
reduceDefCopy :: forall m. PureTCM m => QName -> Elims -> m (Reduced () Term)
reduceDefCopy f es = do
  info <- getConstInfo f
  case theDef info of
    _ | not $ defCopy info     -> return $ NoReduction ()
    Constructor{conSrcCon = c} -> return $ YesReduction YesSimplification (Con c ConOSystem es)
    _                          -> reduceDef_ info f es
  where
    reduceDef_ :: Definition -> QName -> Elims -> m (Reduced () Term)
    reduceDef_ info f es = case defClauses info of
      [cl] -> do  -- proper copies always have a single clause
        let v0 = Def f [] -- TODO: could be Con
            ps    = namedClausePats cl
            nargs = length es
            -- appDefE_ cannot handle underapplied functions, so we eta-expand here if that's the
            -- case. We use this function to compute display forms from module applications and in
            -- that case we don't always have saturated applications.
            (lam, es') = (unlamView xs, newes)
              where
                etaArgs [] _ = []
                etaArgs (p : ps) []
                  | VarP _ x <- namedArg p = Arg (getArgInfo p) (dbPatVarName x) : etaArgs ps []
                  | otherwise              = []
                etaArgs (_ : ps) (_ : es) = etaArgs ps es
                xs  = etaArgs ps es
                n   = length xs
                newes = raise n es ++ [ Apply $ var i <$ x | (i, x) <- zip (downFrom n) xs ]
        if (defDelayed info == Delayed) || (defNonterminating info)
         then return $ NoReduction ()
         else do
            ev <- liftReduce $ appDefE_ f v0 [cl] Nothing mempty $ map notReduced es'
            case ev of
              YesReduction simpl t -> return $ YesReduction simpl (lam t)
              NoReduction{}        -> return $ NoReduction ()
      []    -> return $ NoReduction ()  -- copies of generalizable variables have no clauses (and don't need unfolding)
      _:_:_ -> __IMPOSSIBLE__

-- | Reduce simple (single clause) definitions.
reduceHead :: PureTCM m => Term -> m (Blocked Term)
reduceHead v = do -- ignoreAbstractMode $ do
  -- Andreas, 2013-02-18 ignoreAbstractMode leads to information leakage
  -- see Issue 796

  -- first, possibly rewrite literal v to constructor form
  v <- constructorForm v
  traceSDoc "tc.inj.reduce" 30 (ignoreAbstractMode $ "reduceHead" <+> prettyTCM v) $ do
  case v of
    Def f es -> do

      abstractMode <- envAbstractMode <$> askTC
      isAbstract <- not <$> hasAccessibleDef f
      traceSLn "tc.inj.reduce" 50 (
        "reduceHead: we are in " ++ show abstractMode++ "; " ++ prettyShow f ++
        " is treated " ++ if isAbstract then "abstractly" else "concretely"
        ) $ do
      let v0  = Def f []
          red = liftReduce $ unfoldDefinitionE False reduceHead v0 f es
      def <- theDef <$> getConstInfo f
      case def of
        -- Andreas, 2012-11-06 unfold aliases (single clause terminating functions)
        -- see test/succeed/Issue747
        -- We restrict this to terminating functions to not make the
        -- type checker loop here on non-terminating functions.
        -- see test/fail/TerminationInfiniteRecord
        Function{ funClauses = [ _ ], funDelayed = NotDelayed, funTerminates = Just True } -> do
          traceSLn "tc.inj.reduce" 50 ("reduceHead: head " ++ prettyShow f ++ " is Function") $ do
          red
        Datatype{ dataClause = Just _ } -> red
        Record{ recClause = Just _ }    -> red
        _                               -> return $ notBlocked v
    _ -> return $ notBlocked v

-- | Unfold a single inlined function.
unfoldInlined :: PureTCM m => Term -> m Term
unfoldInlined v = do
  inTypes <- viewTC eWorkingOnTypes
  case v of
    _ | inTypes -> return v -- Don't inline in types (to avoid unfolding of goals)
    Def f es -> do
      info <- getConstInfo f
      let def = theDef info
          irr = isIrrelevant $ defArgInfo info
      case def of   -- Only for simple definitions with no pattern matching (TODO: maybe copatterns?)
        Function{ funCompiled = Just Done{}, funDelayed = NotDelayed }
          | def ^. funInline , not irr -> liftReduce $
          ignoreBlocking <$> unfoldDefinitionE False (return . notBlocked) (Def f []) f es
        _ -> return v
    _ -> return v

-- | Apply a definition using the compiled clauses, or fall back to
--   ordinary clauses if no compiled clauses exist.
appDef_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef_ f v0 cls mcc rewr args = appDefE_ f v0 cls mcc rewr $ map (fmap Apply) args

appDefE_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE_ f v0 cls mcc rewr args =
  localTC (\ e -> e { envAppDef = Just f }) $
  maybe (appDefE'' v0 cls rewr args)
        (\cc -> appDefE v0 cc rewr args) mcc


-- | Apply a defined function to it's arguments, using the compiled clauses.
--   The original term is the first argument applied to the third.
appDef :: Term -> CompiledClauses -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef v cc rewr args = appDefE v cc rewr $ map (fmap Apply) args

appDefE :: Term -> CompiledClauses -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE v cc rewr es = do
  traceSDoc "tc.reduce" 90 ("appDefE v = " <+> pretty v) $ do
  r <- matchCompiledE cc es
  case r of
    YesReduction simpl t -> return $ YesReduction simpl t
    NoReduction es'      -> rewrite (void es') (applyE v) rewr (ignoreBlocking es')

-- | Apply a defined function to it's arguments, using the original clauses.
appDef' :: QName -> Term -> [Clause] -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef' f v cls rewr args = appDefE' f v cls rewr $ map (fmap Apply) args

appDefE' :: QName -> Term -> [Clause] -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE' f v cls rewr es =
  localTC (\ e -> e { envAppDef = Just f }) $
  appDefE'' v cls rewr es

-- | Expects @'envAppDef' = Just f@ in 'TCEnv' to be able to report @'MissingClauses' f@.
appDefE'' :: Term -> [Clause] -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE'' v cls rewr es = traceSDoc "tc.reduce" 90 ("appDefE' v = " <+> pretty v) $ do
  goCls cls $ map ignoreReduced es
  where
    goCls :: [Clause] -> [Elim] -> ReduceM (Reduced (Blocked Term) Term)
    goCls cl es = do
      case cl of
        -- Andreas, 2013-10-26  In case of an incomplete match,
        -- we just do not reduce.  This allows adding single function
        -- clauses after they have been type-checked, to type-check
        -- the remaining clauses (see Issue 907).
        -- Andrea(s), 2014-12-05:  We return 'MissingClauses' here, since this
        -- is the most conservative reason.
        [] -> do
          f <- fromMaybe __IMPOSSIBLE__ <$> asksTC envAppDef
          rewrite (NotBlocked (MissingClauses f) ()) (applyE v) rewr es
        cl : cls -> do
          let pats = namedClausePats cl
              body = clauseBody cl
              npats = length pats
              nvars = size $ clauseTel cl
          -- if clause is underapplied, skip to next clause
          if length es < npats then goCls cls es else do
            let (es0, es1) = splitAt npats es
            (m, es0) <- matchCopatterns pats es0
            let es = es0 ++ es1
            case m of
              No         -> goCls cls es
              DontKnow b -> rewrite b (applyE v) rewr es
              Yes simpl vs -- vs is the subst. for the variables bound in body
                | Just w <- body -> do -- clause has body?
                    -- TODO: let matchPatterns also return the reduced forms
                    -- of the original arguments!
                    -- Andreas, 2013-05-19 isn't this done now?
                    let sigma = buildSubstitution impossible nvars vs
                    return $ YesReduction simpl $ applySubst sigma w `applyE` es1
                | otherwise     -> rewrite (NotBlocked AbsurdMatch ()) (applyE v) rewr es

instance Reduce a => Reduce (Closure a) where
    reduce' cl = do
        x <- enterClosure cl reduce'
        return $ cl { clValue = x }

instance Reduce Telescope where
  reduce' EmptyTel          = return EmptyTel
  reduce' (ExtendTel a tel) = ExtendTel <$> reduce' a <*> reduce' tel

instance Reduce Constraint where
  reduce' (ValueCmp cmp t u v) = do
    (t,u,v) <- reduce' (t,u,v)
    return $ ValueCmp cmp t u v
  reduce' (ValueCmpOnFace cmp p t u v) = do
    ((p,t),u,v) <- reduce' ((p,t),u,v)
    return $ ValueCmpOnFace cmp p t u v
  reduce' (ElimCmp cmp fs t v as bs) =
    ElimCmp cmp fs <$> reduce' t <*> reduce' v <*> reduce' as <*> reduce' bs
  reduce' (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> reduce' (u,v)
  reduce' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> reduce' (a,b)
  reduce' (UnBlock m)           = return $ UnBlock m
  reduce' (FindInstance m cs)   = FindInstance m <$> mapM reduce' cs
  reduce' (IsEmpty r t)         = IsEmpty r <$> reduce' t
  reduce' (CheckSizeLtSat t)    = CheckSizeLtSat <$> reduce' t
  reduce' c@CheckFunDef{}       = return c
  reduce' (HasBiggerSort a)     = HasBiggerSort <$> reduce' a
  reduce' (HasPTSRule a b)      = uncurry HasPTSRule <$> reduce' (a,b)
  reduce' (UnquoteTactic t h g) = UnquoteTactic <$> reduce' t <*> reduce' h <*> reduce' g
  reduce' (CheckLockedVars a b c d) =
    CheckLockedVars <$> reduce' a <*> reduce' b <*> reduce' c <*> reduce' d
  reduce' (CheckDataSort q s)   = CheckDataSort q <$> reduce' s
  reduce' c@CheckMetaInst{}     = return c
  reduce' (CheckType t)         = CheckType <$> reduce' t
  reduce' (UsableAtModality cc ms mod t) = flip (UsableAtModality cc) mod <$> reduce' ms <*> reduce' t

instance Reduce CompareAs where
  reduce' (AsTermsOf a) = AsTermsOf <$> reduce' a
  reduce' AsSizes       = return AsSizes
  reduce' AsTypes       = return AsTypes

instance Reduce e => Reduce (Map k e) where
  reduce' = traverse reduce'

instance Reduce Candidate where
  reduce' (Candidate q u t ov) = Candidate q <$> reduce' u <*> reduce' t <*> pure ov

instance Reduce EqualityView where
  reduce' (OtherType t)            = OtherType
    <$> reduce' t
  reduce' (IdiomType t)            = IdiomType
    <$> reduce' t
  reduce' (EqualityType s eq l t a b) = EqualityType
    <$> reduce' s
    <*> return eq
    <*> mapM reduce' l
    <*> reduce' t
    <*> reduce' a
    <*> reduce' b

instance Reduce t => Reduce (IPBoundary' t) where
  reduce' = traverse reduce'
  reduceB' = fmap sequenceA . traverse reduceB'

---------------------------------------------------------------------------
-- * Simplification
---------------------------------------------------------------------------

-- | Only unfold definitions if this leads to simplification
--   which means that a constructor/literal pattern is matched.
--   We include reduction of IApply patterns, as `p i0` is akin to
--   matcing on the `i0` constructor of interval.
class Simplify t where
  simplify' :: t -> ReduceM t

  default simplify' :: (t ~ f a, Traversable f, Simplify a) => t -> ReduceM t
  simplify' = traverse simplify'

-- boring instances:

instance Simplify t => Simplify [t]
instance Simplify t => Simplify (Map k t)
instance Simplify t => Simplify (Maybe t)
instance Simplify t => Simplify (Strict.Maybe t)

instance Simplify t => Simplify (Arg t)
instance Simplify t => Simplify (Elim' t)
instance Simplify t => Simplify (Named name t)
instance Simplify t => Simplify (IPBoundary' t)

instance (Simplify a, Simplify b) => Simplify (a,b) where
    simplify' (x,y) = (,) <$> simplify' x <*> simplify' y

instance (Simplify a, Simplify b, Simplify c) => Simplify (a,b,c) where
    simplify' (x,y,z) =
        do  (x,(y,z)) <- simplify' (x,(y,z))
            return (x,y,z)

instance Simplify Bool where
  simplify' = return

-- interesting instances:

instance Simplify Term where
  simplify' v = do
    v <- instantiate' v
    let iapp es m = ignoreBlocking <$> reduceIApply' (fmap notBlocked . simplify') (notBlocked <$> m) es
    case v of
      Def f vs   -> iapp vs $ do
        let keepGoing simp v = return (simp, notBlocked v)
        (simpl, v) <- unfoldDefinition' False keepGoing (Def f []) f vs
        when (simpl == YesSimplification) $
          reportSDoc "tc.simplify'" 90 $
            pretty f <+> text ("simplify': unfolding definition returns " ++ show simpl) <+> pretty (ignoreBlocking v)
        case simpl of
          YesSimplification -> simplifyBlocked' v -- Dangerous, but if @simpl@ then @v /= Def f vs@
          NoSimplification  -> Def f <$> simplify' vs
      MetaV x vs -> iapp vs $ MetaV x  <$> simplify' vs
      Con c ci vs-> iapp vs $ Con c ci <$> simplify' vs
      Sort s     -> Sort     <$> simplify' s
      Level l    -> levelTm  <$> simplify' l
      Pi a b     -> Pi       <$> simplify' a <*> simplify' b
      Lit l      -> return v
      Var i vs   -> iapp vs $ Var i    <$> simplify' vs
      Lam h v    -> Lam h    <$> simplify' v
      DontCare v -> dontCare <$> simplify' v
      Dummy{}    -> return v

simplifyBlocked' :: Simplify t => Blocked t -> ReduceM t
simplifyBlocked' (Blocked _ t) = return t
simplifyBlocked' (NotBlocked _ t) = simplify' t  -- Andrea(s), 2014-12-05 OK?

instance Simplify t => Simplify (Type' t) where
    simplify' (El s t) = El <$> simplify' s <*> simplify' t

instance Simplify Sort where
    simplify' s = do
      case s of
        PiSort a s1 s2 -> piSort <$> simplify' a <*> simplify' s1 <*> simplify' s2
        FunSort s1 s2 -> funSort <$> simplify' s1 <*> simplify' s2
        UnivSort s -> univSort <$> simplify' s
        Univ u s   -> Univ u <$> simplify' s
        Inf _ _    -> return s
        SizeUniv   -> return s
        LockUniv   -> return s
        LevelUniv  -> return s
        IntervalUniv -> return s
        MetaS x es -> MetaS x <$> simplify' es
        DefS d es  -> DefS d <$> simplify' es
        DummyS{}   -> return s

instance Simplify Level where
  simplify' (Max m as) = levelMax m <$> simplify' as

instance Simplify PlusLevel where
  simplify' (Plus n l) = Plus n <$> simplify' l

instance (Subst a, Simplify a) => Simplify (Abs a) where
    simplify' a@(Abs x _) = Abs x <$> underAbstraction_ a simplify'
    simplify' (NoAbs x v) = NoAbs x <$> simplify' v

instance Simplify t => Simplify (Dom t) where
    simplify' = traverse simplify'

instance Simplify a => Simplify (Closure a) where
    simplify' cl = do
        x <- enterClosure cl simplify'
        return $ cl { clValue = x }

instance (Subst a, Simplify a) => Simplify (Tele a) where
  simplify' EmptyTel        = return EmptyTel
  simplify' (ExtendTel a b) = uncurry ExtendTel <$> simplify' (a, b)

instance Simplify ProblemConstraint where
  simplify' (PConstr pid unblock c) = PConstr pid unblock <$> simplify' c

instance Simplify Constraint where
  simplify' (ValueCmp cmp t u v) = do
    (t,u,v) <- simplify' (t,u,v)
    return $ ValueCmp cmp t u v
  simplify' (ValueCmpOnFace cmp p t u v) = do
    ((p,t),u,v) <- simplify' ((p,t),u,v)
    return $ ValueCmp cmp (AsTermsOf t) u v
  simplify' (ElimCmp cmp fs t v as bs) =
    ElimCmp cmp fs <$> simplify' t <*> simplify' v <*> simplify' as <*> simplify' bs
  simplify' (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> simplify' (u,v)
  simplify' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> simplify' (a,b)
  simplify' (UnBlock m)           = return $ UnBlock m
  simplify' (FindInstance m cs)   = FindInstance m <$> mapM simplify' cs
  simplify' (IsEmpty r t)         = IsEmpty r <$> simplify' t
  simplify' (CheckSizeLtSat t)    = CheckSizeLtSat <$> simplify' t
  simplify' c@CheckFunDef{}       = return c
  simplify' (HasBiggerSort a)     = HasBiggerSort <$> simplify' a
  simplify' (HasPTSRule a b)      = uncurry HasPTSRule <$> simplify' (a,b)
  simplify' (UnquoteTactic t h g) = UnquoteTactic <$> simplify' t <*> simplify' h <*> simplify' g
  simplify' (CheckLockedVars a b c d) =
    CheckLockedVars <$> simplify' a <*> simplify' b <*> simplify' c <*> simplify' d
  simplify' (CheckDataSort q s)   = CheckDataSort q <$> simplify' s
  simplify' c@CheckMetaInst{}     = return c
  simplify' (CheckType t)         = CheckType <$> simplify' t
  simplify' (UsableAtModality cc ms mod t) = flip (UsableAtModality cc) mod <$> simplify' ms <*> simplify' t

instance Simplify CompareAs where
  simplify' (AsTermsOf a) = AsTermsOf <$> simplify' a
  simplify' AsSizes       = return AsSizes
  simplify' AsTypes       = return AsTypes

-- UNUSED
-- instance Simplify ConPatternInfo where
--   simplify' (ConPatternInfo mr mt) = ConPatternInfo mr <$> simplify' mt

-- UNUSED
-- instance Simplify Pattern where
--   simplify' p = case p of
--     VarP _       -> return p
--     LitP _       -> return p
--     ConP c ci ps -> ConP c <$> simplify' ci <*> simplify' ps
--     DotP v       -> DotP <$> simplify' v
--     ProjP _      -> return p

instance Simplify DisplayForm where
  simplify' (Display n ps v) = Display n <$> simplify' ps <*> return v

instance Simplify Candidate where
  simplify' (Candidate q u t ov) = Candidate q <$> simplify' u <*> simplify' t <*> pure ov

instance Simplify EqualityView where
  simplify' (OtherType t)            = OtherType
    <$> simplify' t
  simplify' (IdiomType t)            = IdiomType
    <$> simplify' t
  simplify' (EqualityType s eq l t a b) = EqualityType
    <$> simplify' s
    <*> return eq
    <*> mapM simplify' l
    <*> simplify' t
    <*> simplify' a
    <*> simplify' b

---------------------------------------------------------------------------
-- * Normalisation
---------------------------------------------------------------------------

class Normalise t where
  normalise' :: t -> ReduceM t

  default normalise' :: (t ~ f a, Traversable f, Normalise a) => t -> ReduceM t
  normalise' = traverse normalise'

-- boring instances:

instance Normalise t => Normalise [t]
instance Normalise t => Normalise (Map k t)
instance Normalise t => Normalise (Maybe t)
instance Normalise t => Normalise (Strict.Maybe t)

-- Arg not included since we do not normalize irrelevant subterms
-- Elim' not included since it contains Arg
instance Normalise t => Normalise (Named name t)
instance Normalise t => Normalise (IPBoundary' t)
instance Normalise t => Normalise (WithHiding t)

instance (Normalise a, Normalise b) => Normalise (a,b) where
    normalise' (x,y) = (,) <$> normalise' x <*> normalise' y

instance (Normalise a, Normalise b, Normalise c) => Normalise (a,b,c) where
    normalise' (x,y,z) =
        do  (x,(y,z)) <- normalise' (x,(y,z))
            return (x,y,z)

instance Normalise Bool where
  normalise' = return

instance Normalise Char where
  normalise' = return

instance Normalise Int where
  normalise' = return

instance Normalise DBPatVar where
  normalise' = return

-- interesting instances:

instance Normalise Sort where
    normalise' s = do
      s <- reduce' s
      case s of
        PiSort a s1 s2 -> piSort <$> normalise' a <*> normalise' s1 <*> normalise' s2
        FunSort s1 s2 -> funSort <$> normalise' s1 <*> normalise' s2
        UnivSort s -> univSort <$> normalise' s
        Univ u s   -> Univ u <$> normalise' s
        Inf _ _    -> return s
        SizeUniv   -> return SizeUniv
        LockUniv   -> return LockUniv
        LevelUniv  -> return LevelUniv
        IntervalUniv -> return IntervalUniv
        MetaS x es -> return s
        DefS d es  -> return s
        DummyS{}   -> return s

instance Normalise t => Normalise (Type' t) where
    normalise' (El s t) = El <$> normalise' s <*> normalise' t

instance Normalise Term where
    normalise' v = ifM shouldTryFastReduce (fastNormalise v) (slowNormaliseArgs =<< reduce' v)

slowNormaliseArgs :: Term -> ReduceM Term
slowNormaliseArgs = \case
  Var n vs    -> Var n      <$> normalise' vs
  Con c ci vs -> Con c ci   <$> normalise' vs
  Def f vs    -> Def f      <$> normalise' vs
  MetaV x vs  -> MetaV x    <$> normalise' vs
  v@(Lit _)   -> return v
  Level l     -> levelTm    <$> normalise' l
  Lam h b     -> Lam h      <$> normalise' b
  Sort s      -> Sort       <$> normalise' s
  Pi a b      -> uncurry Pi <$> normalise' (a, b)
  v@DontCare{}-> return v
  v@Dummy{}   -> return v

-- Note: not the default instance for Elim' since we do something special for Arg.
instance Normalise t => Normalise (Elim' t) where
  normalise' (Apply v) = Apply <$> normalise' v  -- invokes Normalise Arg here
  normalise' (Proj o f)= pure $ Proj o f
  normalise' (IApply x y v) = IApply <$> normalise' x <*> normalise' y <*> normalise' v

instance Normalise Level where
  normalise' (Max m as) = levelMax m <$> normalise' as

instance Normalise PlusLevel where
  normalise' (Plus n l) = Plus n <$> normalise' l

instance (Subst a, Normalise a) => Normalise (Abs a) where
    normalise' a@(Abs x _) = Abs x <$> underAbstraction_ a normalise'
    normalise' (NoAbs x v) = NoAbs x <$> normalise' v

instance Normalise t => Normalise (Arg t) where
    normalise' a
      | isIrrelevant a = return a -- Andreas, 2012-04-02: Do not normalize irrelevant terms!?
      | otherwise      = traverse normalise' a

instance Normalise t => Normalise (Dom t) where
    normalise' = traverse normalise'

instance Normalise a => Normalise (Closure a) where
    normalise' cl = do
        x <- enterClosure cl normalise'
        return $ cl { clValue = x }

instance (Subst a, Normalise a) => Normalise (Tele a) where
  normalise' EmptyTel        = return EmptyTel
  normalise' (ExtendTel a b) = uncurry ExtendTel <$> normalise' (a, b)

instance Normalise ProblemConstraint where
  normalise' (PConstr pid unblock c) = PConstr pid unblock <$> normalise' c

instance Normalise Constraint where
  normalise' (ValueCmp cmp t u v) = do
    (t,u,v) <- normalise' (t,u,v)
    return $ ValueCmp cmp t u v
  normalise' (ValueCmpOnFace cmp p t u v) = do
    ((p,t),u,v) <- normalise' ((p,t),u,v)
    return $ ValueCmpOnFace cmp p t u v
  normalise' (ElimCmp cmp fs t v as bs) =
    ElimCmp cmp fs <$> normalise' t <*> normalise' v <*> normalise' as <*> normalise' bs
  normalise' (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> normalise' (u,v)
  normalise' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> normalise' (a,b)
  normalise' (UnBlock m)           = return $ UnBlock m
  normalise' (FindInstance m cs)   = FindInstance m <$> mapM normalise' cs
  normalise' (IsEmpty r t)         = IsEmpty r <$> normalise' t
  normalise' (CheckSizeLtSat t)    = CheckSizeLtSat <$> normalise' t
  normalise' c@CheckFunDef{}       = return c
  normalise' (HasBiggerSort a)     = HasBiggerSort <$> normalise' a
  normalise' (HasPTSRule a b)      = uncurry HasPTSRule <$> normalise' (a,b)
  normalise' (UnquoteTactic t h g) = UnquoteTactic <$> normalise' t <*> normalise' h <*> normalise' g
  normalise' (CheckLockedVars a b c d) =
    CheckLockedVars <$> normalise' a <*> normalise' b <*> normalise' c <*> normalise' d
  normalise' (CheckDataSort q s)   = CheckDataSort q <$> normalise' s
  normalise' c@CheckMetaInst{}     = return c
  normalise' (CheckType t)         = CheckType <$> normalise' t
  normalise' (UsableAtModality cc ms mod t) = flip (UsableAtModality cc) mod <$> normalise' ms <*> normalise' t

instance Normalise CompareAs where
  normalise' (AsTermsOf a) = AsTermsOf <$> normalise' a
  normalise' AsSizes       = return AsSizes
  normalise' AsTypes       = return AsTypes

instance Normalise ConPatternInfo where
  normalise' i = normalise' (conPType i) <&> \ t -> i { conPType = t }

instance Normalise a => Normalise (Pattern' a) where
  normalise' p = case p of
    VarP o x     -> VarP o <$> normalise' x
    LitP{}       -> return p
    ConP c mt ps -> ConP c <$> normalise' mt <*> normalise' ps
    DefP o q ps  -> DefP o q <$> normalise' ps
    DotP o v     -> DotP o <$> normalise' v
    ProjP{}      -> return p
    IApplyP o t u x -> IApplyP o <$> normalise' t <*> normalise' u <*> normalise' x

instance Normalise DisplayForm where
  normalise' (Display n ps v) = Display n <$> normalise' ps <*> return v

instance Normalise Candidate where
  normalise' (Candidate q u t ov) = Candidate q <$> normalise' u <*> normalise' t <*> pure ov

instance Normalise EqualityView where
  normalise' (OtherType t)            = OtherType
    <$> normalise' t
  normalise' (IdiomType t)            = IdiomType
    <$> normalise' t
  normalise' (EqualityType s eq l t a b) = EqualityType
    <$> normalise' s
    <*> return eq
    <*> mapM normalise' l
    <*> normalise' t
    <*> normalise' a
    <*> normalise' b

---------------------------------------------------------------------------
-- * Full instantiation
---------------------------------------------------------------------------

-- | @instantiateFull'@ 'instantiate's metas everywhere (and recursively)
--   but does not 'reduce'.
class InstantiateFull t where
  instantiateFull' :: t -> ReduceM t

  default instantiateFull' :: (t ~ f a, Traversable f, InstantiateFull a) => t -> ReduceM t
  instantiateFull' = traverse instantiateFull'

-- Traversables (doesn't include binders like Abs, Tele):

instance InstantiateFull t => InstantiateFull [t]
instance InstantiateFull t => InstantiateFull (HashMap k t)
instance InstantiateFull t => InstantiateFull (Map k t)
instance InstantiateFull t => InstantiateFull (Maybe t)
instance InstantiateFull t => InstantiateFull (Strict.Maybe t)

instance InstantiateFull t => InstantiateFull (Arg t)
instance InstantiateFull t => InstantiateFull (Elim' t)
instance InstantiateFull t => InstantiateFull (Named name t)
instance InstantiateFull t => InstantiateFull (WithArity t)
instance InstantiateFull t => InstantiateFull (IPBoundary' t)

-- Tuples:

instance (InstantiateFull a, InstantiateFull b) => InstantiateFull (a,b) where
    instantiateFull' (x,y) = (,) <$> instantiateFull' x <*> instantiateFull' y

instance (InstantiateFull a, InstantiateFull b, InstantiateFull c) => InstantiateFull (a,b,c) where
    instantiateFull' (x,y,z) =
        do  (x,(y,z)) <- instantiateFull' (x,(y,z))
            return (x,y,z)

instance (InstantiateFull a, InstantiateFull b, InstantiateFull c, InstantiateFull d) => InstantiateFull (a,b,c,d) where
    instantiateFull' (x,y,z,w) =
        do  (x,(y,z,w)) <- instantiateFull' (x,(y,z,w))
            return (x,y,z,w)

-- Base types:

instance InstantiateFull Bool where
    instantiateFull' = return

instance InstantiateFull Char where
    instantiateFull' = return

instance InstantiateFull Int where
    instantiateFull' = return

instance InstantiateFull ModuleName where
    instantiateFull' = return

instance InstantiateFull Name where
    instantiateFull' = return

instance InstantiateFull QName where
  instantiateFull' = return

instance InstantiateFull Scope where
    instantiateFull' = return

instance InstantiateFull ConHead where
  instantiateFull' = return

instance InstantiateFull DBPatVar where
    instantiateFull' = return

-- Rest:

instance InstantiateFull Sort where
    instantiateFull' s = do
        s <- instantiate' s
        case s of
            Univ u n   -> Univ u <$> instantiateFull' n
            PiSort a s1 s2 -> piSort <$> instantiateFull' a <*> instantiateFull' s1 <*> instantiateFull' s2
            FunSort s1 s2 -> funSort <$> instantiateFull' s1 <*> instantiateFull' s2
            UnivSort s -> univSort <$> instantiateFull' s
            Inf _ _    -> return s
            SizeUniv   -> return s
            LockUniv   -> return s
            LevelUniv  -> return s
            IntervalUniv -> return s
            MetaS x es -> MetaS x <$> instantiateFull' es
            DefS d es  -> DefS d <$> instantiateFull' es
            DummyS{}   -> return s

instance InstantiateFull t => InstantiateFull (Type' t) where
    instantiateFull' (El s t) =
      El <$> instantiateFull' s <*> instantiateFull' t

instance InstantiateFull Term where
    instantiateFull' = instantiate' >=> recurse >=> etaOnce
      -- Andreas, 2010-11-12 DONT ETA!? eta-reduction breaks subject reduction
      -- but removing etaOnce now breaks everything
      where
        recurse = \case
          Var n vs    -> Var n <$> instantiateFull' vs
          Con c ci vs -> Con c ci <$> instantiateFull' vs
          Def f vs    -> Def f <$> instantiateFull' vs
          MetaV x vs  -> MetaV x <$> instantiateFull' vs
          v@Lit{}     -> return v
          Level l     -> levelTm <$> instantiateFull' l
          Lam h b     -> Lam h <$> instantiateFull' b
          Sort s      -> Sort <$> instantiateFull' s
          Pi a b      -> uncurry Pi <$> instantiateFull' (a,b)
          DontCare v  -> dontCare <$> instantiateFull' v
          v@Dummy{}   -> return v

instance InstantiateFull Level where
  instantiateFull' (Max m as) = levelMax m <$> instantiateFull' as

instance InstantiateFull PlusLevel where
  instantiateFull' (Plus n l) = Plus n <$> instantiateFull' l

instance InstantiateFull Substitution where
  instantiateFull' sigma =
    case sigma of
      IdS                    -> return IdS
      EmptyS err             -> return $ EmptyS err
      Wk   n sigma           -> Wk   n           <$> instantiateFull' sigma
      Lift n sigma           -> Lift n           <$> instantiateFull' sigma
      Strengthen bot n sigma -> Strengthen bot n <$> instantiateFull' sigma
      t :# sigma             -> consS <$> instantiateFull' t
                                      <*> instantiateFull' sigma

instance InstantiateFull ConPatternInfo where
    instantiateFull' i = instantiateFull' (conPType i) <&> \ t -> i { conPType = t }

instance InstantiateFull a => InstantiateFull (Pattern' a) where
    instantiateFull' (VarP o x)     = VarP o <$> instantiateFull' x
    instantiateFull' (DotP o t)     = DotP o <$> instantiateFull' t
    instantiateFull' (ConP n mt ps) = ConP n <$> instantiateFull' mt <*> instantiateFull' ps
    instantiateFull' (DefP o q ps) = DefP o q <$> instantiateFull' ps
    instantiateFull' l@LitP{}       = return l
    instantiateFull' p@ProjP{}      = return p
    instantiateFull' (IApplyP o t u x) = IApplyP o <$> instantiateFull' t <*> instantiateFull' u <*> instantiateFull' x

instance (Subst a, InstantiateFull a) => InstantiateFull (Abs a) where
    instantiateFull' a@(Abs x _) = Abs x <$> underAbstraction_ a instantiateFull'
    instantiateFull' (NoAbs x a) = NoAbs x <$> instantiateFull' a

instance (InstantiateFull t, InstantiateFull e) => InstantiateFull (Dom' t e) where
    instantiateFull' (Dom i n b tac x) = Dom i n b <$> instantiateFull' tac <*> instantiateFull' x

instance InstantiateFull LetBinding where
  instantiateFull' (LetBinding o v t) = LetBinding o <$> instantiateFull' v <*> instantiateFull' t

-- Andreas, 2021-09-13, issue #5544, need to traverse @checkpoints@ map
instance InstantiateFull t => InstantiateFull (Open t) where
  instantiateFull' (OpenThing checkpoint checkpoints modl t) =
    OpenThing checkpoint
    <$> (instantiateFull' =<< prune checkpoints)
    <*> pure modl
    <*> instantiateFull' t
    where
      -- Ulf, 2021-11-17, #5544
      --  Remove checkpoints that are no longer in scope, since they can
      --  mention functions that deadcode elimination will get rid of.
      prune cps = do
        inscope <- viewTC eCheckpoints
        return $ cps `Map.intersection` inscope

instance InstantiateFull a => InstantiateFull (Closure a) where
    instantiateFull' cl = do
        x <- enterClosure cl instantiateFull'
        return $ cl { clValue = x }

instance InstantiateFull ProblemConstraint where
  instantiateFull' (PConstr p u c) = PConstr p u <$> instantiateFull' c

instance InstantiateFull Constraint where
  instantiateFull' = \case
    ValueCmp cmp t u v -> do
      (t,u,v) <- instantiateFull' (t,u,v)
      return $ ValueCmp cmp t u v
    ValueCmpOnFace cmp p t u v -> do
      ((p,t),u,v) <- instantiateFull' ((p,t),u,v)
      return $ ValueCmpOnFace cmp p t u v
    ElimCmp cmp fs t v as bs ->
      ElimCmp cmp fs <$> instantiateFull' t <*> instantiateFull' v <*> instantiateFull' as <*> instantiateFull' bs
    LevelCmp cmp u v    -> uncurry (LevelCmp cmp) <$> instantiateFull' (u,v)
    SortCmp cmp a b     -> uncurry (SortCmp cmp) <$> instantiateFull' (a,b)
    UnBlock m           -> return $ UnBlock m
    FindInstance m cs   -> FindInstance m <$> mapM instantiateFull' cs
    IsEmpty r t         -> IsEmpty r <$> instantiateFull' t
    CheckSizeLtSat t    -> CheckSizeLtSat <$> instantiateFull' t
    c@CheckFunDef{}     -> return c
    HasBiggerSort a     -> HasBiggerSort <$> instantiateFull' a
    HasPTSRule a b      -> uncurry HasPTSRule <$> instantiateFull' (a,b)
    UnquoteTactic t g h -> UnquoteTactic <$> instantiateFull' t <*> instantiateFull' g <*> instantiateFull' h
    CheckLockedVars a b c d ->
      CheckLockedVars <$> instantiateFull' a <*> instantiateFull' b <*> instantiateFull' c <*> instantiateFull' d
    CheckDataSort q s   -> CheckDataSort q <$> instantiateFull' s
    c@CheckMetaInst{}   -> return c
    CheckType t         -> CheckType <$> instantiateFull' t
    UsableAtModality cc ms mod t -> flip (UsableAtModality cc) mod <$> instantiateFull' ms <*> instantiateFull' t

instance InstantiateFull CompareAs where
  instantiateFull' (AsTermsOf a) = AsTermsOf <$> instantiateFull' a
  instantiateFull' AsSizes       = return AsSizes
  instantiateFull' AsTypes       = return AsTypes

instance InstantiateFull Signature where
  instantiateFull' (Sig a b c) = uncurry3 Sig <$> instantiateFull' (a, b, c)

instance InstantiateFull Section where
  instantiateFull' (Section tel) = Section <$> instantiateFull' tel

instance (Subst a, InstantiateFull a) => InstantiateFull (Tele a) where
  instantiateFull' EmptyTel = return EmptyTel
  instantiateFull' (ExtendTel a b) = uncurry ExtendTel <$> instantiateFull' (a, b)

instance InstantiateFull Definition where
    instantiateFull' def@Defn{ defType = t ,defDisplay = df, theDef = d } = do
      (t, df, d) <- instantiateFull' (t, df, d)
      return $ def{ defType = t, defDisplay = df, theDef = d }

instance InstantiateFull NLPat where
  instantiateFull' (PVar x y) = return $ PVar x y
  instantiateFull' (PDef x y) = PDef <$> instantiateFull' x <*> instantiateFull' y
  instantiateFull' (PLam x y) = PLam x <$> instantiateFull' y
  instantiateFull' (PPi x y)  = PPi <$> instantiateFull' x <*> instantiateFull' y
  instantiateFull' (PSort x)  = PSort <$> instantiateFull' x
  instantiateFull' (PBoundVar x y) = PBoundVar x <$> instantiateFull' y
  instantiateFull' (PTerm x)  = PTerm <$> instantiateFull' x

instance InstantiateFull NLPType where
  instantiateFull' (NLPType s a) = NLPType
    <$> instantiateFull' s
    <*> instantiateFull' a

instance InstantiateFull NLPSort where
  instantiateFull' (PUniv u x) = PUniv u <$> instantiateFull' x
  instantiateFull' (PInf f n) = return $ PInf f n
  instantiateFull' PSizeUniv = return PSizeUniv
  instantiateFull' PLockUniv = return PLockUniv
  instantiateFull' PLevelUniv = return PLevelUniv
  instantiateFull' PIntervalUniv = return PIntervalUniv

instance InstantiateFull RewriteRule where
  instantiateFull' (RewriteRule q gamma f ps rhs t c) =
    RewriteRule q
      <$> instantiateFull' gamma
      <*> pure f
      <*> instantiateFull' ps
      <*> instantiateFull' rhs
      <*> instantiateFull' t
      <*> pure c

instance InstantiateFull DisplayForm where
  instantiateFull' (Display n ps v) = uncurry (Display n) <$> instantiateFull' (ps, v)

instance InstantiateFull DisplayTerm where
  instantiateFull' (DTerm' v es)   = DTerm' <$> instantiateFull' v <*> instantiateFull' es
  instantiateFull' (DDot' v es)    = DDot'  <$> instantiateFull' v <*> instantiateFull' es
  instantiateFull' (DCon c ci vs)  = DCon c ci <$> instantiateFull' vs
  instantiateFull' (DDef c es)     = DDef c <$> instantiateFull' es
  instantiateFull' (DWithApp v vs ws) = uncurry3 DWithApp <$> instantiateFull' (v, vs, ws)

instance InstantiateFull Defn where
    instantiateFull' d = case d of
      Axiom{} -> return d
      DataOrRecSig{} -> return d
      GeneralizableVar{} -> return d
      AbstractDefn d -> AbstractDefn <$> instantiateFull' d
      Function{ funClauses = cs, funCompiled = cc, funCovering = cov, funInv = inv, funExtLam = extLam } -> do
        (cs, cc, cov, inv) <- instantiateFull' (cs, cc, cov, inv)
        extLam <- instantiateFull' extLam
        return $ d { funClauses = cs, funCompiled = cc, funCovering = cov, funInv = inv, funExtLam = extLam }
      Datatype{ dataSort = s, dataClause = cl } -> do
        s  <- instantiateFull' s
        cl <- instantiateFull' cl
        return $ d { dataSort = s, dataClause = cl }
      Record{ recClause = cl, recTel = tel } -> do
        cl  <- instantiateFull' cl
        tel <- instantiateFull' tel
        return $ d { recClause = cl, recTel = tel }
      Constructor{} -> return d
      Primitive{ primClauses = cs } -> do
        cs <- instantiateFull' cs
        return $ d { primClauses = cs }
      PrimitiveSort{} -> return d

instance InstantiateFull ExtLamInfo where
  instantiateFull' e@(ExtLamInfo { extLamSys = sys}) = do
    sys <- instantiateFull' sys
    return $ e { extLamSys = sys}

instance InstantiateFull System where
  instantiateFull' (System tel sys) = System <$> instantiateFull' tel <*> instantiateFull' sys

instance InstantiateFull FunctionInverse where
  instantiateFull' NotInjective = return NotInjective
  instantiateFull' (Inverse inv) = Inverse <$> instantiateFull' inv

instance InstantiateFull a => InstantiateFull (Case a) where
  instantiateFull' (Branches cop cs eta ls m b lz) =
    Branches cop
      <$> instantiateFull' cs
      <*> instantiateFull' eta
      <*> instantiateFull' ls
      <*> instantiateFull' m
      <*> pure b
      <*> pure lz

instance InstantiateFull CompiledClauses where
  instantiateFull' (Fail xs)   = return $ Fail xs
  instantiateFull' (Done m t)  = Done m <$> instantiateFull' t
  instantiateFull' (Case n bs) = Case n <$> instantiateFull' bs

instance InstantiateFull Clause where
    instantiateFull' (Clause rl rf tel ps b t catchall exact recursive unreachable ell wm) =
       Clause rl rf <$> instantiateFull' tel
       <*> instantiateFull' ps
       <*> instantiateFull' b
       <*> instantiateFull' t
       <*> return catchall
       <*> return exact
       <*> return recursive
       <*> return unreachable
       <*> return ell
       <*> return wm

instance InstantiateFull Instantiation where
  instantiateFull' (Instantiation a b) =
    Instantiation a <$> instantiateFull' b

instance InstantiateFull (Judgement MetaId) where
  instantiateFull' (HasType a b c) =
    HasType a b <$> instantiateFull' c
  instantiateFull' (IsSort a b) =
    IsSort a <$> instantiateFull' b

instance InstantiateFull RemoteMetaVariable where
  instantiateFull' (RemoteMetaVariable a b c) = RemoteMetaVariable
    <$> instantiateFull' a
    <*> return b
    <*> instantiateFull' c

instance InstantiateFull Interface where
  instantiateFull' i = do
    defs <- instantiateFull' (i ^. intSignature . sigDefinitions)
    instantiateFullExceptForDefinitions'
      (set (intSignature . sigDefinitions) defs i)

-- | Instantiates everything except for definitions in the signature.

instantiateFullExceptForDefinitions' :: Interface -> ReduceM Interface
instantiateFullExceptForDefinitions'
  (Interface h s ft ms mod tlmod scope inside sig metas display userwarn
     importwarn b foreignCode highlighting libPragmas filePragmas
     usedOpts patsyns warnings partialdefs oblocks onames) =
  Interface h s ft ms mod tlmod scope inside
    <$> ((\s r -> Sig { _sigSections     = s
                      , _sigDefinitions  = sig ^. sigDefinitions
                      , _sigRewriteRules = r
                      })
         <$> instantiateFull' (sig ^. sigSections)
         <*> instantiateFull' (sig ^. sigRewriteRules))
    <*> instantiateFull' metas
    <*> instantiateFull' display
    <*> return userwarn
    <*> return importwarn
    <*> instantiateFull' b
    <*> return foreignCode
    <*> return highlighting
    <*> return libPragmas
    <*> return filePragmas
    <*> return usedOpts
    <*> return patsyns
    <*> return warnings
    <*> return partialdefs
    <*> return oblocks
    <*> return onames

-- | Instantiates everything except for definitions in the signature.

instantiateFullExceptForDefinitions ::
  MonadReduce m => Interface -> m Interface
instantiateFullExceptForDefinitions =
  liftReduce . instantiateFullExceptForDefinitions'

instance InstantiateFull a => InstantiateFull (Builtin a) where
    instantiateFull' (Builtin t) = Builtin <$> instantiateFull' t
    instantiateFull' (Prim x)   = Prim <$> instantiateFull' x
    instantiateFull' b@(BuiltinRewriteRelations xs) = pure b

instance InstantiateFull Candidate where
  instantiateFull' (Candidate q u t ov) =
    Candidate q <$> instantiateFull' u <*> instantiateFull' t <*> pure ov

instance InstantiateFull EqualityView where
  instantiateFull' (OtherType t)            = OtherType
    <$> instantiateFull' t
  instantiateFull' (IdiomType t)            = IdiomType
    <$> instantiateFull' t
  instantiateFull' (EqualityType s eq l t a b) = EqualityType
    <$> instantiateFull' s
    <*> return eq
    <*> mapM instantiateFull' l
    <*> instantiateFull' t
    <*> instantiateFull' a
    <*> instantiateFull' b
