{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}

module Agda.TypeChecking.Reduce where

import Prelude hiding (mapM)
import Control.Monad.Reader hiding (mapM)

import Data.Maybe
import Data.Map (Map)
import Data.Traversable
import Data.HashMap.Strict (HashMap)

import Agda.Interaction.Options

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Scope.Base (Scope)
import Agda.Syntax.Literal

import {-# SOURCE #-} Agda.TypeChecking.Irrelevance (workOnTypes, isPropM)
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

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Tuple
import qualified Agda.Utils.SmallSet as SmallSet

import Agda.Utils.Impossible

instantiate :: (Instantiate a, MonadReduce m) => a -> m a
instantiate = liftReduce . instantiate'

instantiateFull :: (InstantiateFull a, MonadReduce m) => a -> m a
instantiateFull = liftReduce . instantiateFull'

reduce :: (Reduce a, MonadReduce m) => a -> m a
reduce = liftReduce . reduce'

reduceB :: (Reduce a, MonadReduce m) => a -> m (Blocked a)
reduceB = liftReduce . reduceB'

normalise :: (Normalise a, MonadReduce m) => a -> m a
normalise = liftReduce . normalise'

-- | Normalise the given term but also preserve blocking tags
--   TODO: implement a more efficient version of this.
normaliseB :: (MonadReduce m, Reduce t, Normalise t) => t -> m (Blocked t)
normaliseB = normalise >=> reduceB

simplify :: (Simplify a, MonadReduce m) => a -> m a
simplify = liftReduce . simplify'

-- | Meaning no metas left in the instantiation.
isFullyInstantiatedMeta :: MetaId -> TCM Bool
isFullyInstantiatedMeta m = do
  mv <- lookupMeta m
  case mvInstantiation mv of
    InstV _tel v -> noMetas <$> instantiateFull v
    _ -> return False

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

instance (Instantiate a, Instantiate b) => Instantiate (a,b) where
    instantiate' (x,y) = (,) <$> instantiate' x <*> instantiate' y

instance (Instantiate a, Instantiate b,Instantiate c) => Instantiate (a,b,c) where
    instantiate' (x,y,z) = (,,) <$> instantiate' x <*> instantiate' y <*> instantiate' z

instance Instantiate Term where
  instantiate' t@(MetaV x es) = do
    blocking <- view stInstantiateBlocking <$> getTCState

    mv <- lookupMeta x
    let mi = mvInstantiation mv

    case mi of
      InstV tel v -> instantiate' inst
        where
          -- A slight complication here is that the meta might be underapplied,
          -- in which case we have to build the lambda abstraction before
          -- applying the substitution, or overapplied in which case we need to
          -- fall back to applyE.
          (es1, es2) = splitAt (length tel) es
          vs1 = reverse $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es1
          rho = vs1 ++# wkS (length vs1) idS
                -- really should be .. ++# emptyS but using wkS makes it reduce to idS
                -- when applicable
          -- specification: inst == foldr mkLam v tel `applyE` es
          inst = applySubst rho (foldr mkLam v $ drop (length es1) tel) `applyE` es2
      _ | Just m' <- mvTwin mv, blocking -> do
            instantiate' (MetaV m' es)
      Open                             -> return t
      OpenInstance                     -> return t
      BlockedConst u | blocking  -> instantiate' . unBrave $ BraveTerm u `applyE` es
                     | otherwise -> return t
      PostponedTypeCheckingProblem _ _ -> return t
  instantiate' (Level l) = levelTm <$> instantiate' l
  instantiate' (Sort s) = Sort <$> instantiate' s
  instantiate' t = return t

instance Instantiate t => Instantiate (Type' t) where
  instantiate' (El s t) = El <$> instantiate' s <*> instantiate' t

instance Instantiate Level where
  instantiate' (Max m as) = levelMax m <$> instantiate' as

-- Note: since @PlusLevel' t@ embeds a @LevelAtom' t@, simply
-- using @traverse@ for @PlusLevel'@ would not be not correct.
instance Instantiate PlusLevel where
  instantiate' (Plus n a) = Plus n <$> instantiate' a

instance Instantiate LevelAtom where
  instantiate' l = case l of
    MetaLevel m vs -> do
      v <- instantiate' (MetaV m vs)
      case v of
        MetaV m vs -> return $ MetaLevel m vs
        _          -> return $ UnreducedLevel v
    UnreducedLevel l -> UnreducedLevel <$> instantiate' l
    _ -> return l

instance Instantiate a => Instantiate (Blocked a) where
  instantiate' v@NotBlocked{} = return v
  instantiate' v@(Blocked x u) = do
    mi <- mvInstantiation <$> lookupMeta x
    case mi of
      InstV{}                        -> notBlocked <$> instantiate' u
      Open                           -> return v
      OpenInstance                   -> return v
      BlockedConst{}                 -> return v
      PostponedTypeCheckingProblem{} -> return v

instance Instantiate Sort where
  instantiate' s = case s of
    MetaS x es -> instantiate' (MetaV x es) >>= \case
      Sort s'      -> return s'
      MetaV x' es' -> return $ MetaS x' es'
      Def d es'     -> return $ DefS d es'
      _            -> __IMPOSSIBLE__
    _ -> return s

instance (Instantiate t, Instantiate e) => Instantiate (Dom' t e) where
    instantiate' (Dom i fin n tac x) = Dom i fin n <$> instantiate' tac <*> instantiate' x

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
  instantiate' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp)  <$> instantiate' (tela,telb)
  instantiate' (SortCmp cmp a b)    = uncurry (SortCmp cmp) <$> instantiate' (a,b)
  instantiate' (Guarded c pid)      = Guarded <$> instantiate' c <*> pure pid
  instantiate' (UnBlock m)          = return $ UnBlock m
  instantiate' (FindInstance m b args) = FindInstance m b <$> mapM instantiate' args
  instantiate' (IsEmpty r t)        = IsEmpty r <$> instantiate' t
  instantiate' (CheckSizeLtSat t)   = CheckSizeLtSat <$> instantiate' t
  instantiate' c@CheckFunDef{}      = return c
  instantiate' (HasBiggerSort a)    = HasBiggerSort <$> instantiate' a
  instantiate' (HasPTSRule a b)     = uncurry HasPTSRule <$> instantiate' (a,b)
  instantiate' (UnquoteTactic m t h g) = UnquoteTactic m <$> instantiate' t <*> instantiate' h <*> instantiate' g
  instantiate' c@CheckMetaInst{}    = return c

instance Instantiate CompareAs where
  instantiate' (AsTermsOf a) = AsTermsOf <$> instantiate' a
  instantiate' AsSizes       = return AsSizes
  instantiate' AsTypes       = return AsTypes

instance Instantiate Candidate where
  instantiate' (Candidate q u t ov) = Candidate q <$> instantiate' u <*> instantiate' t <*> pure ov

instance Instantiate EqualityView where
  instantiate' (OtherType t)            = OtherType
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

class IsMeta a where
  isMeta :: HasBuiltins m => a -> m (Maybe MetaId)

instance IsMeta Term where
  isMeta (MetaV m _) = return $ Just m
  isMeta _           = return Nothing

instance IsMeta Type where
  isMeta = isMeta . unEl

instance IsMeta Level where
  isMeta = isMeta <=< reallyUnLevelView

instance IsMeta Sort where
  isMeta (MetaS m _) = return $ Just m
  isMeta _           = return Nothing

instance IsMeta CompareAs where
  isMeta (AsTermsOf a) = isMeta a
  isMeta AsSizes       = return Nothing
  isMeta AsTypes       = return Nothing

-- | Case on whether a term is blocked on a meta (or is a meta).
--   That means it can change its shape when the meta is instantiated.
ifBlocked
  :: (Reduce t, IsMeta t, MonadReduce m, HasBuiltins m)
  => t -> (MetaId -> t -> m a) -> (NotBlocked -> t -> m a) -> m a
ifBlocked t blocked unblocked = do
  t <- reduceB t
  case t of
    Blocked m t -> blocked m t
    NotBlocked nb t -> isMeta t >>= \case
      Just m    -> blocked m t
      Nothing   -> unblocked nb t

isBlocked
  :: (Reduce t, IsMeta t, MonadReduce m, HasBuiltins m)
  => t -> m (Maybe MetaId)
isBlocked t = ifBlocked t (\m _ -> return $ Just m) (\_ _ -> return Nothing)

class Reduce t where
    reduce'  :: t -> ReduceM t
    reduceB' :: t -> ReduceM (Blocked t)

    reduce'  t = ignoreBlocking <$> reduceB' t
    reduceB' t = notBlocked <$> reduce' t

instance Reduce Type where
    reduce'  (El s t) = workOnTypes $ El s <$> reduce' t
    reduceB' (El s t) = workOnTypes $ fmap (El s) <$> reduceB' t

instance Reduce Sort where
    reduce' s = do
      s <- instantiate' s
      case s of
        PiSort a s2 -> do
          (s1' , s2') <- reduce' (getSort a , s2)
          let a' = set lensSort s1' a
          maybe (return $ PiSort a' s2') reduce' $ piSort' a' s2'
        FunSort s1 s2 -> do
          (s1' , s2') <- reduce (s1 , s2)
          maybe (return $ FunSort s1' s2') reduce' $ funSort' s1' s2'
        UnivSort s' -> do
          s' <- reduce' s'
          ui <- univInf
          caseMaybe (univSort' ui s') (return $ UnivSort s') reduce'
        Prop s'    -> Prop <$> reduce' s'
        Type s'    -> Type <$> reduce' s'
        Inf        -> return Inf
        SizeUniv   -> return SizeUniv
        MetaS x es -> return s
        DefS d es  -> return s -- postulated sorts do not reduce
        DummyS{}   -> return s

instance Reduce Elim where
  reduce' (Apply v) = Apply <$> reduce' v
  reduce' (Proj o f)= pure $ Proj o f
  reduce' (IApply x y v) = IApply <$> reduce' x <*> reduce' y <*> reduce' v

instance Reduce Level where
  reduce'  (Max m as) = levelMax m <$> mapM reduce' as
  reduceB' (Max m as) = fmap (levelMax m) . traverse id <$> traverse reduceB' as

instance Reduce PlusLevel where
  reduceB' (Plus n l) = fmap (Plus n) <$> reduceB' l

instance Reduce LevelAtom where
  reduceB' l = case l of
    MetaLevel m vs   -> fromTm (MetaV m vs)
    NeutralLevel r v -> return $ NotBlocked r $ NeutralLevel r v
    BlockedLevel m v ->
      ifM (isInstantiatedMeta m) (fromTm v) (return $ Blocked m $ BlockedLevel m v)
    UnreducedLevel v -> fromTm v
    where
      fromTm v = do
        bv <- reduceB' v
        let v = ignoreBlocking bv
        case bv of
          NotBlocked r (MetaV m vs) -> return $ NotBlocked r $ MetaLevel m vs
          Blocked m _               -> return $ Blocked m    $ BlockedLevel m v
          NotBlocked r _            -> return $ NotBlocked r $ NeutralLevel r v


instance (Subst t a, Reduce a) => Reduce (Abs a) where
  reduce' b@(Abs x _) = Abs x <$> underAbstraction_ b reduce'
  reduce' (NoAbs x v) = NoAbs x <$> reduce' v

-- Lists are never blocked
instance Reduce t => Reduce [t] where
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

blockedOrMeta :: Blocked Term -> Blocked ()
blockedOrMeta r =
  case r of
    Blocked m _              -> Blocked m ()
    NotBlocked _ (MetaV m _) -> Blocked m ()
    NotBlocked i _           -> NotBlocked i ()

reduceIApply' :: (Term -> ReduceM (Blocked Term)) -> ReduceM (Blocked Term) -> [Elim] -> ReduceM (Blocked Term)
reduceIApply' red d (IApply x y r : es) = do
  view <- intervalView'
  r <- reduceB' r
  -- We need to propagate the blocking information so that e.g.
  -- we postpone "someNeutralPath ?0 = a" rather than fail.
  let blockedInfo = blockedOrMeta r

  case view (ignoreBlocking r) of
   IZero -> red (applyE x es)
   IOne  -> red (applyE y es)
   _     -> fmap (<* blockedInfo) (reduceIApply' red d es)
reduceIApply' red d (_ : es) = reduceIApply' red d es
reduceIApply' _   d [] = d

instance Reduce DeBruijnPattern where
  reduceB' (DotP o v) = fmap (DotP o) <$> reduceB' v
  reduceB' p          = return $ notBlocked p

instance Reduce Term where
  reduceB' = {-# SCC "reduce'<Term>" #-} maybeFastReduceTerm

shouldTryFastReduce :: ReduceM Bool
shouldTryFastReduce = (optFastReduce <$> pragmaOptions) `and2M` do
  allowed <- asksTC envAllowedReductions
  let optionalReductions = SmallSet.fromList [NonTerminatingReductions, UnconfirmedReductions]
      requiredReductions = allReductions SmallSet.\\ optionalReductions
  return $ (allowed SmallSet.\\ optionalReductions) == requiredReductions

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
      MetaV x _ -> ifM (isOpen x) (return $ notBlocked v) (maybeFast v)
      _         -> maybeFast v
  where
    isOpen x = isOpenMeta . mvInstantiation <$> lookupMeta x
    maybeFast v = ifM shouldTryFastReduce (fastReduce v) (slowReduceTerm v)

slowReduceTerm :: Term -> ReduceM (Blocked Term)
slowReduceTerm v = do
    v <- instantiate' v
    let done = return $ notBlocked v
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
      Sort s   -> fmap Sort <$> reduceB' s
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
          _ | Just v == mz  -> return $ Lit $ LitNat (getRange c) 0
          _                 -> return v
      reduceNat v@(Con c ci [Apply a]) | visible a && isRelevant a = do
        ms  <- getBuiltin' builtinSuc
        case v of
          _ | Just (Con c ci []) == ms -> inc <$> reduce' (unArg a)
          _                         -> return v
          where
            inc w = case w of
              Lit (LitNat r n) -> Lit (LitNat (fuseRange c r) $ n + 1)
              _                -> Con c ci [Apply $ defaultArg w]
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
  traceSDoc "tc.reduce" 90 ("unfoldDefinitionStep v0" <+> prettyTCM v0) $ do
  info <- getConstInfo f
  rewr <- instantiateRewriteRules =<< getRewriteRulesFor f
  allowed <- asksTC envAllowedReductions
  prp <- isPropM $ defType info
  let def = theDef info
      v   = v0 `applyE` es
      -- Non-terminating functions
      -- (i.e., those that failed the termination check)
      -- and delayed definitions
      -- are not unfolded unless explicitly permitted.
      dontUnfold =
        (defNonterminating info && SmallSet.notMember NonTerminatingReductions allowed)
        || (defTerminationUnconfirmed info && SmallSet.notMember UnconfirmedReductions allowed)
        || (defDelayed info == Delayed && not unfoldDelayed)
        || prp || isIrrelevant (defArgInfo info)
      copatterns = defCopatternLHS info
  case def of
    Constructor{conSrcCon = c} ->
      noReduction $ notBlocked $ Con (c `withRangeOf` f) ConOSystem [] `applyE` es
    Primitive{primAbstr = ConcreteDef, primName = x, primClauses = cls} -> do
      pf <- fromMaybe __IMPOSSIBLE__ <$> getPrimitive' x
      if FunctionReductions `SmallSet.member` allowed
        then reducePrimitive x v0 f es pf dontUnfold
                             cls (defCompiled info) rewr
        else noReduction $ notBlocked v
    _  -> do
      if (RecursiveReductions `SmallSet.member` allowed) ||
         (isJust (isProjection_ def) && ProjectionReductions `SmallSet.member` allowed) || -- includes projection-like
         (isInlineFun def && InlineReductions `SmallSet.member` allowed) ||
         (definitelyNonRecursive_ def && copatterns && CopatternReductions `SmallSet.member` allowed) ||
         (definitelyNonRecursive_ def && FunctionReductions `SmallSet.member` allowed)
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
                  traverse id $
                    map mredToBlocked es1' ++ map notBlocked es2
               else
                reduceNormalE v0 f (es1' ++ map notReduced es2) dontUnfold cls mcc rewr
            YesReduction simpl v -> yesReduction simpl $ v `applyE` es2
      where
          ar  = primFunArity pf
          mredToBlocked :: MaybeReduced a -> Blocked a
          mredToBlocked (MaybeRed NotReduced  x) = notBlocked x
          mredToBlocked (MaybeRed (Reduced b) x) = x <$ b

    reduceNormalE :: Term -> QName -> [MaybeReduced Elim] -> Bool -> [Clause] -> Maybe CompiledClauses -> RewriteRules -> ReduceM (Reduced (Blocked Term) Term)
    reduceNormalE v0 f es dontUnfold def mcc rewr = {-# SCC "reduceNormal" #-} do
      traceSDoc "tc.reduce" 90 ("reduceNormalE v0 =" <+> prettyTCM v0) $ do
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
              [ "*** tried to reduce " <+> prettyTCM f
              , "    es =  " <+> sep (map (prettyTCM . ignoreReduced) es)
              -- , "*** tried to reduce " <+> prettyTCM vfull
              , "    stuck on" <+> prettyTCM (ignoreBlocking v)
              ]
          YesReduction _simpl v -> do
            reportSDoc "tc.reduce"  90 $ "*** reduced definition: " <+> prettyTCM f
            reportSDoc "tc.reduce"  95 $ "    result" <+> prettyTCM v
            reportSDoc "tc.reduce" 100 $ "    raw   " <+> text (show v)

-- | Reduce a non-primitive definition if it is a copy linking to another def.
reduceDefCopy :: forall m. (MonadReduce m, HasConstInfo m, HasOptions m,
                            ReadTCState m, MonadTCEnv m, MonadDebug m)
              => QName -> Elims -> m (Reduced () Term)
reduceDefCopy f es = do
  info <- getConstInfo f
  rewr <- instantiateRewriteRules =<< getRewriteRulesFor f
  if (defCopy info) then reduceDef_ info rewr f es else return $ NoReduction ()
  where
    reduceDef_ :: Definition -> RewriteRules -> QName -> Elims -> m (Reduced () Term)
    reduceDef_ info rewr f es = do
      let v0   = Def f []
          cls  = (defClauses info)
          mcc  = (defCompiled info)
      if (defDelayed info == Delayed) || (defNonterminating info)
       then return $ NoReduction ()
       else do
          ev <- liftReduce $ appDefE_ f v0 cls mcc rewr $ map notReduced es
          case ev of
            YesReduction simpl t -> return $ YesReduction simpl t
            NoReduction{}        -> return $ NoReduction ()

-- | Reduce simple (single clause) definitions.
reduceHead :: (HasBuiltins m, HasConstInfo m, MonadReduce m, MonadDebug m)
           => Term -> m (Blocked Term)
reduceHead v = do -- ignoreAbstractMode $ do
  -- Andreas, 2013-02-18 ignoreAbstractMode leads to information leakage
  -- see Issue 796

  -- first, possibly rewrite literal v to constructor form
  v <- constructorForm v
  traceSDoc "tc.inj.reduce" 30 (ignoreAbstractMode $ "reduceHead" <+> prettyTCM v) $ do
  case v of
    Def f es -> do

      abstractMode <- envAbstractMode <$> askTC
      isAbstract <- treatAbstractly f
      traceSLn "tc.inj.reduce" 50 (
        "reduceHead: we are in " ++ show abstractMode++ "; " ++ show f ++
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
          traceSLn "tc.inj.reduce" 50 ("reduceHead: head " ++ show f ++ " is Function") $ do
          red
        Datatype{ dataClause = Just _ } -> red
        Record{ recClause = Just _ }    -> red
        _                               -> return $ notBlocked v
    _ -> return $ notBlocked v

-- | Unfold a single inlined function.
unfoldInlined :: (HasConstInfo m, MonadReduce m) => Term -> m Term
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
  maybe (appDefE' v0 cls rewr args)
        (\cc -> appDefE v0 cc rewr args) mcc


-- | Apply a defined function to it's arguments, using the compiled clauses.
--   The original term is the first argument applied to the third.
appDef :: Term -> CompiledClauses -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef v cc rewr args = appDefE v cc rewr $ map (fmap Apply) args

appDefE :: Term -> CompiledClauses -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE v cc rewr es = do
  traceSDoc "tc.reduce" 90 ("appDefE v = " <+> prettyTCM v) $ do
  r <- matchCompiledE cc es
  case r of
    YesReduction simpl t -> return $ YesReduction simpl t
    NoReduction es'      -> rewrite (void es') v rewr (ignoreBlocking es')

-- | Apply a defined function to it's arguments, using the original clauses.
appDef' :: Term -> [Clause] -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef' v cls rewr args = appDefE' v cls rewr $ map (fmap Apply) args

appDefE' :: Term -> [Clause] -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE' v cls rewr es = traceSDoc "tc.reduce" 90 ("appDefE' v = " <+> prettyTCM v) $ do
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
        [] -> rewrite (NotBlocked MissingClauses ()) v rewr es
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
              DontKnow b -> rewrite b v rewr es
              Yes simpl vs -- vs is the subst. for the variables bound in body
                | Just w <- body -> do -- clause has body?
                    -- TODO: let matchPatterns also return the reduced forms
                    -- of the original arguments!
                    -- Andreas, 2013-05-19 isn't this done now?
                    let sigma = buildSubstitution __IMPOSSIBLE__ nvars vs
                    return $ YesReduction simpl $ applySubst sigma w `applyE` es1
                | otherwise     -> rewrite (NotBlocked AbsurdMatch ()) v rewr es

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
  reduce' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp)  <$> reduce' (tela,telb)
  reduce' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> reduce' (a,b)
  reduce' (Guarded c pid)       = Guarded <$> reduce' c <*> pure pid
  reduce' (UnBlock m)           = return $ UnBlock m
  reduce' (FindInstance m b cands) = FindInstance m b <$> mapM reduce' cands
  reduce' (IsEmpty r t)         = IsEmpty r <$> reduce' t
  reduce' (CheckSizeLtSat t)    = CheckSizeLtSat <$> reduce' t
  reduce' c@CheckFunDef{}       = return c
  reduce' (HasBiggerSort a)     = HasBiggerSort <$> reduce' a
  reduce' (HasPTSRule a b)      = uncurry HasPTSRule <$> reduce' (a,b)
  reduce' (UnquoteTactic m t h g) = UnquoteTactic m <$> reduce' t <*> reduce' h <*> reduce' g
  reduce' c@CheckMetaInst{}     = return c

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
    case v of
      Def f vs   -> do
        let keepGoing simp v = return (simp, notBlocked v)
        (simpl, v) <- unfoldDefinition' False keepGoing (Def f []) f vs
        traceSDoc "tc.simplify'" 90 (
          text ("simplify': unfolding definition returns " ++ show simpl)
            <+> prettyTCM (ignoreBlocking v)) $ do
        case simpl of
          YesSimplification -> simplifyBlocked' v -- Dangerous, but if @simpl@ then @v /= Def f vs@
          NoSimplification  -> Def f <$> simplify' vs
      MetaV x vs -> MetaV x  <$> simplify' vs
      Con c ci vs-> Con c ci <$> simplify' vs
      Sort s     -> Sort     <$> simplify' s
      Level l    -> levelTm  <$> simplify' l
      Pi a b     -> Pi       <$> simplify' a <*> simplify' b
      Lit l      -> return v
      Var i vs   -> Var i    <$> simplify' vs
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
        PiSort a s -> piSort <$> simplify' a <*> simplify' s
        FunSort s1 s2 -> funSort <$> simplify' s1 <*> simplify' s2
        UnivSort s -> do
          ui <- univInf
          univSort ui <$> simplify' s
        Type s     -> Type <$> simplify' s
        Prop s     -> Prop <$> simplify' s
        Inf        -> return s
        SizeUniv   -> return s
        MetaS x es -> MetaS x <$> simplify' es
        DefS d es  -> DefS d <$> simplify' es
        DummyS{}   -> return s

instance Simplify Level where
  simplify' (Max m as) = levelMax m <$> simplify' as

instance Simplify PlusLevel where
  simplify' (Plus n l) = Plus n <$> simplify' l

instance Simplify LevelAtom where
  simplify' l = do
    l <- instantiate' l
    case l of
      MetaLevel m vs   -> MetaLevel m <$> simplify' vs
      BlockedLevel m v -> BlockedLevel m <$> simplify' v
      NeutralLevel r v -> NeutralLevel r <$> simplify' v -- ??
      UnreducedLevel v -> UnreducedLevel <$> simplify' v -- ??

instance (Subst t a, Simplify a) => Simplify (Abs a) where
    simplify' a@(Abs x _) = Abs x <$> underAbstraction_ a simplify'
    simplify' (NoAbs x v) = NoAbs x <$> simplify' v

instance Simplify t => Simplify (Dom t) where
    simplify' = traverse simplify'

instance Simplify a => Simplify (Closure a) where
    simplify' cl = do
        x <- enterClosure cl simplify'
        return $ cl { clValue = x }

instance (Subst t a, Simplify a) => Simplify (Tele a) where
  simplify' EmptyTel        = return EmptyTel
  simplify' (ExtendTel a b) = uncurry ExtendTel <$> simplify' (a, b)

instance Simplify ProblemConstraint where
  simplify' (PConstr pid c) = PConstr pid <$> simplify' c

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
  simplify' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp) <$> simplify' (tela,telb)
  simplify' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> simplify' (a,b)
  simplify' (Guarded c pid)       = Guarded <$> simplify' c <*> pure pid
  simplify' (UnBlock m)           = return $ UnBlock m
  simplify' (FindInstance m b cands) = FindInstance m b <$> mapM simplify' cands
  simplify' (IsEmpty r t)         = IsEmpty r <$> simplify' t
  simplify' (CheckSizeLtSat t)    = CheckSizeLtSat <$> simplify' t
  simplify' c@CheckFunDef{}       = return c
  simplify' (HasBiggerSort a)     = HasBiggerSort <$> simplify' a
  simplify' (HasPTSRule a b)      = uncurry HasPTSRule <$> simplify' (a,b)
  simplify' (UnquoteTactic m t h g) = UnquoteTactic m <$> simplify' t <*> simplify' h <*> simplify' g
  simplify' c@CheckMetaInst{}     = return c

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
        PiSort a s -> piSort <$> normalise' a <*> normalise' s
        FunSort s1 s2 -> funSort <$> normalise' s1 <*> normalise' s2
        UnivSort s -> do
          ui <- univInf
          univSort ui <$> normalise' s
        Prop s     -> Prop <$> normalise' s
        Type s     -> Type <$> normalise' s
        Inf        -> return Inf
        SizeUniv   -> return SizeUniv
        MetaS x es -> return s
        DefS d es  -> return s
        DummyS{}   -> return s

instance Normalise t => Normalise (Type' t) where
    normalise' (El s t) = El <$> normalise' s <*> normalise' t

instance Normalise Term where
    normalise' v = ifM shouldTryFastReduce (fastNormalise v) (slowNormaliseArgs =<< reduce' v)

slowNormaliseArgs :: Term -> ReduceM Term
slowNormaliseArgs v = case v of
  Var n vs    -> Var n      <$> normalise' vs
  Con c ci vs -> Con c ci   <$> normalise' vs
  Def f vs    -> Def f      <$> normalise' vs
  MetaV x vs  -> MetaV x    <$> normalise' vs
  Lit _       -> return v
  Level l     -> levelTm    <$> normalise' l
  Lam h b     -> Lam h      <$> normalise' b
  Sort s      -> Sort       <$> normalise' s
  Pi a b      -> uncurry Pi <$> normalise' (a, b)
  DontCare _  -> return v
  Dummy{}     -> return v

-- Note: not the default instance for Elim' since we do something special for Arg.
instance Normalise t => Normalise (Elim' t) where
  normalise' (Apply v) = Apply <$> normalise' v  -- invokes Normalise Arg here
  normalise' (Proj o f)= pure $ Proj o f
  normalise' (IApply x y v) = IApply <$> normalise' x <*> normalise' y <*> normalise' v

instance Normalise Level where
  normalise' (Max m as) = levelMax m <$> normalise' as

instance Normalise PlusLevel where
  normalise' (Plus n l) = Plus n <$> normalise' l

instance Normalise LevelAtom where
  normalise' l = do
    l <- reduce' l
    case l of
      MetaLevel m vs   -> MetaLevel m <$> normalise' vs
      BlockedLevel m v -> BlockedLevel m <$> normalise' v
      NeutralLevel r v -> NeutralLevel r <$> normalise' v
      UnreducedLevel{} -> __IMPOSSIBLE__    -- I hope

instance (Subst t a, Normalise a) => Normalise (Abs a) where
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

instance (Subst t a, Normalise a) => Normalise (Tele a) where
  normalise' EmptyTel        = return EmptyTel
  normalise' (ExtendTel a b) = uncurry ExtendTel <$> normalise' (a, b)

instance Normalise ProblemConstraint where
  normalise' (PConstr pid c) = PConstr pid <$> normalise' c

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
  normalise' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp) <$> normalise' (tela,telb)
  normalise' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> normalise' (a,b)
  normalise' (Guarded c pid)       = Guarded <$> normalise' c <*> pure pid
  normalise' (UnBlock m)           = return $ UnBlock m
  normalise' (FindInstance m b cands) = FindInstance m b <$> mapM normalise' cands
  normalise' (IsEmpty r t)         = IsEmpty r <$> normalise' t
  normalise' (CheckSizeLtSat t)    = CheckSizeLtSat <$> normalise' t
  normalise' c@CheckFunDef{}       = return c
  normalise' (HasBiggerSort a)     = HasBiggerSort <$> normalise' a
  normalise' (HasPTSRule a b)      = uncurry HasPTSRule <$> normalise' (a,b)
  normalise' (UnquoteTactic m t h g) = UnquoteTactic m <$> normalise' t <*> normalise' h <*> normalise' g
  normalise' c@CheckMetaInst{}     = return c

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
instance InstantiateFull t => InstantiateFull (Open t)
instance InstantiateFull t => InstantiateFull (WithArity t)

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
            Type n     -> Type <$> instantiateFull' n
            Prop n     -> Prop <$> instantiateFull' n
            PiSort a s -> piSort <$> instantiateFull' a <*> instantiateFull' s
            FunSort s1 s2 -> funSort <$> instantiateFull' s1 <*> instantiateFull' s2
            UnivSort s -> do
              ui <- univInf
              univSort ui <$> instantiateFull' s
            Inf        -> return s
            SizeUniv   -> return s
            MetaS x es -> MetaS x <$> instantiateFull' es
            DefS d es  -> DefS d <$> instantiateFull' es
            DummyS{}   -> return s

instance InstantiateFull t => InstantiateFull (Type' t) where
    instantiateFull' (El s t) =
      El <$> instantiateFull' s <*> instantiateFull' t

instance InstantiateFull Term where
    instantiateFull' v = etaOnce =<< do -- Andreas, 2010-11-12 DONT ETA!? eta-reduction breaks subject reduction
-- but removing etaOnce now breaks everything
      v <- instantiate' v
      case v of
          Var n vs    -> Var n <$> instantiateFull' vs
          Con c ci vs -> Con c ci <$> instantiateFull' vs
          Def f vs    -> Def f <$> instantiateFull' vs
          MetaV x vs  -> MetaV x <$> instantiateFull' vs
          Lit _       -> return v
          Level l     -> levelTm <$> instantiateFull' l
          Lam h b     -> Lam h <$> instantiateFull' b
          Sort s      -> Sort <$> instantiateFull' s
          Pi a b      -> uncurry Pi <$> instantiateFull' (a,b)
          DontCare v  -> dontCare <$> instantiateFull' v
          Dummy{}     -> return v

instance InstantiateFull Level where
  instantiateFull' (Max m as) = levelMax m <$> instantiateFull' as

instance InstantiateFull PlusLevel where
  instantiateFull' (Plus n l) = Plus n <$> instantiateFull' l

instance InstantiateFull LevelAtom where
  instantiateFull' l = case l of
    MetaLevel m vs -> do
      v <- instantiateFull' (MetaV m vs)
      case v of
        MetaV m vs -> return $ MetaLevel m vs
        _          -> return $ UnreducedLevel v
    NeutralLevel r v -> NeutralLevel r <$> instantiateFull' v
    BlockedLevel m v ->
      ifM (isInstantiatedMeta m)
          (UnreducedLevel <$> instantiateFull' v)
          (BlockedLevel m <$> instantiateFull' v)
    UnreducedLevel v -> UnreducedLevel <$> instantiateFull' v

instance InstantiateFull Substitution where
  instantiateFull' sigma =
    case sigma of
      IdS                  -> return IdS
      EmptyS err           -> return $ EmptyS err
      Wk   n sigma         -> Wk   n         <$> instantiateFull' sigma
      Lift n sigma         -> Lift n         <$> instantiateFull' sigma
      Strengthen bot sigma -> Strengthen bot <$> instantiateFull' sigma
      t :# sigma           -> consS <$> instantiateFull' t
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

instance (Subst t a, InstantiateFull a) => InstantiateFull (Abs a) where
    instantiateFull' a@(Abs x _) = Abs x <$> underAbstraction_ a instantiateFull'
    instantiateFull' (NoAbs x a) = NoAbs x <$> instantiateFull' a

instance (InstantiateFull t, InstantiateFull e) => InstantiateFull (Dom' t e) where
    instantiateFull' (Dom i fin n tac x) = Dom i fin n <$> instantiateFull' tac <*> instantiateFull' x

instance InstantiateFull a => InstantiateFull (Closure a) where
    instantiateFull' cl = do
        x <- enterClosure cl instantiateFull'
        return $ cl { clValue = x }

instance InstantiateFull ProblemConstraint where
  instantiateFull' (PConstr p c) = PConstr p <$> instantiateFull' c

instance InstantiateFull Constraint where
  instantiateFull' c = case c of
    ValueCmp cmp t u v -> do
      (t,u,v) <- instantiateFull' (t,u,v)
      return $ ValueCmp cmp t u v
    ValueCmpOnFace cmp p t u v -> do
      ((p,t),u,v) <- instantiateFull' ((p,t),u,v)
      return $ ValueCmpOnFace cmp p t u v
    ElimCmp cmp fs t v as bs ->
      ElimCmp cmp fs <$> instantiateFull' t <*> instantiateFull' v <*> instantiateFull' as <*> instantiateFull' bs
    LevelCmp cmp u v    -> uncurry (LevelCmp cmp) <$> instantiateFull' (u,v)
    TelCmp a b cmp tela telb -> uncurry (TelCmp a b cmp) <$> instantiateFull' (tela,telb)
    SortCmp cmp a b     -> uncurry (SortCmp cmp) <$> instantiateFull' (a,b)
    Guarded c pid       -> Guarded <$> instantiateFull' c <*> pure pid
    UnBlock m           -> return $ UnBlock m
    FindInstance m b cands -> FindInstance m b <$> mapM instantiateFull' cands
    IsEmpty r t         -> IsEmpty r <$> instantiateFull' t
    CheckSizeLtSat t    -> CheckSizeLtSat <$> instantiateFull' t
    c@CheckFunDef{}     -> return c
    HasBiggerSort a     -> HasBiggerSort <$> instantiateFull' a
    HasPTSRule a b      -> uncurry HasPTSRule <$> instantiateFull' (a,b)
    UnquoteTactic m t g h -> UnquoteTactic m <$> instantiateFull' t <*> instantiateFull' g <*> instantiateFull' h
    c@CheckMetaInst{}   -> return c

instance InstantiateFull CompareAs where
  instantiateFull' (AsTermsOf a) = AsTermsOf <$> instantiateFull' a
  instantiateFull' AsSizes       = return AsSizes
  instantiateFull' AsTypes       = return AsTypes

instance InstantiateFull Signature where
  instantiateFull' (Sig a b c) = uncurry3 Sig <$> instantiateFull' (a, b, c)

instance InstantiateFull Section where
  instantiateFull' (Section tel) = Section <$> instantiateFull' tel

instance (Subst t a, InstantiateFull a) => InstantiateFull (Tele a) where
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
  instantiateFull' (PType x) = PType <$> instantiateFull' x
  instantiateFull' (PProp x) = PProp <$> instantiateFull' x
  instantiateFull' PInf      = return PInf
  instantiateFull' PSizeUniv = return PSizeUniv

instance InstantiateFull RewriteRule where
  instantiateFull' (RewriteRule q gamma f ps rhs t) =
    RewriteRule q
      <$> instantiateFull' gamma
      <*> pure f
      <*> instantiateFull' ps
      <*> instantiateFull' rhs
      <*> instantiateFull' t

instance InstantiateFull DisplayForm where
  instantiateFull' (Display n ps v) = uncurry (Display n) <$> instantiateFull' (ps, v)

instance InstantiateFull DisplayTerm where
  instantiateFull' (DTerm v)       = DTerm <$> instantiateFull' v
  instantiateFull' (DDot  v)       = DDot  <$> instantiateFull' v
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
  instantiateFull' Fail        = return Fail
  instantiateFull' (Done m t)  = Done m <$> instantiateFull' t
  instantiateFull' (Case n bs) = Case n <$> instantiateFull' bs

instance InstantiateFull Clause where
    instantiateFull' (Clause rl rf tel ps b t catchall recursive unreachable ell) =
       Clause rl rf <$> instantiateFull' tel
       <*> instantiateFull' ps
       <*> instantiateFull' b
       <*> instantiateFull' t
       <*> return catchall
       <*> return recursive
       <*> return unreachable
       <*> return ell

instance InstantiateFull Interface where
    instantiateFull' (Interface h s ft ms mod scope inside
                               sig display userwarn importwarn b foreignCode
                               highlighting pragmas usedOpts patsyns warnings partialdefs) =
        Interface h s ft ms mod scope inside
            <$> instantiateFull' sig
            <*> instantiateFull' display
            <*> return userwarn
            <*> return importwarn
            <*> instantiateFull' b
            <*> return foreignCode
            <*> return highlighting
            <*> return pragmas
            <*> return usedOpts
            <*> return patsyns
            <*> return warnings
            <*> return partialdefs

instance InstantiateFull a => InstantiateFull (Builtin a) where
    instantiateFull' (Builtin t) = Builtin <$> instantiateFull' t
    instantiateFull' (Prim x)   = Prim <$> instantiateFull' x

instance InstantiateFull Candidate where
  instantiateFull' (Candidate q u t ov) =
    Candidate q <$> instantiateFull' u <*> instantiateFull' t <*> pure ov

instance InstantiateFull EqualityView where
  instantiateFull' (OtherType t)            = OtherType
    <$> instantiateFull' t
  instantiateFull' (EqualityType s eq l t a b) = EqualityType
    <$> instantiateFull' s
    <*> return eq
    <*> mapM instantiateFull' l
    <*> instantiateFull' t
    <*> instantiateFull' a
    <*> instantiateFull' b
