{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE UndecidableInstances     #-}

module Agda.TypeChecking.Reduce where

import Prelude hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Applicative

import Data.List as List hiding (sort)
import Data.Maybe
import Data.Map (Map)
import Data.Traversable
import Data.Hashable

import Agda.Interaction.Options

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Scope.Base (Scope)
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad hiding ( underAbstraction_, enterClosure, isInstantiatedMeta
                                      , getConstInfo
                                      , lookupMeta )
import qualified Agda.TypeChecking.Monad as TCM
import Agda.TypeChecking.Monad.Builtin hiding (getPrimitive, constructorForm)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.EtaContract

import Agda.TypeChecking.Reduce.Monad

import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Match
import {-# SOURCE #-} Agda.TypeChecking.Patterns.Match
import {-# SOURCE #-} Agda.TypeChecking.Pretty
import {-# SOURCE #-} Agda.TypeChecking.Rewriting
import {-# SOURCE #-} Agda.TypeChecking.Reduce.Fast

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Monad
import Agda.Utils.HashMap (HashMap)
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

instantiate :: Instantiate a => a -> TCM a
instantiate = runReduceM . instantiate'

instantiateFull :: InstantiateFull a => a -> TCM a
instantiateFull = runReduceM . instantiateFull'

reduce :: Reduce a => a -> TCM a
reduce = runReduceM . reduce'

reduceB :: Reduce a => a -> TCM (Blocked a)
reduceB = runReduceM . reduceB'

normalise :: Normalise a => a -> TCM a
normalise = runReduceM . normalise'

simplify :: Simplify a => a -> TCM a
simplify = runReduceM . simplify'

-- | Meaning no metas left in the instantiation.
isFullyInstantiatedMeta :: MetaId -> TCM Bool
isFullyInstantiatedMeta m = do
  mv <- TCM.lookupMeta m
  case mvInstantiation mv of
    InstV _tel v -> null . allMetas <$> instantiateFull v
    _ -> return False

-- | Instantiate something.
--   Results in an open meta variable or a non meta.
--   Doesn't do any reduction, and preserves blocking tags (when blocking meta
--   is uninstantiated).
class Instantiate t where
    instantiate' :: t -> ReduceM t

instance Instantiate Term where
  instantiate' t@(MetaV x es) = do
    mi <- mvInstantiation <$> lookupMeta x
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
      Open                             -> return t
      OpenIFS                          -> return t
      BlockedConst _                   -> return t
      PostponedTypeCheckingProblem _ _ -> return t
  instantiate' (Level l) = levelTm <$> instantiate' l
  instantiate' (Sort s) = sortTm <$> instantiate' s
  instantiate' v@Shared{} =
    updateSharedTerm instantiate' v
  instantiate' t = return t

instance Instantiate Level where
  instantiate' (Max as) = levelMax <$> instantiate' as

instance Instantiate PlusLevel where
  instantiate' l@ClosedLevel{} = return l
  instantiate' (Plus n a) = Plus n <$> instantiate' a

instance Instantiate LevelAtom where
  instantiate' l = case l of
    MetaLevel m vs -> do
      v <- instantiate' (MetaV m vs)
      case ignoreSharing v of
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
      OpenIFS                        -> return v
      BlockedConst{}                 -> return v
      PostponedTypeCheckingProblem{} -> return v

instance Instantiate Type where
    instantiate' (El s t) = El <$> instantiate' s <*> instantiate' t

instance Instantiate Sort where
  instantiate' s = case s of
    Type l -> levelSort <$> instantiate' l
    _      -> return s

instance Instantiate Elim where
  instantiate' (Apply v) = Apply <$> instantiate' v
  instantiate' (Proj o f)= pure $ Proj o f

instance Instantiate t => Instantiate (Abs t) where
  instantiate' = traverse instantiate'

instance Instantiate t => Instantiate (Arg t) where
    instantiate' = traverse instantiate'

instance Instantiate t => Instantiate (Dom t) where
    instantiate' = traverse instantiate'

instance Instantiate t => Instantiate [t] where
    instantiate' = traverse instantiate'

instance (Instantiate a, Instantiate b) => Instantiate (a,b) where
    instantiate' (x,y) = (,) <$> instantiate' x <*> instantiate' y


instance (Instantiate a, Instantiate b,Instantiate c) => Instantiate (a,b,c) where
    instantiate' (x,y,z) = (,,) <$> instantiate' x <*> instantiate' y <*> instantiate' z

instance Instantiate a => Instantiate (Closure a) where
    instantiate' cl = do
        x <- enterClosure cl instantiate'
        return $ cl { clValue = x }

instance Instantiate Telescope where
  instantiate' EmptyTel = return EmptyTel
  instantiate' (ExtendTel a tel) = ExtendTel <$> instantiate' a <*> instantiate' tel
--instantiate' tel = return tel

instance Instantiate Constraint where
  instantiate' (ValueCmp cmp t u v) = do
    (t,u,v) <- instantiate' (t,u,v)
    return $ ValueCmp cmp t u v
  instantiate' (ElimCmp cmp t v as bs) =
    ElimCmp cmp <$> instantiate' t <*> instantiate' v <*> instantiate' as <*> instantiate' bs
  instantiate' (LevelCmp cmp u v)   = uncurry (LevelCmp cmp) <$> instantiate' (u,v)
  instantiate' (TypeCmp cmp a b)    = uncurry (TypeCmp cmp) <$> instantiate' (a,b)
  instantiate' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp)  <$> instantiate' (tela,telb)
  instantiate' (SortCmp cmp a b)    = uncurry (SortCmp cmp) <$> instantiate' (a,b)
  instantiate' (Guarded c pid)      = Guarded <$> instantiate' c <*> pure pid
  instantiate' (UnBlock m)          = return $ UnBlock m
  instantiate' (FindInScope m b args) = FindInScope m b <$> mapM instantiate' args
  instantiate' (IsEmpty r t)        = IsEmpty r <$> instantiate' t
  instantiate' (CheckSizeLtSat t)   = CheckSizeLtSat <$> instantiate' t

instance Instantiate e => Instantiate (Map k e) where
    instantiate' = traverse instantiate'

instance Instantiate Candidate where
  instantiate' (Candidate u t eti ov) = Candidate <$> instantiate' u <*> instantiate' t <*> pure eti <*> pure ov

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

-- | Case on whether a term is blocked on a meta (or is a meta).
--   That means it can change its shape when the meta is instantiated.
ifBlocked :: MonadTCM tcm =>  Term -> (MetaId -> Term -> tcm a) -> (Term -> tcm a) -> tcm a
ifBlocked t blocked unblocked = do
  t <- liftTCM $ reduceB t
  case ignoreSharing <$> t of
    Blocked m _              -> blocked m (ignoreBlocking t)
    NotBlocked _ (MetaV m _) -> blocked m (ignoreBlocking t)
    NotBlocked{}             -> unblocked (ignoreBlocking t)

-- | Case on whether a type is blocked on a meta (or is a meta).
ifBlockedType :: MonadTCM tcm => Type -> (MetaId -> Type -> tcm a) -> (Type -> tcm a) -> tcm a
ifBlockedType (El s t) blocked unblocked =
  ifBlocked t (\ m v -> blocked m $ El s v) (\ v -> unblocked $ El s v)

class Reduce t where
    reduce'  :: t -> ReduceM t
    reduceB' :: t -> ReduceM (Blocked t)

    reduce'  t = ignoreBlocking <$> reduceB' t
    reduceB' t = notBlocked <$> reduce' t

instance Reduce Type where
    reduce'  (El s t) = El s <$> reduce' t
    reduceB' (El s t) = fmap (El s) <$> reduceB' t

instance Reduce Sort where
    reduce' s = {-# SCC "reduce'<Sort>" #-}
      ifNotM hasUniversePolymorphism (red s) $ {- else -} red =<< instantiateFull' s
      where
        red s = do
          s <- instantiate' s
          case s of
            DLub s1 s2 -> do
              s <- dLub <$> reduce' s1 <*> reduce' s2
              case s of
                DLub{}  -> return s
                _       -> reduce' s   -- TODO: not so nice
            Prop       -> return s
            Type s'    -> levelSort <$> reduce' s'
            Inf        -> return Inf
            SizeUniv   -> return SizeUniv

instance Reduce Elim where
  reduce' (Apply v) = Apply <$> reduce' v
  reduce' (Proj o f)= pure $ Proj o f

instance Reduce Level where
  reduce'  (Max as) = levelMax <$> mapM reduce' as
  reduceB' (Max as) = fmap levelMax . traverse id <$> traverse reduceB' as

instance Reduce PlusLevel where
  reduceB' l@ClosedLevel{} = return $ notBlocked l
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
        case ignoreSharing <$> bv of
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
                 _          -> traverse reduce' a

    reduceB' t = traverse id <$> traverse reduceB' t

instance Reduce t => Reduce (Dom t) where
    reduce' = traverse reduce'
    reduceB' t = traverse id <$> traverse reduceB' t

-- Tuples are never blocked
instance (Reduce a, Reduce b) => Reduce (a,b) where
    reduce' (x,y)  = (,) <$> reduce' x <*> reduce' y

instance (Reduce a, Reduce b,Reduce c) => Reduce (a,b,c) where
    reduce' (x,y,z) = (,,) <$> reduce' x <*> reduce' y <*> reduce' z

instance Reduce Term where
  reduceB' = {-# SCC "reduce'<Term>" #-} maybeFastReduceTerm

maybeFastReduceTerm :: Term -> ReduceM (Blocked Term)
maybeFastReduceTerm v = do
  let tryFast = case v of
                  Def{} -> True
                  Con{} -> True
                  _     -> False
  if not tryFast then slowReduceTerm v
                 else do
    s <- optSharing   <$> commandLineOptions
    allowed <- asks envAllowedReductions
    let notAll = delete NonTerminatingReductions allowed /= allReductions
    if s || notAll then slowReduceTerm v else fastReduce (elem NonTerminatingReductions allowed) v

slowReduceTerm :: Term -> ReduceM (Blocked Term)
slowReduceTerm v = do
    v <- instantiate' v
    let done = return $ notBlocked v
    case v of
--    Andreas, 2012-11-05 not reducing meta args does not destroy anything
--    and seems to save 2% sec on the standard library
--      MetaV x args -> notBlocked . MetaV x <$> reduce' args
      MetaV x es -> done
      Def f es   -> unfoldDefinitionE False reduceB' (Def f []) f es
      Con c ci args -> do
          -- Constructors can reduce' when they come from an
          -- instantiated module.
          v <- unfoldDefinition False reduceB' (Con c ci []) (conName c) args
          traverse reduceNat v
      Sort s   -> fmap sortTm <$> reduceB' s
      Level l  -> ifM (elem LevelReductions <$> asks envAllowedReductions)
                    {- then -} (fmap levelTm <$> reduceB' l)
                    {- else -} done
      Pi _ _   -> done
      Lit _    -> done
      Var _ _  -> done
      Lam _ _  -> done
      DontCare _ -> done
      Shared{}   -> updateSharedTermF reduceB' v
    where
      -- NOTE: reduceNat can traverse the entire term.
      reduceNat v@Shared{} = updateSharedTerm reduceNat v
      reduceNat v@(Con c ci []) = do
        mz  <- getBuiltin' builtinZero
        case v of
          _ | Just v == mz  -> return $ Lit $ LitNat (getRange c) 0
          _                 -> return v
      reduceNat v@(Con c ci [a]) | notHidden a && isRelevant a = do
        ms  <- fmap ignoreSharing <$> getBuiltin' builtinSuc
        case v of
          _ | Just (Con c ci []) == ms -> inc <$> reduce' (unArg a)
          _                         -> return v
          where
            inc w = case ignoreSharing w of
              Lit (LitNat r n) -> Lit (LitNat (fuseRange c r) $ n + 1)
              _                -> Con c ci [defaultArg w]
      reduceNat v = return v

-- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
-- need also to instantiate metas, see Issue 826.
unfoldCorecursionE :: Elim -> ReduceM (Blocked Elim)
unfoldCorecursionE (Proj o p)           = notBlocked . Proj o <$> getOriginalProjection p
unfoldCorecursionE (Apply (Arg info v)) = fmap (Apply . Arg info) <$>
  unfoldCorecursion v

unfoldCorecursion :: Term -> ReduceM (Blocked Term)
unfoldCorecursion v = do
  v <- instantiate' v
  case compressPointerChain v of
    Def f es -> unfoldDefinitionE True unfoldCorecursion (Def f []) f es
    v@(Shared p) ->
      case derefPtr p of
        Def{} -> updateSharedFM unfoldCorecursion v
        _     -> slowReduceTerm v
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
  info <- getConstInfo f
  rewr <- getRewriteRulesFor f
  allowed <- asks envAllowedReductions
  let def = theDef info
      v   = v0 `applyE` es
      -- Non-terminating functions
      -- (i.e., those that failed the termination check)
      -- and delayed definitions
      -- are not unfolded unless explicitely permitted.
      dontUnfold =
        (defNonterminating info && notElem NonTerminatingReductions allowed)
        || (defTerminationUnconfirmed info && notElem UnconfirmedReductions allowed)
        || (defDelayed info == Delayed && not unfoldDelayed)
      copatterns =
        case def of
          Function{funCopatternLHS = b} -> b
          _                             -> False
  case def of
    Constructor{conSrcCon = c} ->
      noReduction $ notBlocked $ Con (c `withRangeOf` f) ConOSystem [] `applyE` es
    Primitive{primAbstr = ConcreteDef, primName = x, primClauses = cls} -> do
      pf <- fromMaybe __IMPOSSIBLE__ <$> getPrimitive' x
      if FunctionReductions `elem` allowed
        then reducePrimitive x v0 f es pf dontUnfold
                             cls (defCompiled info) rewr
        else noReduction $ notBlocked v
    _  -> do
      if FunctionReductions `elem` allowed ||
         (isJust (isProjection_ def) && ProjectionReductions `elem` allowed) || -- includes projection-like
         (isInlineFun def && InlineReductions `elem` allowed) ||
         (copatterns && CopatternReductions `elem` allowed)
        then
          reduceNormalE v0 f (map notReduced es) dontUnfold
                       (defClauses info) (defCompiled info) rewr
        else noReduction $ notBlocked v  -- Andrea(s), 2014-12-05 OK?

  where
    noReduction    = return . NoReduction
    yesReduction s = return . YesReduction s
    reducePrimitive x v0 f es pf dontUnfold cls mcc rewr
      | genericLength es < ar
                  = noReduction $ NotBlocked Underapplied $ v0 `applyE` es -- not fully applied
      | otherwise = {-# SCC "reducePrimitive" #-} do
          let (es1,es2) = genericSplitAt ar es
              args1     = fromMaybe __IMPOSSIBLE__ $ mapM isApplyElim es1
          r <- primFunImplementation pf args1
          case r of
            NoReduction args1' -> do
              let es1' = map (fmap Apply) args1'
              if null cls then do
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
      case (def,rewr) of
        _ | dontUnfold -> defaultResult -- non-terminating or delayed
        ([],[])        -> defaultResult -- no definition for head
        (cls,rewr)     -> appDefE_ f v0 cls mcc rewr es
      where defaultResult = noReduction $ NotBlocked AbsurdMatch vfull
            vfull         = v0 `applyE` map ignoreReduced es

-- | Reduce a non-primitive definition if it is a copy linking to another def.
reduceDefCopy :: QName -> Elims -> TCM (Reduced () Term)
reduceDefCopy f es = do
  info <- TCM.getConstInfo f
  rewr <- TCM.getRewriteRulesFor f
  if (defCopy info) then reduceDef_ info rewr f es else return $ NoReduction ()
  where
    reduceDef_ :: Definition -> RewriteRules -> QName -> Elims -> TCM (Reduced () Term)
    reduceDef_ info rewr f es = do
      let v0   = Def f []
          cls  = (defClauses info)
          mcc  = (defCompiled info)
      if (defDelayed info == Delayed) || (defNonterminating info)
       then return $ NoReduction ()
       else do
          ev <- runReduceM $ appDefE_ f v0 cls mcc rewr $ map notReduced es
          case ev of
            YesReduction simpl t -> return $ YesReduction simpl t
            NoReduction{}        -> return $ NoReduction ()

-- | Reduce simple (single clause) definitions.
reduceHead :: Term -> TCM (Blocked Term)
reduceHead = runReduceM . reduceHead'

reduceHead' :: Term -> ReduceM (Blocked Term)
reduceHead' v = do -- ignoreAbstractMode $ do
  -- Andreas, 2013-02-18 ignoreAbstractMode leads to information leakage
  -- see Issue 796

  -- first, possibly rewrite literal v to constructor form
  v <- constructorForm v
  traceSDoc "tc.inj.reduce" 30 (text "reduceHead" <+> prettyTCM v) $ do
  case ignoreSharing v of
    Def f es -> do

      abstractMode <- envAbstractMode <$> ask
      isAbstract <- treatAbstractly f
      traceSLn "tc.inj.reduce" 50 (
        "reduceHead: we are in " ++ show abstractMode++ "; " ++ show f ++
        " is treated " ++ if isAbstract then "abstractly" else "concretely"
        ) $ do
      let v0  = Def f []
          red = unfoldDefinitionE False reduceHead' v0 f es
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

-- | Apply a definition using the compiled clauses, or fall back to
--   ordinary clauses if no compiled clauses exist.
appDef_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef_ f v0 cls mcc rewr args = appDefE_ f v0 cls mcc rewr $ map (fmap Apply) args

appDefE_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE_ f v0 cls mcc rewr args =
  local (\ e -> e { envAppDef = Just f }) $
  maybe (appDefE' v0 cls rewr args)
        (\cc -> appDefE v0 cc rewr args) mcc


-- | Apply a defined function to it's arguments, using the compiled clauses.
--   The original term is the first argument applied to the third.
appDef :: Term -> CompiledClauses -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef v cc rewr args = appDefE v cc rewr $ map (fmap Apply) args

appDefE :: Term -> CompiledClauses -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE v cc rewr es = do
  r <- matchCompiledE cc es
  case r of
    YesReduction simpl t -> return $ YesReduction simpl t
    NoReduction es'      -> rewrite (void es') v rewr (ignoreBlocking es')

-- | Apply a defined function to it's arguments, using the original clauses.
appDef' :: Term -> [Clause] -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef' v cls rewr args = appDefE' v cls rewr $ map (fmap Apply) args

appDefE' :: Term -> [Clause] -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE' v cls rewr es = goCls cls $ map ignoreReduced es
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
            es <- return $ es0 ++ es1
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
  reduce' (ElimCmp cmp t v as bs) =
    ElimCmp cmp <$> reduce' t <*> reduce' v <*> reduce' as <*> reduce' bs
  reduce' (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> reduce' (u,v)
  reduce' (TypeCmp cmp a b)     = uncurry (TypeCmp cmp) <$> reduce' (a,b)
  reduce' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp)  <$> reduce' (tela,telb)
  reduce' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> reduce' (a,b)
  reduce' (Guarded c pid)       = Guarded <$> reduce' c <*> pure pid
  reduce' (UnBlock m)           = return $ UnBlock m
  reduce' (FindInScope m b cands) = FindInScope m b <$> mapM reduce' cands
  reduce' (IsEmpty r t)         = IsEmpty r <$> reduce' t
  reduce' (CheckSizeLtSat t)    = CheckSizeLtSat <$> reduce' t

instance Reduce e => Reduce (Map k e) where
    reduce' = traverse reduce'

instance Reduce Candidate where
  reduce' (Candidate u t eti ov) = Candidate <$> reduce' u <*> reduce' t <*> pure eti <*> pure ov

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

---------------------------------------------------------------------------
-- * Simplification
---------------------------------------------------------------------------

-- | Only unfold definitions if this leads to simplification
--   which means that a constructor/literal pattern is matched.
class Simplify t where
  simplify' :: t -> ReduceM t

instance Simplify Term where
  simplify' v = do
    v <- instantiate' v
    case v of
      Def f vs   -> do
        let keepGoing simp v = return (simp, notBlocked v)
        (simpl, v) <- unfoldDefinition' False keepGoing (Def f []) f vs
        traceSDoc "tc.simplify'" 20 (
          text ("simplify': unfolding definition returns " ++ show simpl)
            <+> prettyTCM (ignoreBlocking v)) $ do
        case simpl of
          YesSimplification -> simplifyBlocked' v -- Dangerous, but if @simpl@ then @v /= Def f vs@
          NoSimplification  -> Def f <$> simplify' vs
      MetaV x vs -> MetaV x  <$> simplify' vs
      Con c ci vs-> Con c ci <$> simplify' vs
      Sort s     -> sortTm   <$> simplify' s
      Level l    -> levelTm  <$> simplify' l
      Pi a b     -> Pi       <$> simplify' a <*> simplify' b
      Lit l      -> return v
      Var i vs   -> Var i    <$> simplify' vs
      Lam h v    -> Lam h    <$> simplify' v
      DontCare v -> dontCare <$> simplify' v
      Shared{}   -> updateSharedTerm simplify' v

simplifyBlocked' :: Simplify t => Blocked t -> ReduceM t
simplifyBlocked' (Blocked _ t) = return t
simplifyBlocked' (NotBlocked _ t) = simplify' t  -- Andrea(s), 2014-12-05 OK?

instance Simplify Type where
    simplify' (El s t) = El <$> simplify' s <*> simplify' t

instance Simplify Elim where
  simplify' (Apply v) = Apply <$> simplify' v
  simplify' (Proj o f)= pure $ Proj o f

instance Simplify Sort where
    simplify' s = do
      case s of
        DLub s1 s2 -> dLub <$> simplify' s1 <*> simplify' s2
        Type s     -> levelSort <$> simplify' s
        Prop       -> return s
        Inf        -> return s
        SizeUniv   -> return s

instance Simplify Level where
  simplify' (Max as) = levelMax <$> simplify' as

instance Simplify PlusLevel where
  simplify' l@ClosedLevel{} = return l
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

instance Simplify t => Simplify (Arg t) where
    simplify' = traverse simplify'

instance Simplify t => Simplify (Named name t) where
    simplify' = traverse simplify'

instance Simplify t => Simplify (Dom t) where
    simplify' = traverse simplify'

instance Simplify t => Simplify [t] where
    simplify' = traverse simplify'

instance Simplify e => Simplify (Map k e) where
    simplify' = traverse simplify'

instance Simplify a => Simplify (Maybe a) where
    simplify' = traverse simplify'

instance (Simplify a, Simplify b) => Simplify (a,b) where
    simplify' (x,y) = (,) <$> simplify' x <*> simplify' y

instance (Simplify a, Simplify b, Simplify c) => Simplify (a,b,c) where
    simplify' (x,y,z) =
        do  (x,(y,z)) <- simplify' (x,(y,z))
            return (x,y,z)

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
  simplify' (ElimCmp cmp t v as bs) =
    ElimCmp cmp <$> simplify' t <*> simplify' v <*> simplify' as <*> simplify' bs
  simplify' (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> simplify' (u,v)
  simplify' (TypeCmp cmp a b)     = uncurry (TypeCmp cmp) <$> simplify' (a,b)
  simplify' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp) <$> simplify' (tela,telb)
  simplify' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> simplify' (a,b)
  simplify' (Guarded c pid)       = Guarded <$> simplify' c <*> pure pid
  simplify' (UnBlock m)           = return $ UnBlock m
  simplify' (FindInScope m b cands) = FindInScope m b <$> mapM simplify' cands
  simplify' (IsEmpty r t)         = IsEmpty r <$> simplify' t
  simplify' (CheckSizeLtSat t)    = CheckSizeLtSat <$> simplify' t

instance Simplify Bool where
  simplify' = return

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
  simplify' (Candidate u t eti ov) = Candidate <$> simplify' u <*> simplify' t <*> pure eti <*> pure ov

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

instance Normalise Sort where
    normalise' s = do
      s <- reduce' s
      case s of
        DLub s1 s2 -> dLub <$> normalise' s1 <*> normalise' s2
        Prop       -> return s
        Type s     -> levelSort <$> normalise' s
        Inf        -> return Inf
        SizeUniv   -> return SizeUniv

instance Normalise Type where
    normalise' (El s t) = El <$> normalise' s <*> normalise' t

instance Normalise Term where
    normalise' = ignoreBlocking <.> (reduceB' >=> traverse normaliseArgs)
      where
        normaliseArgs :: Term -> ReduceM Term
        normaliseArgs v = case v of
                Var n vs    -> Var n <$> normalise' vs
                Con c ci vs -> Con c ci <$> normalise' vs
                Def f vs    -> Def f <$> normalise' vs
                MetaV x vs  -> MetaV x <$> normalise' vs
                Lit _       -> return v
                Level l     -> levelTm <$> normalise' l
                Lam h b     -> Lam h <$> normalise' b
                Sort s      -> sortTm <$> normalise' s
                Pi a b      -> uncurry Pi <$> normalise' (a,b)
                Shared{}    -> updateSharedTerm normalise' v
                DontCare _  -> return v

instance Normalise Elim where
  normalise' (Apply v) = Apply <$> normalise' v
  normalise' (Proj o f)= pure $ Proj o f

instance Normalise Level where
  normalise' (Max as) = levelMax <$> normalise' as

instance Normalise PlusLevel where
  normalise' l@ClosedLevel{} = return l
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
    normalise' a | isIrrelevant a = return a -- Andreas, 2012-04-02: Do not normalize irrelevant terms!?
                | otherwise                       = traverse normalise' a

instance Normalise t => Normalise (Named name t) where
    normalise' = traverse normalise'

instance Normalise t => Normalise (Dom t) where
    normalise' = traverse normalise'

instance Normalise t => Normalise [t] where
    normalise' = traverse normalise'

instance (Normalise a, Normalise b) => Normalise (a,b) where
    normalise' (x,y) = (,) <$> normalise' x <*> normalise' y

instance (Normalise a, Normalise b, Normalise c) => Normalise (a,b,c) where
    normalise' (x,y,z) =
        do  (x,(y,z)) <- normalise' (x,(y,z))
            return (x,y,z)

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
  normalise' (ElimCmp cmp t v as bs) =
    ElimCmp cmp <$> normalise' t <*> normalise' v <*> normalise' as <*> normalise' bs
  normalise' (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> normalise' (u,v)
  normalise' (TypeCmp cmp a b)     = uncurry (TypeCmp cmp) <$> normalise' (a,b)
  normalise' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp) <$> normalise' (tela,telb)
  normalise' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> normalise' (a,b)
  normalise' (Guarded c pid)       = Guarded <$> normalise' c <*> pure pid
  normalise' (UnBlock m)           = return $ UnBlock m
  normalise' (FindInScope m b cands) = FindInScope m b <$> mapM normalise' cands
  normalise' (IsEmpty r t)         = IsEmpty r <$> normalise' t
  normalise' (CheckSizeLtSat t)    = CheckSizeLtSat <$> normalise' t

instance Normalise Bool where
  normalise' = return

instance Normalise Int where
  normalise' = return

instance Normalise Char where
  normalise' = return

instance Normalise ConPatternInfo where
  normalise' (ConPatternInfo mr mt) = ConPatternInfo mr <$> normalise' mt

instance Normalise DBPatVar where
  normalise' = return

instance Normalise a => Normalise (Pattern' a) where
  normalise' p = case p of
    VarP x       -> VarP <$> normalise' x
    LitP _       -> return p
    ConP c mt ps -> ConP c <$> normalise' mt <*> normalise' ps
    DotP v       -> DotP <$> normalise' v
    ProjP{}      -> return p

instance Normalise DisplayForm where
  normalise' (Display n ps v) = Display n <$> normalise' ps <*> return v

instance Normalise e => Normalise (Map k e) where
    normalise' = traverse normalise'

instance Normalise a => Normalise (Maybe a) where
    normalise' = traverse normalise'

instance Normalise Candidate where
  normalise' (Candidate u t eti ov) = Candidate <$> normalise' u <*> normalise' t <*> pure eti <*> pure ov

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

-- STALE: Full instantiatiation = normalisation [ instantiate' / reduce' ]
-- How can we express this? We need higher order classes!

-- | @instantiateFull'@ 'instantiate's metas everywhere (and recursively)
--   but does not 'reduce'.
class InstantiateFull t where
    instantiateFull' :: t -> ReduceM t

instance InstantiateFull Name where
    instantiateFull' = return

instance InstantiateFull Sort where
    instantiateFull' s = do
        s <- instantiate' s
        case s of
            Type n     -> levelSort <$> instantiateFull' n
            Prop       -> return s
            DLub s1 s2 -> dLub <$> instantiateFull' s1 <*> instantiateFull' s2
            Inf        -> return s
            SizeUniv   -> return s

instance (InstantiateFull a) => InstantiateFull (Type' a) where
    instantiateFull' (El s t) =
      El <$> instantiateFull' s <*> instantiateFull' t

instance InstantiateFull Term where
    instantiateFull' v = etaOnce =<< do -- Andreas, 2010-11-12 DONT ETA!! eta-reduction breaks subject reduction
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
          Sort s      -> sortTm <$> instantiateFull' s
          Pi a b      -> uncurry Pi <$> instantiateFull' (a,b)
          Shared{}    -> updateSharedTerm instantiateFull' v
          DontCare v  -> dontCare <$> instantiateFull' v

instance InstantiateFull Level where
  instantiateFull' (Max as) = levelMax <$> instantiateFull' as

instance InstantiateFull PlusLevel where
  instantiateFull' l@ClosedLevel{} = return l
  instantiateFull' (Plus n l) = Plus n <$> instantiateFull' l

instance InstantiateFull LevelAtom where
  instantiateFull' l = case l of
    MetaLevel m vs -> do
      v <- instantiateFull' (MetaV m vs)
      case ignoreSharing v of
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
      EmptyS               -> return EmptyS
      Wk   n sigma         -> Wk   n         <$> instantiateFull' sigma
      Lift n sigma         -> Lift n         <$> instantiateFull' sigma
      Strengthen bot sigma -> Strengthen bot <$> instantiateFull' sigma
      t :# sigma           -> consS <$> instantiateFull' t
                                    <*> instantiateFull' sigma

instance InstantiateFull Bool where
    instantiateFull' = return

instance InstantiateFull Int where
    instantiateFull' = return

instance InstantiateFull ConPatternInfo where
  instantiateFull' (ConPatternInfo mr mt) = ConPatternInfo mr <$> instantiateFull' mt

instance InstantiateFull DBPatVar where
    instantiateFull' = return

instance InstantiateFull a => InstantiateFull (Pattern' a) where
    instantiateFull' (VarP x)       = VarP <$> instantiateFull' x
    instantiateFull' (DotP t)       = DotP <$> instantiateFull' t
    instantiateFull' (ConP n mt ps) = ConP n <$> instantiateFull' mt <*> instantiateFull' ps
    instantiateFull' l@LitP{}       = return l
    instantiateFull' p@ProjP{}      = return p

instance (Subst t a, InstantiateFull a) => InstantiateFull (Abs a) where
    instantiateFull' a@(Abs x _) = Abs x <$> underAbstraction_ a instantiateFull'
    instantiateFull' (NoAbs x a) = NoAbs x <$> instantiateFull' a

instance InstantiateFull t => InstantiateFull (Arg t) where
    instantiateFull' = traverse instantiateFull'

instance InstantiateFull t => InstantiateFull (Named name t) where
    instantiateFull' = traverse instantiateFull'

instance InstantiateFull t => InstantiateFull (Dom t) where
    instantiateFull' = traverse instantiateFull'

instance InstantiateFull t => InstantiateFull [t] where
    instantiateFull' = traverse instantiateFull'

instance (InstantiateFull a, InstantiateFull b) => InstantiateFull (a,b) where
    instantiateFull' (x,y) = (,) <$> instantiateFull' x <*> instantiateFull' y

instance (InstantiateFull a, InstantiateFull b, InstantiateFull c) => InstantiateFull (a,b,c) where
    instantiateFull' (x,y,z) =
        do  (x,(y,z)) <- instantiateFull' (x,(y,z))
            return (x,y,z)

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
    ElimCmp cmp t v as bs ->
      ElimCmp cmp <$> instantiateFull' t <*> instantiateFull' v <*> instantiateFull' as <*> instantiateFull' bs
    LevelCmp cmp u v    -> uncurry (LevelCmp cmp) <$> instantiateFull' (u,v)
    TypeCmp cmp a b     -> uncurry (TypeCmp cmp) <$> instantiateFull' (a,b)
    TelCmp a b cmp tela telb -> uncurry (TelCmp a b cmp) <$> instantiateFull' (tela,telb)
    SortCmp cmp a b     -> uncurry (SortCmp cmp) <$> instantiateFull' (a,b)
    Guarded c pid       -> Guarded <$> instantiateFull' c <*> pure pid
    UnBlock m           -> return $ UnBlock m
    FindInScope m b cands -> FindInScope m b <$> mapM instantiateFull' cands
    IsEmpty r t         -> IsEmpty r <$> instantiateFull' t
    CheckSizeLtSat t    -> CheckSizeLtSat <$> instantiateFull' t

instance (InstantiateFull a) => InstantiateFull (Elim' a) where
  instantiateFull' (Apply v) = Apply <$> instantiateFull' v
  instantiateFull' (Proj o f)= pure $ Proj o f

instance InstantiateFull e => InstantiateFull (Map k e) where
    instantiateFull' = traverse instantiateFull'

instance InstantiateFull e => InstantiateFull (HashMap k e) where
    instantiateFull' = traverse instantiateFull'

instance InstantiateFull ModuleName where
    instantiateFull' = return

instance InstantiateFull Scope where
    instantiateFull' = return

instance InstantiateFull Signature where
  instantiateFull' (Sig a b c) = uncurry3 Sig <$> instantiateFull' (a, b, c)

instance InstantiateFull Section where
  instantiateFull' (Section tel) = Section <$> instantiateFull' tel

instance (Subst t a, InstantiateFull a) => InstantiateFull (Tele a) where
  instantiateFull' EmptyTel = return EmptyTel
  instantiateFull' (ExtendTel a b) = uncurry ExtendTel <$> instantiateFull' (a, b)

instance InstantiateFull Char where
    instantiateFull' = return

instance InstantiateFull Definition where
    instantiateFull' (Defn rel x t pol occ df i c inst copy ma inj d) = do
      (t, df, d) <- instantiateFull' (t, df, d)
      return $ Defn rel x t pol occ df i c inst copy ma inj d

instance InstantiateFull NLPat where
  instantiateFull' (PVar x y z) = return $ PVar x y z
  instantiateFull' (PWild)    = return PWild
  instantiateFull' (PDef x y) = PDef <$> instantiateFull' x <*> instantiateFull' y
  instantiateFull' (PLam x y) = PLam x <$> instantiateFull' y
  instantiateFull' (PPi x y)  = PPi <$> instantiateFull' x <*> instantiateFull' y
  instantiateFull' (PBoundVar x y) = PBoundVar x <$> instantiateFull' y
  instantiateFull' (PTerm x)  = PTerm <$> instantiateFull' x

instance InstantiateFull NLPType where
  instantiateFull' (NLPType l a) = NLPType
    <$> instantiateFull' l
    <*> instantiateFull' a

instance InstantiateFull RewriteRule where
  instantiateFull' (RewriteRule q gamma f ps rhs t) =
    RewriteRule q
      <$> instantiateFull' gamma
      <*> pure f
      <*> instantiateFull' ps
      <*> instantiateFull' rhs
      <*> instantiateFull' t

instance InstantiateFull a => InstantiateFull (Open a) where
  instantiateFull' (OpenThing n a) = OpenThing n <$> instantiateFull' a

instance InstantiateFull a => InstantiateFull (Local a) where
  instantiateFull' = traverseF instantiateFull'

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
      AbstractDefn -> return d
      Function{ funClauses = cs, funCompiled = cc, funInv = inv } -> do
        (cs, cc, inv) <- instantiateFull' (cs, cc, inv)
        return $ d { funClauses = cs, funCompiled = cc, funInv = inv }
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

instance InstantiateFull FunctionInverse where
  instantiateFull' NotInjective = return NotInjective
  instantiateFull' (Inverse inv) = Inverse <$> instantiateFull' inv

instance InstantiateFull a => InstantiateFull (WithArity a) where
  instantiateFull' (WithArity n a) = WithArity n <$> instantiateFull' a

instance InstantiateFull a => InstantiateFull (Case a) where
  instantiateFull' (Branches cop cs ls m) =
    Branches cop
      <$> instantiateFull' cs
      <*> instantiateFull' ls
      <*> instantiateFull' m

instance InstantiateFull CompiledClauses where
  instantiateFull' Fail        = return Fail
  instantiateFull' (Done m t)  = Done m <$> instantiateFull' t
  instantiateFull' (Case n bs) = Case n <$> instantiateFull' bs

instance InstantiateFull Clause where
    instantiateFull' (Clause rl rf tel ps b t catchall) =
       Clause rl rf <$> instantiateFull' tel
       <*> instantiateFull' ps
       <*> instantiateFull' b
       <*> instantiateFull' t
       <*> return catchall

instance InstantiateFull Interface where
    instantiateFull' (Interface h ms mod scope inside
                               sig display b hsImports hsImportsUHC hsCode highlighting pragmas patsyns) =
        Interface h ms mod scope inside
            <$> instantiateFull' sig
            <*> instantiateFull' display
            <*> instantiateFull' b
            <*> return hsImports
            <*> return hsImportsUHC
            <*> return hsCode
            <*> return highlighting
            <*> return pragmas
            <*> return patsyns

instance InstantiateFull a => InstantiateFull (Builtin a) where
    instantiateFull' (Builtin t) = Builtin <$> instantiateFull' t
    instantiateFull' (Prim x)   = Prim <$> instantiateFull' x

instance InstantiateFull QName where
  instantiateFull' = return

instance InstantiateFull a => InstantiateFull (Maybe a) where
  instantiateFull' = mapM instantiateFull'

instance InstantiateFull Candidate where
  instantiateFull' (Candidate u t eti ov) =
    Candidate <$> instantiateFull' u <*> instantiateFull' t <*> pure eti <*> pure ov

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
