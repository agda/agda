{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE FlexibleContexts #-}
#endif

module Agda.TypeChecking.Reduce where

import Prelude hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Applicative

import Data.List as List hiding (sort)
import Data.Maybe
import Data.Map (Map)
import Data.Traversable
import Data.Hashable

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

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Monad
import Agda.Utils.HashMap (HashMap)
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
      InstS _                          -> __IMPOSSIBLE__
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
      InstS{}                        -> __IMPOSSIBLE__

instance Instantiate Type where
    instantiate' (El s t) = El <$> instantiate' s <*> instantiate' t

instance Instantiate Sort where
  instantiate' s = case s of
    Type l -> levelSort <$> instantiate' l
    _      -> return s

instance Instantiate Elim where
  instantiate' (Apply v) = Apply <$> instantiate' v
  instantiate' (Proj f)  = pure $ Proj f

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

instance (Ord k, Instantiate e) => Instantiate (Map k e) where
    instantiate' = traverse instantiate'

instance Instantiate Candidate where
  instantiate' (Candidate u t eti) = Candidate <$> instantiate' u <*> instantiate' t <*> return eti

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
  reduce' (Proj f)  = pure $ Proj f

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
  reduceB' = {-# SCC "reduce'<Term>" #-} rewriteAfter $ \ v -> do
    v <- instantiate' v
    let done = return $ notBlocked v
    case v of
--    Andreas, 2012-11-05 not reducing meta args does not destroy anything
--    and seems to save 2% sec on the standard library
--      MetaV x args -> notBlocked . MetaV x <$> reduce' args
      MetaV x es -> done
      Def f es   -> unfoldDefinitionE False reduceB' (Def f []) f es
      Con c args -> do
          -- Constructors can reduce' when they come from an
          -- instantiated module.
          v <- unfoldDefinition False reduceB' (Con c []) (conName c) args
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
      reduceNat v@(Con c []) = do
        mz  <- getBuiltin' builtinZero
        case v of
          _ | Just v == mz  -> return $ Lit $ LitNat (getRange c) 0
          _                 -> return v
      reduceNat v@(Con c [a]) | notHidden a && isRelevant a = do
        ms  <- fmap ignoreSharing <$> getBuiltin' builtinSuc
        case v of
          _ | Just (Con c []) == ms -> inc <$> reduce' (unArg a)
          _                         -> return v
          where
            inc w = case ignoreSharing w of
              Lit (LitNat r n) -> Lit (LitNat (fuseRange c r) $ n + 1)
              _                -> Con c [defaultArg w]
      reduceNat v = return v

rewriteAfter :: (Term -> ReduceM (Blocked Term)) -> Term -> ReduceM (Blocked Term)
rewriteAfter f = trampolineM $ rewrite <=< f

-- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
-- need also to instantiate metas, see Issue 826.
unfoldCorecursionE :: Elim -> ReduceM (Blocked Elim)
unfoldCorecursionE e@(Proj f)           = return $ notBlocked e
unfoldCorecursionE (Apply (Arg info v)) = fmap (Apply . Arg info) <$>
  unfoldCorecursion v

unfoldCorecursion :: Term -> ReduceM (Blocked Term)
unfoldCorecursion = rewriteAfter $ \ v -> do
  v <- instantiate' v
  case compressPointerChain v of
    Def f es -> unfoldDefinitionE True unfoldCorecursion (Def f []) f es
    v@(Shared p) ->
      case derefPtr p of
        Def{} -> updateSharedFM unfoldCorecursion v
        _     -> reduceB' v
    _ -> reduceB' v

-- | If the first argument is 'True', then a single delayed clause may
-- be unfolded.
unfoldDefinition ::
  Bool -> (Term -> ReduceM (Blocked Term)) ->
  Term -> QName -> Args -> ReduceM (Blocked Term)
unfoldDefinition b keepGoing v f args = snd <$> do
  unfoldDefinition' b (\ t -> (NoSimplification,) <$> keepGoing t) v f $
    map Apply args

unfoldDefinitionE ::
  Bool -> (Term -> ReduceM (Blocked Term)) ->
  Term -> QName -> Elims -> ReduceM (Blocked Term)
unfoldDefinitionE b keepGoing v f es = snd <$>
  unfoldDefinition' b (\ t -> (NoSimplification,) <$> keepGoing t) v f es

unfoldDefinition' ::
  Bool -> (Term -> ReduceM (Simplification, Blocked Term)) ->
  Term -> QName -> Elims -> ReduceM (Simplification, Blocked Term)
unfoldDefinition' unfoldDelayed keepGoing v0 f es =
  {-# SCC "reduceDef" #-} do
  info <- getConstInfo f
  allowed <- asks envAllowedReductions
  let def = theDef info
      v   = v0 `applyE` es
      -- Non-terminating functions
      -- (i.e., those that failed the termination check)
      -- and delayed definitions
      -- are not unfolded unless explicitely permitted.
      dontUnfold =
        (defNonterminating info && notElem NonTerminatingReductions allowed)
        || (defDelayed info == Delayed && not unfoldDelayed)
      copatterns =
        case def of
          Function{funCopatternLHS = b} -> b
          _                             -> False
  case def of
    Constructor{conSrcCon = c} ->
      retSimpl $ notBlocked $ Con (c `withRangeOf` f) [] `applyE` es
    Primitive{primAbstr = ConcreteDef, primName = x, primClauses = cls} -> do
      pf <- fromMaybe __IMPOSSIBLE__ <$> getPrimitive' x
      if FunctionReductions `elem` allowed
        then reducePrimitive x v0 f es pf dontUnfold
                             cls (defCompiled info)
        else retSimpl $ notBlocked v
    _  -> do
      if FunctionReductions `elem` allowed ||
         (isJust (isProjection_ def) && ProjectionReductions `elem` allowed) || -- includes projection-like
         (isInlineFun def && InlineReductions `elem` allowed) ||
         (copatterns && CopatternReductions `elem` allowed)
        then
          reduceNormalE keepGoing v0 f (map notReduced es)
                       dontUnfold
                       (defClauses info) (defCompiled info)
        else retSimpl $ notBlocked v  -- Andrea(s), 2014-12-05 OK?

  where
    retSimpl v = (,v) <$> getSimplification

    reducePrimitive x v0 f es pf dontUnfold cls mcc
      | genericLength es < ar
                  = retSimpl $ NotBlocked Underapplied $ v0 `applyE` es -- not fully applied
      | otherwise = {-# SCC "reducePrimitive" #-} do
          let (es1,es2) = genericSplitAt ar es
              args1     = fromMaybe __IMPOSSIBLE__ $ mapM isApplyElim es1
          r <- primFunImplementation pf args1
          case r of
            NoReduction args1' -> do
              let es1' = map (fmap Apply) args1'
              if null cls then do
                retSimpl $ applyE (Def f []) <$> do
                  traverse id $
                    map mredToBlocked es1' ++ map notBlocked es2
               else
                reduceNormalE keepGoing v0 f
                             (es1' ++ map notReduced es2)
                             dontUnfold cls mcc
            YesReduction simpl v -> performedSimplification' simpl $
              keepGoing $ v `applyE` es2
      where
          ar  = primFunArity pf
          mredToBlocked :: MaybeReduced a -> Blocked a
          mredToBlocked (MaybeRed NotReduced  x) = notBlocked x
          mredToBlocked (MaybeRed (Reduced b) x) = x <$ b

    reduceNormalE :: (Term -> ReduceM (Simplification, Blocked Term)) -> Term -> QName -> [MaybeReduced Elim] -> Bool -> [Clause] -> Maybe CompiledClauses -> ReduceM (Simplification, Blocked Term)
    reduceNormalE keepGoing v0 f es dontUnfold def mcc = {-# SCC "reduceNormal" #-} do
      case def of
        _ | dontUnfold -> defaultResult -- non-terminating or delayed
        [] -> defaultResult -- no definition for head
        cls -> do
            ev <- appDefE_ f v0 cls mcc es
            case ev of
              NoReduction v -> do
                traceSDoc "tc.reduce'" 90 (vcat
                  [ text "*** tried to reduce' " <+> prettyTCM f
                  , text "    es =  " <+> sep (map (prettyTCM . ignoreReduced) es)
--                  [ text "*** tried to reduce' " <+> prettyTCM vfull
                  , text "    stuck on" <+> prettyTCM (ignoreBlocking v) ]) $ do
                  retSimpl v
              YesReduction simpl v -> performedSimplification' simpl $ do
                traceSDoc "tc.reduce'"  90 (text "*** reduced definition: " <+> prettyTCM f) $ do
                  traceSDoc "tc.reduce'"  95 (text "    result" <+> prettyTCM v) $ do
                    traceSDoc "tc.reduce'" 100 (text "    raw   " <+> text (show v)) $ do
                      keepGoing v
      where defaultResult = retSimpl $ NotBlocked AbsurdMatch vfull
            vfull         = v0 `applyE` map ignoreReduced es

-- | Reduce a non-primitive definition if it is a copy linking to another def.
reduceDefCopy :: QName -> Args -> TCM (Reduced () Term)
reduceDefCopy f vs = do
  info <- TCM.getConstInfo f
  if (defCopy info) then reduceDef_ info f vs else return $ NoReduction ()
  where
    reduceDef_ :: Definition -> QName -> Args -> TCM (Reduced () Term)
    reduceDef_ info f vs = do
      let v0   = Def f []
          args = map notReduced vs
          cls  = (defClauses info)
          mcc  = (defCompiled info)
      if (defDelayed info == Delayed) || (defNonterminating info)
       then return $ NoReduction ()
       else do
          ev <- runReduceM $ appDef_ f v0 cls mcc args
          case ev of
            YesReduction simpl t -> return $ YesReduction simpl t
            NoReduction args'    -> return $ NoReduction ()

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
appDef_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef_ f v0 cls mcc args = appDefE_ f v0 cls mcc $ map (fmap Apply) args

appDefE_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE_ f v0 cls mcc args =
  local (\ e -> e { envAppDef = Just f }) $
  maybe (appDefE' v0 cls args)
        (\cc -> appDefE v0 cc args) mcc


-- | Apply a defined function to it's arguments, using the compiled clauses.
--   The original term is the first argument applied to the third.
appDef :: Term -> CompiledClauses -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef v cc args = appDefE v cc $ map (fmap Apply) args

appDefE :: Term -> CompiledClauses -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE v cc es = do
  r <- matchCompiledE cc es
  case r of
    YesReduction simpl t -> return $ YesReduction simpl t
    NoReduction es'      -> return $ NoReduction $ applyE v <$> es'

-- | Apply a defined function to it's arguments, using the original clauses.
appDef' :: Term -> [Clause] -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef' v cls args = appDefE' v cls $ map (fmap Apply) args

appDefE' :: Term -> [Clause] -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE' v cls es = goCls cls $ map ignoreReduced es
  where
    goCls :: [Clause] -> [Elim] -> ReduceM (Reduced (Blocked Term) Term)
    goCls cl es = do
      traceSLn "tc.reduce'" 95 ("Reduce.goCls tries reduction, #clauses = " ++ show (length cl)) $ do
      case cl of
        -- Andreas, 2013-10-26  In case of an incomplete match,
        -- we just do not reduce.  This allows adding single function
        -- clauses after they have been type-checked, to type-check
        -- the remaining clauses (see Issue 907).
        -- Andrea(s), 2014-12-05:  We return 'MissingClauses' here, since this
        -- is the most conservative reason.
        [] -> return $ NoReduction $ NotBlocked MissingClauses $ v `applyE` es
        Clause{ namedClausePats = pats, clauseBody = body } : cls -> do
          let n = length pats
          -- if clause is underapplied, skip to next clause
          if length es < n then goCls cls es else do
            let (es0, es1) = splitAt n es
            (m, es0) <- matchCopatterns (unnumberPatVars pats) es0
            es <- return $ es0 ++ es1
            case m of
              No         -> goCls cls es
              DontKnow b -> return $ NoReduction $ b $> v `applyE` es
              Yes simpl vs -- vs is the subst. for the variables bound in body
                | isJust (getBodyUnraised body)  -- clause has body?
                                -> return $ YesReduction simpl $
                    -- TODO: let matchPatterns also return the reduced forms
                    -- of the original arguments!
                    -- Andreas, 2013-05-19 isn't this done now?
                    app vs body EmptyS `applyE` es1
                | otherwise     -> return $ NoReduction $ NotBlocked AbsurdMatch $ v `applyE` es

    -- Build an explicit substitution from arguments
    -- and execute it using parallel substitution.
    -- Calculating the de Bruijn indices: ;-) for the Bind case
    --   Simply-typed version
    --   (we are not interested in types, only in de Bruijn indices here)
    --   Γ ⊢ σ : Δ
    --   Γ ⊢ v : A
    --   Γ ⊢ (σ,v) : Δ.A
    --   Δ ⊢ λ b : A → B
    --   Δ.A ⊢ b : B
    app :: [Term] -> ClauseBody -> Substitution -> Term
    app []       (Body v)           sigma = applySubst sigma v
    app (v : vs) (Bind (Abs   _ b)) sigma = app vs b $ consS v sigma -- CBN
    app (v : vs) (Bind (NoAbs _ b)) sigma = app vs b sigma
    app  _        NoBody            sigma = __IMPOSSIBLE__
    app (_ : _)  (Body _)           sigma = __IMPOSSIBLE__
    app []       (Bind _)           sigma = __IMPOSSIBLE__

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

instance (Ord k, Reduce e) => Reduce (Map k e) where
    reduce' = traverse reduce'

instance Reduce Candidate where
  reduce' (Candidate u t eti) = Candidate <$> reduce' u <*> reduce' t <*> return eti

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
        let keepGoing v = (,notBlocked v) <$> getSimplification  -- Andrea(s), 2014-12-05 OK?
        (simpl, v) <- unfoldDefinition' False keepGoing (Def f []) f vs
        traceSDoc "tc.simplify'" 20 (
          text ("simplify': unfolding definition returns " ++ show simpl)
            <+> prettyTCM (ignoreBlocking v)) $ do
        case simpl of
          YesSimplification -> simplifyBlocked' v -- Dangerous, but if @simpl@ then @v /= Def f vs@
          NoSimplification  -> Def f <$> simplify' vs
      MetaV x vs -> MetaV x  <$> simplify' vs
      Con c vs   -> Con c    <$> simplify' vs
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
  simplify' (Proj f)  = pure $ Proj f

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

instance (Ord k, Simplify e) => Simplify (Map k e) where
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

instance Simplify ClauseBody where
    simplify' (Body   t) = Body   <$> simplify' t
    simplify' (Bind   b) = Bind   <$> simplify' b
    simplify'  NoBody   = return NoBody

instance Simplify DisplayForm where
  simplify' (Display n ps v) = Display n <$> simplify' ps <*> return v

instance Simplify Candidate where
  simplify' (Candidate u t eti) = Candidate <$> simplify' u <*> simplify' t <*> return eti

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
    normalise' = ignoreBlocking <.> rewriteAfter (reduceB' >=> traverse normaliseArgs)
      where
        normaliseArgs :: Term -> ReduceM Term
        normaliseArgs v = case v of
                Var n vs    -> Var n <$> normalise' vs
                Con c vs    -> Con c <$> normalise' vs
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
  normalise' (Proj f)  = pure $ Proj f

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

instance Normalise ClauseBody where
    normalise' (Body   t) = Body   <$> normalise' t
    normalise' (Bind   b) = Bind   <$> normalise' b
    normalise'  NoBody   = return NoBody

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

instance Normalise a => Normalise (Pattern' a) where
  normalise' p = case p of
    VarP x       -> VarP <$> normalise' x
    LitP _       -> return p
    ConP c mt ps -> ConP c <$> normalise' mt <*> normalise' ps
    DotP v       -> DotP <$> normalise' v
    ProjP _      -> return p

instance Normalise DisplayForm where
  normalise' (Display n ps v) = Display n <$> normalise' ps <*> return v

instance (Ord k, Normalise e) => Normalise (Map k e) where
    normalise' = traverse normalise'

instance Normalise a => Normalise (Maybe a) where
    normalise' = traverse normalise'

instance Normalise Candidate where
  normalise' (Candidate u t eti) = Candidate <$> normalise' u <*> normalise' t <*> return eti

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
          Con c vs    -> Con c <$> instantiateFull' vs
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

instance InstantiateFull a => InstantiateFull (Pattern' a) where
    instantiateFull' (VarP x)       = VarP <$> instantiateFull' x
    instantiateFull' (DotP t)       = DotP <$> instantiateFull' t
    instantiateFull' (ConP n mt ps) = ConP n <$> instantiateFull' mt <*> instantiateFull' ps
    instantiateFull' l@LitP{}       = return l
    instantiateFull' p@ProjP{}      = return p

instance InstantiateFull ClauseBody where
    instantiateFull' (Body   t) = Body   <$> instantiateFull' t
    instantiateFull' (Bind   b) = Bind   <$> instantiateFull' b
    instantiateFull'  NoBody    = return NoBody

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
  instantiateFull' (Proj f)  = pure $ Proj f

instance (Ord k, InstantiateFull e) => InstantiateFull (Map k e) where
    instantiateFull' = traverse instantiateFull'

instance (Eq k, Hashable k, InstantiateFull e) => InstantiateFull (HashMap k e) where
    instantiateFull' = traverse instantiateFull'

instance InstantiateFull ModuleName where
    instantiateFull' = return

instance InstantiateFull Scope where
    instantiateFull' = return

instance InstantiateFull Signature where
  instantiateFull' (Sig a b c) = uncurry3 Sig <$> instantiateFull' (a, b, c)

instance InstantiateFull Section where
  instantiateFull' (Section tel n) = flip Section n <$> instantiateFull' tel

instance (Subst t a, InstantiateFull a) => InstantiateFull (Tele a) where
  instantiateFull' EmptyTel = return EmptyTel
  instantiateFull' (ExtendTel a b) = uncurry ExtendTel <$> instantiateFull' (a, b)

instance InstantiateFull Char where
    instantiateFull' = return

instance InstantiateFull Definition where
    instantiateFull' (Defn rel x t pol occ df i c inst d) = do
      (t, df, d) <- instantiateFull' (t, df, d)
      return $ Defn rel x t pol occ df i c inst d

instance InstantiateFull NLPat where
  instantiateFull' (PVar x)   = return $ PVar x
  instantiateFull' (PWild)    = return PWild
  instantiateFull' (PDef x y) = PDef <$> instantiateFull' x <*> instantiateFull' y
  instantiateFull' (PLam x y) = PLam x <$> instantiateFull' y
  instantiateFull' (PPi x y)  = PPi <$> instantiateFull' x <*> instantiateFull' y
  instantiateFull' (PBoundVar x y) = PBoundVar x <$> instantiateFull' y
  instantiateFull' (PTerm x)  = PTerm <$> instantiateFull' x

instance InstantiateFull RewriteRule where
  instantiateFull' (RewriteRule q gamma lhs rhs t) =
    RewriteRule q
      <$> instantiateFull' gamma
      <*> instantiateFull' lhs
      <*> instantiateFull' rhs
      <*> instantiateFull' t

instance InstantiateFull a => InstantiateFull (Open a) where
  instantiateFull' (OpenThing n a) = OpenThing n <$> instantiateFull' a

instance InstantiateFull DisplayForm where
  instantiateFull' (Display n ps v) = uncurry (Display n) <$> instantiateFull' (ps, v)

instance InstantiateFull DisplayTerm where
  instantiateFull' (DTerm v)       = DTerm <$> instantiateFull' v
  instantiateFull' (DDot  v)       = DDot  <$> instantiateFull' v
  instantiateFull' (DCon c vs)     = DCon c <$> instantiateFull' vs
  instantiateFull' (DDef c es)     = DDef c <$> instantiateFull' es
  instantiateFull' (DWithApp v vs ws) = uncurry3 DWithApp <$> instantiateFull' (v, vs, ws)

instance InstantiateFull Defn where
    instantiateFull' d = case d of
      Axiom{} -> return d
      Function{ funClauses = cs, funCompiled = cc, funInv = inv } -> do
        (cs, cc, inv) <- instantiateFull' (cs, cc, inv)
        return $ d { funClauses = cs, funCompiled = cc, funInv = inv }
      Datatype{ dataSort = s, dataClause = cl } -> do
        s  <- instantiateFull' s
        cl <- instantiateFull' cl
        return $ d { dataSort = s, dataClause = cl }
      Record{ recConType = t, recClause = cl, recTel = tel } -> do
        t   <- instantiateFull' t
        cl  <- instantiateFull' cl
        tel <- instantiateFull' tel
        return $ d { recConType = t, recClause = cl, recTel = tel }
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
    instantiateFull' (Clause r tel ps b t catchall) =
       Clause r <$> instantiateFull' tel
       <*> instantiateFull' ps
       <*> instantiateFull' b
       <*> instantiateFull' t
       <*> return catchall

instance InstantiateFull Interface where
    instantiateFull' (Interface h ms mod scope inside
                               sig b hsImports hsImportsUHC highlighting pragmas patsyns) =
        Interface h ms mod scope inside
            <$> instantiateFull' sig
            <*> instantiateFull' b
            <*> return hsImports
            <*> return hsImportsUHC
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
  instantiateFull' (Candidate u t eti) = Candidate <$> instantiateFull' u <*> instantiateFull' t <*> return eti
