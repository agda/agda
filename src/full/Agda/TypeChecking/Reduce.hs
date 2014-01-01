{-# LANGUAGE CPP, PatternGuards, TupleSections,
             TypeSynonymInstances, FlexibleInstances #-}

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
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Base (Scope)
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.CompiledClause
import {-# SOURCE #-} Agda.TypeChecking.Pretty

import {-# SOURCE #-} Agda.TypeChecking.Patterns.Match
import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Match

import Agda.Utils.Monad
import Agda.Utils.HashMap (HashMap)

#include "../undefined.h"
import Agda.Utils.Impossible

traceFun :: String -> TCM a -> TCM a
traceFun s m = do
  reportSLn "tc.inst" 100 $ "[ " ++ s
  x <- m
  reportSLn "tc.inst" 100 $ "]"
  return x

traceFun' :: Show a => String -> TCM a -> TCM a
traceFun' s m = do
  reportSLn "tc.inst" 100 $ "[ " ++ s
  x <- m
  reportSLn "tc.inst" 100 $ "  result = " ++ show x ++ "\n]"
  return x

-- | Instantiate something.
--   Results in an open meta variable or a non meta.
--   Doesn't do any reduction, and preserves blocking tags (when blocking meta
--   is uninstantiated).
class Instantiate t where
    instantiate :: t -> TCM t

instance Instantiate Term where
  instantiate t@(MetaV x es) = do
    mi <- mvInstantiation <$> lookupMeta x
    case mi of
      InstV a                        -> instantiate $ a `applyE` es
      Open                           -> return t
      OpenIFS                        -> return t
      BlockedConst _                 -> return t
      PostponedTypeCheckingProblem _ -> return t
      InstS _                        -> __IMPOSSIBLE__
  instantiate (Level l) = levelTm <$> instantiate l
  instantiate (Sort s) = sortTm <$> instantiate s
  instantiate v@Shared{} = updateSharedTerm instantiate v
  instantiate t = return t

instance Instantiate Level where
  instantiate (Max as) = levelMax <$> instantiate as

instance Instantiate PlusLevel where
  instantiate l@ClosedLevel{} = return l
  instantiate (Plus n a) = Plus n <$> instantiate a

instance Instantiate LevelAtom where
  instantiate l = case l of
    MetaLevel m vs -> do
      v <- instantiate (MetaV m vs)
      case ignoreSharing v of
        MetaV m vs -> return $ MetaLevel m vs
        _          -> return $ UnreducedLevel v
    UnreducedLevel l -> UnreducedLevel <$> instantiate l
    _ -> return l

instance Instantiate a => Instantiate (Blocked a) where
  instantiate v@NotBlocked{} = return v
  instantiate v@(Blocked x u) = do
    mi <- mvInstantiation <$> lookupMeta x
    case mi of
      InstV _                        -> notBlocked <$> instantiate u
      Open                           -> return v
      OpenIFS                        -> return v
      BlockedConst _                 -> return v
      PostponedTypeCheckingProblem _ -> return v
      InstS _                        -> __IMPOSSIBLE__

instance Instantiate Type where
    instantiate (El s t) = El <$> instantiate s <*> instantiate t

instance Instantiate Sort where
  instantiate s = case s of
    Type l -> levelSort <$> instantiate l
    _      -> return s

instance Instantiate Elim where
  instantiate (Apply v) = Apply <$> instantiate v
  instantiate (Proj f)  = pure $ Proj f

instance Instantiate t => Instantiate (Abs t) where
  instantiate = traverse instantiate

instance Instantiate t => Instantiate (Arg t) where
    instantiate = traverse instantiate

instance Instantiate t => Instantiate (Dom t) where
    instantiate = traverse instantiate

instance Instantiate t => Instantiate [t] where
    instantiate = traverse instantiate

instance (Instantiate a, Instantiate b) => Instantiate (a,b) where
    instantiate (x,y) = (,) <$> instantiate x <*> instantiate y


instance (Instantiate a, Instantiate b,Instantiate c) => Instantiate (a,b,c) where
    instantiate (x,y,z) = (,,) <$> instantiate x <*> instantiate y <*> instantiate z

instance Instantiate a => Instantiate (Closure a) where
    instantiate cl = do
	x <- enterClosure cl instantiate
	return $ cl { clValue = x }

instance Instantiate Telescope where
  instantiate tel = return tel

instance Instantiate Constraint where
  instantiate (ValueCmp cmp t u v) = do
    (t,u,v) <- instantiate (t,u,v)
    return $ ValueCmp cmp t u v
  instantiate (ElimCmp cmp t v as bs) =
    ElimCmp cmp <$> instantiate t <*> instantiate v <*> instantiate as <*> instantiate bs
  instantiate (LevelCmp cmp u v)   = uncurry (LevelCmp cmp) <$> instantiate (u,v)
  instantiate (TypeCmp cmp a b)    = uncurry (TypeCmp cmp) <$> instantiate (a,b)
  instantiate (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp)  <$> instantiate (tela,telb)
  instantiate (SortCmp cmp a b)    = uncurry (SortCmp cmp) <$> instantiate (a,b)
  instantiate (Guarded c pid)      = Guarded <$> instantiate c <*> pure pid
  instantiate (UnBlock m)          = return $ UnBlock m
  instantiate (FindInScope m args) = FindInScope m <$> mapM instantiate args
  instantiate (IsEmpty r t)        = IsEmpty r <$> instantiate t

instance (Ord k, Instantiate e) => Instantiate (Map k e) where
    instantiate = traverse instantiate


---------------------------------------------------------------------------
-- * Reduction to weak head normal form.
---------------------------------------------------------------------------

ifBlocked :: MonadTCM tcm =>  Term -> (MetaId -> Term -> tcm a) -> (Term -> tcm a) -> tcm a
ifBlocked t blocked unblocked = do
  t <- liftTCM $ reduceB t
  case ignoreSharing <$> t of
    Blocked m _            -> blocked m (ignoreBlocking t)
    NotBlocked (MetaV m _) -> blocked m (ignoreBlocking t)
    NotBlocked _           -> unblocked (ignoreBlocking t)

ifBlockedType :: MonadTCM tcm => Type -> (MetaId -> Type -> tcm a) -> (Type -> tcm a) -> tcm a
ifBlockedType t blocked unblocked = do
  t <- liftTCM $ reduceB t
  case ignoreSharing . unEl <$> t of
    Blocked m _            -> blocked m (ignoreBlocking t)
    NotBlocked (MetaV m _) -> blocked m (ignoreBlocking t)
    NotBlocked _           -> unblocked (ignoreBlocking t)

class Reduce t where
    reduce  :: t -> TCM t
    reduceB :: t -> TCM (Blocked t)

    reduce  t = ignoreBlocking <$> reduceB t
    reduceB t = notBlocked <$> reduce t

instance Reduce Type where
    reduce  (El s t) = El s <$> reduce t
    reduceB (El s t) = fmap (El s) <$> reduceB t

instance Reduce Sort where
    reduce s = {-# SCC "reduce<Sort>" #-}
      ifNotM hasUniversePolymorphism (red s) $ {- else -} red =<< instantiateFull s
      where
        red s = do
          s <- instantiate s
          case s of
            DLub s1 s2 -> do
              s <- dLub <$> reduce s1 <*> reduce s2
              case s of
                DLub{}  -> return s
                _       -> reduce s   -- TODO: not so nice
            Prop       -> return s
            Type s'    -> levelSort <$> reduce s'
            Inf        -> return Inf

instance Reduce Elim where
  reduce (Apply v) = Apply <$> reduce v
  reduce (Proj f)  = pure $ Proj f

instance Reduce Level where
  reduce  (Max as) = levelMax <$> mapM reduce as
  reduceB (Max as) = fmap levelMax . traverse id <$> traverse reduceB as

instance Reduce PlusLevel where
  reduceB l@ClosedLevel{} = return $ notBlocked l
  reduceB (Plus n l) = fmap (Plus n) <$> reduceB l

instance Reduce LevelAtom where
  reduceB l = case l of
    MetaLevel m vs   -> fromTm (MetaV m vs)
    NeutralLevel v   -> return $ NotBlocked $ NeutralLevel v
    BlockedLevel m v ->
      ifM (isInstantiatedMeta m) (fromTm v) (return $ Blocked m $ BlockedLevel m v)
    UnreducedLevel v -> fromTm v
    where
      fromTm v = do
        bv <- reduceB v
        let v = ignoreBlocking bv
        case ignoreSharing <$> bv of
          NotBlocked (MetaV m vs) -> return $ NotBlocked $ MetaLevel m vs
          Blocked m _             -> return $ Blocked m  $ BlockedLevel m v
          NotBlocked _            -> return $ NotBlocked $ NeutralLevel v


instance (Subst t, Reduce t) => Reduce (Abs t) where
  reduce b@(Abs x _) = Abs x <$> underAbstraction_ b reduce
  reduce (NoAbs x v) = NoAbs x <$> reduce v

-- Lists are never blocked
instance Reduce t => Reduce [t] where
    reduce = traverse reduce

instance Reduce t => Reduce (Arg t) where
    reduce a = case getRelevance a of
                 Irrelevant -> return a             -- Don't reduce irr. args!?
                 _          -> traverse reduce a

    reduceB t = traverse id <$> traverse reduceB t

instance Reduce t => Reduce (Dom t) where
    reduce = traverse reduce
    reduceB t = traverse id <$> traverse reduceB t

-- Tuples are never blocked
instance (Reduce a, Reduce b) => Reduce (a,b) where
    reduce (x,y)  = (,) <$> reduce x <*> reduce y

instance (Reduce a, Reduce b,Reduce c) => Reduce (a,b,c) where
    reduce (x,y,z) = (,,) <$> reduce x <*> reduce y <*> reduce z

instance Reduce Term where
  reduceB v = {-# SCC "reduce<Term>" #-} do
    v <- instantiate v
    case v of
--    Andreas, 2012-11-05 not reducing meta args does not destroy anything
--    and seems to save 2% sec on the standard library
--      MetaV x args -> notBlocked . MetaV x <$> reduce args
      MetaV x es -> return $ notBlocked v
      Def f es   -> unfoldDefinitionE False reduceB (Def f []) f es
      Con c args -> do
          -- Constructors can reduce when they come from an
          -- instantiated module.
          v <- unfoldDefinition False reduceB (Con c []) (conName c) args
          traverse reduceNat v
      Sort s   -> fmap sortTm <$> reduceB s
      Level l  -> fmap levelTm <$> reduceB l
      Pi _ _   -> return $ notBlocked v
      Lit _    -> return $ notBlocked v
      Var _ _  -> return $ notBlocked v
      Lam _ _  -> return $ notBlocked v
      DontCare _ -> return $ notBlocked v
      Shared{}   -> updateSharedTermF reduceB v
    where
      -- NOTE: reduceNat can traverse the entire term.
      reduceNat v@Shared{} = updateSharedTerm reduceNat v
      reduceNat v@(Con c []) = do
        mz  <- getBuiltin' builtinZero
        case v of
          _ | Just v == mz  -> return $ Lit $ LitInt (getRange c) 0
          _		    -> return v
      reduceNat v@(Con c [a]) | notHidden a && isRelevant a = do
        ms  <- fmap ignoreSharing <$> getBuiltin' builtinSuc
        case v of
          _ | Just (Con c []) == ms -> inc <$> reduce (unArg a)
          _	                    -> return v
          where
            inc w = case ignoreSharing w of
              Lit (LitInt r n) -> Lit (LitInt (fuseRange c r) $ n + 1)
              _                -> Con c [defaultArg w]
      reduceNat v = return v

-- | If the first argument is 'True', then a single delayed clause may
-- be unfolded.
unfoldDefinition ::
  Bool -> (Term -> TCM (Blocked Term)) ->
  Term -> QName -> Args -> TCM (Blocked Term)
unfoldDefinition b keepGoing v f args = snd <$> do
  unfoldDefinition' b (\ t -> (NoSimplification,) <$> keepGoing t) v f $
    map Apply args

unfoldDefinitionE ::
  Bool -> (Term -> TCM (Blocked Term)) ->
  Term -> QName -> Elims -> TCM (Blocked Term)
unfoldDefinitionE b keepGoing v f es = snd <$>
  unfoldDefinition' b (\ t -> (NoSimplification,) <$> keepGoing t) v f es

unfoldDefinition' ::
  Bool -> (Term -> TCM (Simplification, Blocked Term)) ->
  Term -> QName -> Elims -> TCM (Simplification, Blocked Term)
unfoldDefinition' unfoldDelayed keepGoing v0 f es =
  {-# SCC "reduceDef" #-} do
  info <- getConstInfo f
  let def = theDef info
      v   = v0 `applyE` es
  case def of
    Constructor{conSrcCon = c} ->
      retSimpl $ notBlocked $ Con (c `withRangeOf` f) [] `applyE` es
    Primitive{primAbstr = ConcreteDef, primName = x, primClauses = cls} -> do
      pf <- getPrimitive x
      reducePrimitive x v0 f es pf (defDelayed info) (defNonterminating info)
                      cls (defCompiled info)
    _  -> do
      allowed <- asks envAllowedReductions
{-
      -- case f is projection-like:
      if isProperProjection def then
        if ProjectionReductions `elem` allowed then do
          -- we cannot call elimView right away, since it calls back to reduce
          -- get rid of projection if possible
          (simpl, w) <- onlyReduceProjections $ do
            reduceNormal (retSimpl <=< reduceB) v0 f (map notReduced args)
              (defDelayed info) (defNonterminating info)
              (defClauses info) (defCompiled info)
          -- Now @w@ should not have any reducible projection in the head.
          -- By not allowing reentrace (dontReduceProjections),
          -- we can now call elimView without risk of circularity.
          case w of
            Blocked{} -> return (simpl, w)
            NotBlocked w' -> do
              ev <- dontReduceProjections $ elimView w'
              case ev of
                DefElim f es -> performedSimplification' simpl $ do
                  reduceDefElim f es
                _ -> return (simpl, w)
        else retSimpl $ notBlocked v
       -- case f is not a projection:
       else if FunctionReductions `elem` allowed then
        -- proceed as before, without calling elimView
-}
      if FunctionReductions `elem` allowed ||
         (isJust (isProjection_ def) && ProjectionReductions `elem` allowed)  -- includes projection-like
       then
        reduceNormalE keepGoing v0 f (map notReduced es)
                       (defDelayed info) (defNonterminating info)
                       (defClauses info) (defCompiled info)
        else retSimpl $ notBlocked v

  where
    retSimpl v = (,v) <$> asks envSimplification
{-
    reduceDefElim :: QName -> [Elim] -> TCM (Simplification, Blocked Term)
    reduceDefElim f es = do
      info <- getConstInfo f
      reduceNormalE keepGoing (Def f []) f (map notReduced es)
                       (defDelayed info) (defNonterminating info)
                       (defClauses info) (defCompiled info)
-}

    reducePrimitive x v0 f es pf delayed nonterminating cls mcc
      | genericLength es < ar
                  = retSimpl $ notBlocked $ v0 `applyE` es -- not fully applied
      | otherwise = {-# SCC "reducePrimitive" #-} do
          let (es1,es2) = genericSplitAt ar es
              args1     = maybe __IMPOSSIBLE__ id $ mapM isApplyElim es1
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
                             delayed nonterminating cls mcc
            YesReduction simpl v -> performedSimplification' simpl $
              keepGoing $ v `applyE` es2
      where
          ar  = primFunArity pf
          mredToBlocked :: MaybeReduced a -> Blocked a
          mredToBlocked (MaybeRed NotReduced  x) = notBlocked x
          mredToBlocked (MaybeRed (Reduced b) x) = x <$ b

{-
    reduceNormal ::  (Term -> TCM (Simplification, Blocked Term)) -> Term -> QName -> [MaybeReduced (Arg Term)] -> Delayed -> Bool -> [Clause] -> Maybe CompiledClauses -> TCM (Simplification, Blocked Term)
    reduceNormal keepGoing v0 f args = reduceNormalE keepGoing v0 f $ map (fmap Apply) args
-}

    reduceNormalE :: (Term -> TCM (Simplification, Blocked Term)) -> Term -> QName -> [MaybeReduced Elim] -> Delayed -> Bool -> [Clause] -> Maybe CompiledClauses -> TCM (Simplification, Blocked Term)
    reduceNormalE keepGoing v0 f es delayed nonterminating def mcc = {-# SCC "reduceNormal" #-} do
      case def of
        _ | nonterminating -> defaultResult
        _ | Delayed <- delayed,
            not unfoldDelayed -> defaultResult
        [] -> defaultResult -- no definition for head
{- OBSOLETE
        -- stop here if we only want to reduce (proper) projections
        -- but the symbol @f@ is not one
        cls -> ifM (asks envOnlyReduceProjections `and2M` do not . maybe False projProper <$> isProjection f) defaultResult $ do
-}
{-
        cls -> allowAllReductions $ do
            -- In subterms, we allow all reductions.
-}
        cls -> do
            ev <- appDefE_ f v0 cls mcc es
            case ev of
              NoReduction v -> do
                reportSDoc "tc.reduce" 90 $ vcat
                  [ text "*** tried to reduce " <+> prettyTCM f
                  , text "    es =  " <+> sep (map (prettyTCM . ignoreReduced) es)
--                  [ text "*** tried to reduce " <+> prettyTCM vfull
                  , text "    stuck on" <+> prettyTCM (ignoreBlocking v) ]
                retSimpl v
              YesReduction simpl v -> performedSimplification' simpl $ do
                reportSDoc "tc.reduce" 90 $ vcat
                  [ text "*** reduced definition: " <+> prettyTCM f
                  ]
                reportSDoc "tc.reduce"  95 $ text "    result" <+> prettyTCM v
                reportSDoc "tc.reduce" 100 $ text "    raw   " <+> text (show v)
                keepGoing v
      where defaultResult = retSimpl $ notBlocked $ vfull
            vfull         = v0 `applyE` map ignoreReduced es
--      where defaultResult = retSimpl $ notBlocked $ v0 `apply` (map ignoreReduced args)

-- | Reduce a non-primitive definition if it is a copy linking to another def.
reduceDefCopy :: QName -> Args -> TCM (Reduced () Term)
reduceDefCopy f vs = do
  info <- getConstInfo f
  if (defCopy info) then reduceDef_ info f vs else return $ NoReduction ()

-- | Reduce a non-primitive definition once unless it is delayed.
reduceDef :: QName -> Args -> TCM (Reduced () Term)
reduceDef f vs = do
  info <- getConstInfo f
  reduceDef_ info f vs

reduceDef_ :: Definition -> QName -> Args -> TCM (Reduced () Term)
reduceDef_ info f vs = do
  let v0   = Def f []
      args = map notReduced vs
      cls  = (defClauses info)
      mcc  = (defCompiled info)
  if (defDelayed info == Delayed) || (defNonterminating info)
   then return $ NoReduction ()
   else do
      ev <- appDef_ f v0 cls mcc args
      case ev of
        YesReduction simpl t -> return $ YesReduction simpl t
        NoReduction args'    -> return $ NoReduction ()

-- | Apply a definition using the compiled clauses, or fall back to
--   ordinary clauses if no compiled clauses exist.
appDef_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> MaybeReducedArgs -> TCM (Reduced (Blocked Term) Term)
appDef_ f v0 cls mcc args = appDefE_ f v0 cls mcc $ map (fmap Apply) args

appDefE_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> MaybeReducedElims -> TCM (Reduced (Blocked Term) Term)
appDefE_ f v0 cls mcc args =
  local (\ e -> e { envAppDef = Just f }) $ do
    maybe (appDefE' v0 cls args)
          (\cc -> appDefE v0 cc args) mcc


-- | Apply a defined function to it's arguments, using the compiled clauses.
--   The original term is the first argument applied to the third.
appDef :: Term -> CompiledClauses -> MaybeReducedArgs -> TCM (Reduced (Blocked Term) Term)
appDef v cc args = appDefE v cc $ map (fmap Apply) args

appDefE :: Term -> CompiledClauses -> MaybeReducedElims -> TCM (Reduced (Blocked Term) Term)
appDefE v cc es = liftTCM $ do
  r <- matchCompiledE cc es
  case r of
    YesReduction simpl t -> return $ YesReduction simpl t
    NoReduction es'      -> return $ NoReduction $ applyE v <$> es'

-- | Apply a defined function to it's arguments, using the original clauses.
appDef' :: Term -> [Clause] -> MaybeReducedArgs -> TCM (Reduced (Blocked Term) Term)
appDef' v cls args = appDefE' v cls $ map (fmap Apply) args

{- OLD.  With varying function arity, check for underapplication is UNSOUND.
appDefE' :: Term -> [Clause] -> MaybeReducedElims -> TCM (Reduced (Blocked Term) Term)
appDefE' _ [] _ = {- ' -} __IMPOSSIBLE__
appDefE' v cls@(Clause {clausePats = ps} : _) es
    -- case underapplied: no reduction
  | m < n     = return $ NoReduction $ notBlocked $ v `applyE` map ignoreReduced es
  | otherwise = do
    let (es0, es1) = splitAt n es
    r <- goCls cls (map ignoreReduced es0)
    case r of
      YesReduction simpl u -> return $ YesReduction simpl $ u `applyE` map ignoreReduced es1
      NoReduction v        -> return $ NoReduction $ (`applyE` map ignoreReduced es1) <$> v
  where

    n = genericLength ps
    m = genericLength es
-}
appDefE' :: Term -> [Clause] -> MaybeReducedElims -> TCM (Reduced (Blocked Term) Term)
appDefE' v cls es = goCls cls $ map ignoreReduced es
  where
    goCls :: [Clause] -> [Elim] -> TCM (Reduced (Blocked Term) Term)
    goCls cl es = do
      reportSLn "tc.reduce" 95 $ "Reduce.goCls tries reduction, #clauses = " ++ show (length cl)
      let cantReduce es = return $ NoReduction $ notBlocked $ v `applyE` es
      case cl of
        -- Andreas, 2013-10-26  In case of an incomplete match,
        -- we just do not reduce.  This allows adding single function
        -- clauses after they have been type-checked, to type-check
        -- the remaining clauses (see Issue 907).
        [] -> cantReduce es -- WAS: typeError $ IncompletePatternMatching v es
        cl @ Clause { clauseBody = body } : cls -> do
          let pats = namedClausePats cl
              n    = length pats
          -- if clause is underapplied, skip to next clause
          if length es < n then goCls cls es else do
            let (es0, es1) = splitAt n es
            (m, es0) <- matchCopatterns pats es0
            es <- return $ es0 ++ es1
            case m of
              No                -> goCls cls es
              DontKnow Nothing  -> cantReduce es
              DontKnow (Just m) -> return $ NoReduction $ blocked m $ v `applyE` es
              Yes simpl vs -- vs is the subst. for the variables bound in body
                | isJust (getBody body)  -- clause has body?
                                -> return $ YesReduction simpl $
                    -- TODO: let matchPatterns also return the reduced forms
                    -- of the original arguments!
                    -- Andreas, 2013-05-19 isn't this done now?
                    app vs body EmptyS `applyE` es1
                | otherwise     -> cantReduce es


    -- NEW version, building an explicit substitution from arguments
    -- and executing it using parallel substitution.
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
--    app (v : vs) (Bind b) sigma = app es (absBody b) (v :# sigma) -- CBN
    app (v : vs) (Bind (Abs   _ b)) sigma = app vs b (v :# sigma) -- CBN
    app (v : vs) (Bind (NoAbs _ b)) sigma = app vs b sigma
    app  _        NoBody            sigma = __IMPOSSIBLE__
    app (_ : _)	 (Body _)           sigma = __IMPOSSIBLE__
    app []       (Bind _)           sigma = __IMPOSSIBLE__

{- OLD version, one substitution after another
    app :: [Elim] -> ClauseBody -> Term
    app []           (Body v') = v'
    app (Proj f : es)    b         = app es b
    app (Apply arg : es) (Bind b)  = app es $ absApp b $ unArg arg -- CBN
    app  _            NoBody   = __IMPOSSIBLE__
    app (_ : _)	     (Body _)  = __IMPOSSIBLE__
    app []           (Bind _)  = __IMPOSSIBLE__
-}

instance Reduce a => Reduce (Closure a) where
    reduce cl = do
	x <- enterClosure cl reduce
	return $ cl { clValue = x }

instance Reduce Telescope where
  reduce tel = return tel

instance Reduce Constraint where
  reduce (ValueCmp cmp t u v) = do
    (t,u,v) <- reduce (t,u,v)
    return $ ValueCmp cmp t u v
  reduce (ElimCmp cmp t v as bs) =
    ElimCmp cmp <$> reduce t <*> reduce v <*> reduce as <*> reduce bs
  reduce (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> reduce (u,v)
  reduce (TypeCmp cmp a b)     = uncurry (TypeCmp cmp) <$> reduce (a,b)
  reduce (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp)  <$> reduce (tela,telb)
  reduce (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> reduce (a,b)
  reduce (Guarded c pid)       = Guarded <$> reduce c <*> pure pid
  reduce (UnBlock m)           = return $ UnBlock m
  reduce (FindInScope m cands) = FindInScope m <$> mapM reduce cands
  reduce (IsEmpty r t)         = IsEmpty r <$> reduce t

instance (Ord k, Reduce e) => Reduce (Map k e) where
    reduce = traverse reduce

---------------------------------------------------------------------------
-- * Simplification
---------------------------------------------------------------------------

-- | Only unfold definitions if this leads to simplification
--   which means that a constructor/literal pattern is matched.
class Simplify t where
  simplify :: t -> TCM t

instance Simplify Term where
  simplify v = do
    v <- instantiate v
    case v of
      Def f vs   -> do
        let keepGoing v = (,NotBlocked v) <$> asks envSimplification
        (simpl, v) <- unfoldDefinition' False keepGoing (Def f []) f vs
        reportSDoc "tc.simplify" 20 $
          text ("simplify: unfolding definition returns " ++ show simpl)
            <+> prettyTCM (ignoreBlocking v)
        case simpl of
          YesSimplification -> simplifyBlocked v -- Dangerous, but if @simpl@ then @v /= Def f vs@
          NoSimplification  -> Def f <$> simplify vs
      MetaV x vs -> MetaV x  <$> simplify vs
      Con c vs   -> Con c    <$> simplify vs
      Sort s     -> sortTm   <$> simplify s
      Level l    -> levelTm  <$> simplify l
      Pi a b     -> Pi       <$> simplify a <*> simplify b
      Lit l      -> return v
      Var i vs   -> Var i    <$> simplify vs
      Lam h v    -> Lam h    <$> simplify v
      DontCare v -> dontCare <$> simplify v
      Shared{}   -> updateSharedTerm simplify v

simplifyBlocked :: Simplify t => Blocked t -> TCM t
simplifyBlocked (Blocked _ t)  = return t
simplifyBlocked (NotBlocked t) = simplify t

instance Simplify Type where
    simplify (El s t) = El <$> simplify s <*> simplify t

instance Simplify Elim where
  simplify (Apply v) = Apply <$> simplify v
  simplify (Proj f)  = pure $ Proj f

instance Simplify Sort where
    simplify s = do
      case s of
        DLub s1 s2 -> dLub <$> simplify s1 <*> simplify s2
        Type s     -> levelSort <$> simplify s
        Prop       -> return s
        Inf        -> return s

instance Simplify Level where
  simplify (Max as) = levelMax <$> simplify as

instance Simplify PlusLevel where
  simplify l@ClosedLevel{} = return l
  simplify (Plus n l) = Plus n <$> simplify l

instance Simplify LevelAtom where
  simplify l = do
    l <- instantiate l
    case l of
      MetaLevel m vs   -> MetaLevel m <$> simplify vs
      BlockedLevel m v -> BlockedLevel m <$> simplify v
      NeutralLevel v   -> NeutralLevel   <$> simplify v -- ??
      UnreducedLevel v -> UnreducedLevel <$> simplify v -- ??

instance (Subst t, Simplify t) => Simplify (Abs t) where
    simplify a@(Abs x _) = Abs x <$> underAbstraction_ a simplify
    simplify (NoAbs x v) = NoAbs x <$> simplify v

instance Simplify t => Simplify (Arg t) where
    simplify = traverse simplify

instance Simplify t => Simplify (Named name t) where
    simplify = traverse simplify

instance Simplify t => Simplify (Dom t) where
    simplify = traverse simplify

instance Simplify t => Simplify [t] where
    simplify = traverse simplify

instance (Ord k, Simplify e) => Simplify (Map k e) where
    simplify = traverse simplify

instance Simplify a => Simplify (Maybe a) where
    simplify = traverse simplify

instance (Simplify a, Simplify b) => Simplify (a,b) where
    simplify (x,y) = (,) <$> simplify x <*> simplify y

instance (Simplify a, Simplify b, Simplify c) => Simplify (a,b,c) where
    simplify (x,y,z) =
	do  (x,(y,z)) <- simplify (x,(y,z))
	    return (x,y,z)

instance Simplify a => Simplify (Closure a) where
    simplify cl = do
	x <- enterClosure cl simplify
	return $ cl { clValue = x }

instance (Subst a, Simplify a) => Simplify (Tele a) where
  simplify EmptyTel        = return EmptyTel
  simplify (ExtendTel a b) = uncurry ExtendTel <$> simplify (a, b)

instance Simplify ProblemConstraint where
  simplify (PConstr pid c) = PConstr pid <$> simplify c

instance Simplify Constraint where
  simplify (ValueCmp cmp t u v) = do
    (t,u,v) <- simplify (t,u,v)
    return $ ValueCmp cmp t u v
  simplify (ElimCmp cmp t v as bs) =
    ElimCmp cmp <$> simplify t <*> simplify v <*> simplify as <*> simplify bs
  simplify (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> simplify (u,v)
  simplify (TypeCmp cmp a b)     = uncurry (TypeCmp cmp) <$> simplify (a,b)
  simplify (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp) <$> simplify (tela,telb)
  simplify (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> simplify (a,b)
  simplify (Guarded c pid)       = Guarded <$> simplify c <*> pure pid
  simplify (UnBlock m)           = return $ UnBlock m
  simplify (FindInScope m cands) = FindInScope m <$> mapM simplify cands
  simplify (IsEmpty r t)         = IsEmpty r <$> simplify t

instance Simplify Bool where
  simplify = return

instance Simplify Pattern where
  simplify p = case p of
    VarP _       -> return p
    LitP _       -> return p
    ConP c mt ps -> ConP c <$> simplify mt <*> simplify ps
    DotP v       -> DotP <$> simplify v
    ProjP _      -> return p

instance Simplify ClauseBody where
    simplify (Body   t) = Body   <$> simplify t
    simplify (Bind   b) = Bind   <$> simplify b
    simplify  NoBody	= return NoBody

instance Simplify DisplayForm where
  simplify (Display n ps v) = Display n <$> simplify ps <*> return v


---------------------------------------------------------------------------
-- * Normalisation
---------------------------------------------------------------------------

class Normalise t where
    normalise :: t -> TCM t

instance Normalise Sort where
    normalise s = do
      s <- reduce s
      case s of
        DLub s1 s2 -> dLub <$> normalise s1 <*> normalise s2
        Prop       -> return s
        Type s     -> levelSort <$> normalise s
        Inf        -> return Inf

instance Normalise Type where
    normalise (El s t) = El <$> normalise s <*> normalise t

instance Normalise Term where
    normalise v =
	do  v <- reduce v
	    case v of
		Var n vs    -> Var n <$> normalise vs
		Con c vs    -> Con c <$> normalise vs
		Def f vs    -> Def f <$> normalise vs
		MetaV x vs  -> MetaV x <$> normalise vs
		Lit _	    -> return v
                Level l     -> levelTm <$> normalise l
		Lam h b	    -> Lam h <$> normalise b
		Sort s	    -> sortTm <$> normalise s
		Pi a b	    -> uncurry Pi <$> normalise (a,b)
                Shared{}    -> updateSharedTerm normalise v
                DontCare _  -> return v

instance Normalise Elim where
  normalise (Apply v) = Apply <$> normalise v
  normalise (Proj f)  = pure $ Proj f

instance Normalise Level where
  normalise (Max as) = levelMax <$> normalise as

instance Normalise PlusLevel where
  normalise l@ClosedLevel{} = return l
  normalise (Plus n l) = Plus n <$> normalise l

instance Normalise LevelAtom where
  normalise l = do
    l <- reduce l
    case l of
      MetaLevel m vs   -> MetaLevel m <$> normalise vs
      BlockedLevel m v -> BlockedLevel m <$> normalise v
      NeutralLevel v   -> NeutralLevel <$> normalise v
      UnreducedLevel{} -> __IMPOSSIBLE__    -- I hope

instance Normalise ClauseBody where
    normalise (Body   t) = Body   <$> normalise t
    normalise (Bind   b) = Bind   <$> normalise b
    normalise  NoBody	 = return NoBody

instance (Subst t, Normalise t) => Normalise (Abs t) where
    normalise a@(Abs x _) = Abs x <$> underAbstraction_ a normalise
    normalise (NoAbs x v) = NoAbs x <$> normalise v

instance Normalise t => Normalise (Arg t) where
    normalise a | isIrrelevant a = return a -- Andreas, 2012-04-02: Do not normalize irrelevant terms!?
                | otherwise                       = traverse normalise a

instance Normalise t => Normalise (Named name t) where
    normalise = traverse normalise

instance Normalise t => Normalise (Dom t) where
    normalise = traverse normalise

instance Normalise t => Normalise [t] where
    normalise = traverse normalise

instance (Normalise a, Normalise b) => Normalise (a,b) where
    normalise (x,y) = (,) <$> normalise x <*> normalise y

instance (Normalise a, Normalise b, Normalise c) => Normalise (a,b,c) where
    normalise (x,y,z) =
	do  (x,(y,z)) <- normalise (x,(y,z))
	    return (x,y,z)

instance Normalise a => Normalise (Closure a) where
    normalise cl = do
	x <- enterClosure cl normalise
	return $ cl { clValue = x }

instance (Subst a, Normalise a) => Normalise (Tele a) where
  normalise EmptyTel        = return EmptyTel
  normalise (ExtendTel a b) = uncurry ExtendTel <$> normalise (a, b)

instance Normalise ProblemConstraint where
  normalise (PConstr pid c) = PConstr pid <$> normalise c

instance Normalise Constraint where
  normalise (ValueCmp cmp t u v) = do
    (t,u,v) <- normalise (t,u,v)
    return $ ValueCmp cmp t u v
  normalise (ElimCmp cmp t v as bs) =
    ElimCmp cmp <$> normalise t <*> normalise v <*> normalise as <*> normalise bs
  normalise (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> normalise (u,v)
  normalise (TypeCmp cmp a b)     = uncurry (TypeCmp cmp) <$> normalise (a,b)
  normalise (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp) <$> normalise (tela,telb)
  normalise (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> normalise (a,b)
  normalise (Guarded c pid)       = Guarded <$> normalise c <*> pure pid
  normalise (UnBlock m)           = return $ UnBlock m
  normalise (FindInScope m cands) = FindInScope m <$> mapM normalise cands
  normalise (IsEmpty r t)         = IsEmpty r <$> normalise t

instance Normalise Bool where
  normalise = return

instance Normalise Pattern where
  normalise p = case p of
    VarP _       -> return p
    LitP _       -> return p
    ConP c mt ps -> ConP c <$> normalise mt <*> normalise ps
    DotP v       -> DotP <$> normalise v
    ProjP _      -> return p

instance Normalise DisplayForm where
  normalise (Display n ps v) = Display n <$> normalise ps <*> return v

instance (Ord k, Normalise e) => Normalise (Map k e) where
    normalise = traverse normalise

instance Normalise a => Normalise (Maybe a) where
    normalise = traverse normalise

---------------------------------------------------------------------------
-- * Full instantiation
---------------------------------------------------------------------------

-- STALE: Full instantiatiation = normalisation [ instantiate / reduce ]
-- How can we express this? We need higher order classes!

-- | @instantiateFull@ 'instantiate's metas everywhere (and recursively)
--   but does not 'reduce'.
class InstantiateFull t where
    instantiateFull :: t -> TCM t

instance InstantiateFull Name where
    instantiateFull = return

instance InstantiateFull Sort where
    instantiateFull s = do
	s <- instantiate s
	case s of
	    Type n     -> levelSort <$> instantiateFull n
	    Prop       -> return s
	    DLub s1 s2 -> dLub <$> instantiateFull s1 <*> instantiateFull s2
            Inf        -> return s

instance InstantiateFull Type where
    instantiateFull (El s t) =
      El <$> instantiateFull s <*> instantiateFull t

instance InstantiateFull Term where
    instantiateFull v = etaOnce =<< do -- Andreas, 2010-11-12 DONT ETA!! eta-reduction breaks subject reduction
-- but removing etaOnce now breaks everything
      v <- instantiate v
      case v of
          Var n vs    -> Var n <$> instantiateFull vs
          Con c vs    -> Con c <$> instantiateFull vs
          Def f vs    -> Def f <$> instantiateFull vs
          MetaV x vs  -> MetaV x <$> instantiateFull vs
          Lit _	      -> return v
          Level l     -> levelTm <$> instantiateFull l
          Lam h b     -> Lam h <$> instantiateFull b
          Sort s      -> sortTm <$> instantiateFull s
          Pi a b      -> uncurry Pi <$> instantiateFull (a,b)
          Shared{}    -> updateSharedTerm instantiateFull v
          DontCare v  -> dontCare <$> instantiateFull v

instance InstantiateFull Level where
  instantiateFull (Max as) = levelMax <$> instantiateFull as

instance InstantiateFull PlusLevel where
  instantiateFull l@ClosedLevel{} = return l
  instantiateFull (Plus n l) = Plus n <$> instantiateFull l

instance InstantiateFull LevelAtom where
  instantiateFull l = case l of
    MetaLevel m vs -> do
      v <- instantiateFull (MetaV m vs)
      case ignoreSharing v of
        MetaV m vs -> return $ MetaLevel m vs
        _          -> return $ UnreducedLevel v
    NeutralLevel v -> NeutralLevel <$> instantiateFull v
    BlockedLevel m v ->
      ifM (isInstantiatedMeta m)
          (UnreducedLevel <$> instantiateFull v)
          (BlockedLevel m <$> instantiateFull v)
    UnreducedLevel v -> UnreducedLevel <$> instantiateFull v

instance InstantiateFull Bool where
    instantiateFull = return

instance InstantiateFull Pattern where
    instantiateFull v@VarP{}       = return v
    instantiateFull (DotP t)       = DotP <$> instantiateFull t
    instantiateFull (ConP n mt ps) = ConP n <$> instantiateFull mt <*> instantiateFull ps
    instantiateFull l@LitP{}       = return l
    instantiateFull p@ProjP{}      = return p

instance InstantiateFull ClauseBody where
    instantiateFull (Body   t) = Body   <$> instantiateFull t
    instantiateFull (Bind   b) = Bind   <$> instantiateFull b
    instantiateFull  NoBody    = return NoBody

instance (Subst t, InstantiateFull t) => InstantiateFull (Abs t) where
    instantiateFull a@(Abs x _) = Abs x <$> underAbstraction_ a instantiateFull
    instantiateFull (NoAbs x a) = NoAbs x <$> instantiateFull a

instance InstantiateFull t => InstantiateFull (Arg t) where
    instantiateFull = traverse instantiateFull

instance InstantiateFull t => InstantiateFull (Named name t) where
    instantiateFull = traverse instantiateFull

instance InstantiateFull t => InstantiateFull (Dom t) where
    instantiateFull = traverse instantiateFull

instance InstantiateFull t => InstantiateFull [t] where
    instantiateFull = traverse instantiateFull

instance (InstantiateFull a, InstantiateFull b) => InstantiateFull (a,b) where
    instantiateFull (x,y) = (,) <$> instantiateFull x <*> instantiateFull y

instance (InstantiateFull a, InstantiateFull b, InstantiateFull c) => InstantiateFull (a,b,c) where
    instantiateFull (x,y,z) =
	do  (x,(y,z)) <- instantiateFull (x,(y,z))
	    return (x,y,z)

instance InstantiateFull a => InstantiateFull (Closure a) where
    instantiateFull cl = do
	x <- enterClosure cl instantiateFull
	return $ cl { clValue = x }

instance InstantiateFull ProblemConstraint where
  instantiateFull (PConstr p c) = PConstr p <$> instantiateFull c

instance InstantiateFull Constraint where
  instantiateFull c = case c of
    ValueCmp cmp t u v -> do
      (t,u,v) <- instantiateFull (t,u,v)
      return $ ValueCmp cmp t u v
    ElimCmp cmp t v as bs ->
      ElimCmp cmp <$> instantiateFull t <*> instantiateFull v <*> instantiateFull as <*> instantiateFull bs
    LevelCmp cmp u v    -> uncurry (LevelCmp cmp) <$> instantiateFull (u,v)
    TypeCmp cmp a b     -> uncurry (TypeCmp cmp) <$> instantiateFull (a,b)
    TelCmp a b cmp tela telb -> uncurry (TelCmp a b cmp) <$> instantiateFull (tela,telb)
    SortCmp cmp a b     -> uncurry (SortCmp cmp) <$> instantiateFull (a,b)
    Guarded c pid       -> Guarded <$> instantiateFull c <*> pure pid
    UnBlock m           -> return $ UnBlock m
    FindInScope m cands -> FindInScope m <$> mapM instantiateFull cands
    IsEmpty r t         -> IsEmpty r <$> instantiateFull t

instance InstantiateFull Elim where
  instantiateFull (Apply v) = Apply <$> instantiateFull v
  instantiateFull (Proj f)  = pure $ Proj f

instance (Ord k, InstantiateFull e) => InstantiateFull (Map k e) where
    instantiateFull = traverse instantiateFull

instance (Eq k, Hashable k, InstantiateFull e) => InstantiateFull (HashMap k e) where
    instantiateFull = traverse instantiateFull

instance InstantiateFull ModuleName where
    instantiateFull = return

instance InstantiateFull Scope where
    instantiateFull = return

instance InstantiateFull Signature where
  instantiateFull (Sig a b) = uncurry Sig <$> instantiateFull (a, b)

instance InstantiateFull Section where
  instantiateFull (Section tel n) = flip Section n <$> instantiateFull tel

instance (Subst a, InstantiateFull a) => InstantiateFull (Tele a) where
  instantiateFull EmptyTel = return EmptyTel
  instantiateFull (ExtendTel a b) = uncurry ExtendTel <$> instantiateFull (a, b)

instance InstantiateFull Char where
    instantiateFull = return

instance InstantiateFull Definition where
    instantiateFull (Defn rel x t pol occ df i c d) = do
      (t, (df, d)) <- instantiateFull (t, (df, d))
      return $ Defn rel x t pol occ df i c d

instance InstantiateFull a => InstantiateFull (Open a) where
  instantiateFull (OpenThing n a) = OpenThing n <$> instantiateFull a

instance InstantiateFull DisplayForm where
  instantiateFull (Display n ps v) = uncurry (Display n) <$> instantiateFull (ps, v)

instance InstantiateFull DisplayTerm where
  instantiateFull (DTerm v)	   = DTerm <$> instantiateFull v
  instantiateFull (DDot  v)	   = DDot  <$> instantiateFull v
  instantiateFull (DCon c vs)	   = DCon c <$> instantiateFull vs
  instantiateFull (DDef c vs)	   = DDef c <$> instantiateFull vs
  instantiateFull (DWithApp vs ws) = uncurry DWithApp <$> instantiateFull (vs, ws)

instance InstantiateFull Defn where
    instantiateFull d = case d of
      Axiom{} -> return d
      Function{ funClauses = cs, funCompiled = cc, funInv = inv } -> do
        (cs, cc, inv) <- instantiateFull (cs, cc, inv)
        return $ d { funClauses = cs, funCompiled = cc, funInv = inv }
      Datatype{ dataSort = s, dataClause = cl } -> do
	s  <- instantiateFull s
	cl <- instantiateFull cl
	return $ d { dataSort = s, dataClause = cl }
      Record{ recConType = t, recClause = cl, recTel = tel } -> do
        t   <- instantiateFull t
        cl  <- instantiateFull cl
        tel <- instantiateFull tel
        return $ d { recConType = t, recClause = cl, recTel = tel }
      Constructor{} -> return d
      Primitive{ primClauses = cs } -> do
        cs <- instantiateFull cs
        return $ d { primClauses = cs }

instance InstantiateFull FunctionInverse where
  instantiateFull NotInjective = return NotInjective
  instantiateFull (Inverse inv) = Inverse <$> instantiateFull inv

instance InstantiateFull a => InstantiateFull (WithArity a) where
  instantiateFull (WithArity n a) = WithArity n <$> instantiateFull a

instance InstantiateFull a => InstantiateFull (Case a) where
  instantiateFull (Branches cs ls m) =
    Branches <$> instantiateFull cs
             <*> instantiateFull ls
             <*> instantiateFull m

instance InstantiateFull CompiledClauses where
  instantiateFull Fail        = return Fail
  instantiateFull (Done m t)  = Done m <$> instantiateFull t
  instantiateFull (Case n bs) = Case n <$> instantiateFull bs

instance InstantiateFull Clause where
    instantiateFull (Clause r tel perm ps b t) =
       Clause r <$> instantiateFull tel
       <*> return perm
       <*> instantiateFull ps
       <*> instantiateFull b
       <*> instantiateFull t

instance InstantiateFull Interface where
    instantiateFull (Interface h ms mod scope inside
                               sig b hsImports highlighting pragmas patsyns) =
	Interface h ms mod scope inside
	    <$> instantiateFull sig
	    <*> instantiateFull b
            <*> return hsImports
            <*> return highlighting
            <*> return pragmas
            <*> return patsyns

instance InstantiateFull a => InstantiateFull (Builtin a) where
    instantiateFull (Builtin t) = Builtin <$> instantiateFull t
    instantiateFull (Prim x)	= Prim <$> instantiateFull x

instance InstantiateFull QName where
  instantiateFull = return

instance InstantiateFull a => InstantiateFull (Maybe a) where
  instantiateFull = mapM instantiateFull


{- DUPLICATE of Telescope.telView

-- | @telViewM t@ is like @telView' t@, but it reduces @t@ to expose
--   function type constructors.
telViewM :: Type -> TCM TelView
telViewM t = do
  t <- reduce t -- also instantiates meta if in head position
  case ignoreSharing $ unEl t of
    Pi a b -> absV a (absName b) <$> telViewM (absBody b)
    _      -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t
-}
