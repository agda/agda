{-# LANGUAGE CPP, PatternGuards,
             TypeSynonymInstances, FlexibleInstances #-}

module Agda.TypeChecking.Reduce where

import Prelude hiding (mapM)
import Control.Monad.State hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Monad.Error hiding (mapM)
import Control.Applicative
import Data.List as List hiding (sort)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Traversable
import Data.Hashable

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Base (Scope)
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.CompiledClause
import {-# SOURCE #-} Agda.TypeChecking.Pretty

import {-# SOURCE #-} Agda.TypeChecking.Level
import {-# SOURCE #-} Agda.TypeChecking.Patterns.Match
import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Match

import Agda.Utils.Monad
import Agda.Utils.HashMap (HashMap)
import qualified Agda.Utils.HashMap as HMap

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
  instantiate t@(MetaV x args) = do
    mi <- mvInstantiation <$> lookupMeta x
    case mi of
      InstV a                        -> instantiate $ a `apply` args
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
      ifM (not <$> hasUniversePolymorphism) (red s)
      $ red =<< instantiateFull s
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
    reduce a@(Arg h Irrelevant t) = return a  -- Don't reduce irr. args!?
    reduce a                      = traverse reduce a

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
      MetaV x args -> return $ notBlocked v
      Def f args   -> unfoldDefinition False reduceB (Def f []) f args
      Con c args   -> do
          -- Constructors can reduce when they come from an
          -- instantiated module.
          v <- unfoldDefinition False reduceB (Con c []) c args
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
      reduceNat v@(Con c [Arg NotHidden Relevant w]) = do
        ms  <- fmap ignoreSharing <$> getBuiltin' builtinSuc
        case v of
          _ | Just (Con c []) == ms -> inc <$> reduce w
          _	                    -> return v
          where
            inc w = case ignoreSharing w of
              Lit (LitInt r n) -> Lit (LitInt (fuseRange c r) $ n + 1)
              _                -> Con c [Arg NotHidden Relevant w]
      reduceNat v = return v

-- | If the first argument is 'True', then a single delayed clause may
-- be unfolded.
unfoldDefinition ::
  Bool -> (Term -> TCM (Blocked Term)) ->
  Term -> QName -> Args -> TCM (Blocked Term)
unfoldDefinition unfoldDelayed keepGoing v0 f args =
  {-# SCC "reduceDef" #-} do
  info <- getConstInfo f
  case theDef info of
    Constructor{conSrcCon = c} ->
      return $ notBlocked $ Con (c `withRangeOf` f) args
    Primitive{primAbstr = ConcreteDef, primName = x, primClauses = cls} -> do
      pf <- getPrimitive x
      reducePrimitive x v0 f args pf (defDelayed info)
                      (maybe [] id cls) (defCompiled info)
    _  -> reduceNormal v0 f (map notReduced args) (defDelayed info)
                       (defClauses info) (defCompiled info)
  where
    reducePrimitive x v0 f args pf delayed cls mcc
        | n < ar    = return $ notBlocked $ v0 `apply` args -- not fully applied
        | otherwise = {-# SCC "reducePrimitive" #-} do
            let (args1,args2) = genericSplitAt ar args
            r <- def args1
            case r of
              NoReduction args1' ->
                if null cls then
                  return $ apply (Def f []) <$> traverse id (map mredToBlocked args1' ++ map notBlocked args2)
                else
                  reduceNormal v0 f (args1' ++
                                     map notReduced args2)
                               delayed cls mcc
              YesReduction v ->
                keepGoing $ v `apply` args2
        where
            n	= genericLength args
            ar  = primFunArity pf
            def = primFunImplementation pf
            mredToBlocked :: MaybeReduced a -> Blocked a
            mredToBlocked (MaybeRed NotReduced  x) = notBlocked x
            mredToBlocked (MaybeRed (Reduced b) x) = x <$ b

    reduceNormal :: Term -> QName -> [MaybeReduced (Arg Term)] -> Delayed -> [Clause] -> Maybe CompiledClauses -> TCM (Blocked Term)
    reduceNormal v0 f args delayed def mcc = {-# SCC "reduceNormal" #-} do
        case def of
          _ | Delayed <- delayed,
              not unfoldDelayed -> defaultResult
          [] -> defaultResult -- no definition for head
          cls -> do
            ev <- maybe (appDef' v0 cls args)
                        (\cc -> appDef v0 cc args) mcc
            case ev of
              NoReduction v -> do
                reportSDoc "tc.reduce" 90 $ vcat
                  [ text "*** tried to reduce " <+> prettyTCM f
                  , text "    args    " <+> prettyTCM (map (unArg . ignoreReduced) args)
                  , text "    stuck on" <+> prettyTCM (ignoreBlocking v) ]
                return v
              YesReduction v -> do
                reportSDoc "tc.reduce" 90 $ vcat
                  [ text "*** reduced definition: " <+> prettyTCM f
                  ]
                reportSDoc "tc.reduce" 100 $ text "    result" <+> prettyTCM v $$
                                             text "    raw   " <+> text (show v)
                keepGoing v
      where defaultResult = return $ notBlocked $ v0 `apply` (map ignoreReduced args)

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
      delayed = (defDelayed info)
  case delayed of
    Delayed -> return $ NoReduction ()
    NotDelayed -> do
      ev <- maybe (appDef' v0 cls args)
                  (\cc -> appDef v0 cc args) mcc
      case ev of
        YesReduction t    -> return $ YesReduction t
        NoReduction args' -> return $ NoReduction ()

-- Apply a defined function to it's arguments.
--   The original term is the first argument applied to the third.
appDef :: Term -> CompiledClauses -> MaybeReducedArgs -> TCM (Reduced (Blocked Term) Term)
appDef v cc args = liftTCM $ do
  r <- matchCompiled cc args
  case r of
    YesReduction t    -> return $ YesReduction t
    NoReduction args' -> return $ NoReduction $ fmap (apply v) args'

appDef' :: Term -> [Clause] -> MaybeReducedArgs -> TCM (Reduced (Blocked Term) Term)
appDef' _ [] _ = {- ' -} __IMPOSSIBLE__
appDef' v cls@(Clause {clausePats = ps} : _) args
  | m < n     = return $ NoReduction $ notBlocked $ v `apply` map ignoreReduced args
  | otherwise = do
    let (args0, args1) = splitAt n args
    r <- goCls cls (map ignoreReduced args0)
    case r of
      YesReduction u -> return $ YesReduction $ u `apply` map ignoreReduced args1
      NoReduction v  -> return $ NoReduction $ (`apply` map ignoreReduced args1) <$> v
  where

    n = genericLength ps
    m = genericLength args

    goCls :: [Clause] -> Args -> TCM (Reduced (Blocked Term) Term)
    goCls [] args = typeError $ IncompletePatternMatching v args
    goCls (cl@(Clause { clausePats = pats
                      , clauseBody = body }) : cls) args = do
        (m, args) <- matchPatterns pats args
        case m of
            No		  -> goCls cls args
            DontKnow Nothing  -> return $ NoReduction $ notBlocked $ v `apply` args
            DontKnow (Just m) -> return $ NoReduction $ blocked m $ v `apply` args
            Yes args'
              | hasBody body  -> return $ YesReduction (
                  -- TODO: let matchPatterns also return the reduced forms
                  -- of the original arguments!
                  app args' body)
              | otherwise	  -> return $ NoReduction $ notBlocked $ v `apply` args

    hasBody (Body _) = True
    hasBody NoBody   = False
    hasBody (Bind b) = hasBody (unAbs b)

    app []		 (Body v') = v'
    app (arg : args) (Bind b)  = app args $ absApp b arg -- CBN
    app  _		  NoBody   = __IMPOSSIBLE__
    app (_ : _)	 (Body _)  = __IMPOSSIBLE__
    app []		 (Bind _)  = __IMPOSSIBLE__


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
    normalise a@(Arg h Irrelevant t) = return a -- Andreas, 2012-04-02: Do not normalize irrelevant terms!?
    normalise a = traverse normalise a

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

instance Normalise Pattern where
  normalise p = case p of
    VarP _       -> return p
    LitP _       -> return p
    ConP c mt ps -> ConP c <$> normalise mt <*> normalise ps
    DotP v       -> DotP <$> normalise v

instance Normalise DisplayForm where
  normalise (Display n ps v) = Display n <$> normalise ps <*> return v

instance (Ord k, Normalise e) => Normalise (Map k e) where
    normalise = traverse normalise

instance Normalise a => Normalise (Maybe a) where
    normalise = traverse normalise

---------------------------------------------------------------------------
-- * Full instantiation
---------------------------------------------------------------------------

-- Full instantiatiation = normalisation [ instantiate / reduce ]
-- How can we express this? We need higher order classes!

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
          DontCare v  -> DontCare <$> instantiateFull v

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

instance InstantiateFull Pattern where
    instantiateFull v@VarP{}       = return v
    instantiateFull (DotP t)       = DotP <$> instantiateFull t
    instantiateFull (ConP n mt ps) = ConP n <$> instantiateFull mt <*> instantiateFull ps
    instantiateFull l@LitP{}       = return l

instance InstantiateFull ClauseBody where
    instantiateFull (Body   t) = Body   <$> instantiateFull t
    instantiateFull (Bind   b) = Bind   <$> instantiateFull b
    instantiateFull  NoBody    = return NoBody

instance (Subst t, InstantiateFull t) => InstantiateFull (Abs t) where
    instantiateFull a@(Abs x _) = Abs x <$> underAbstraction_ a instantiateFull
    instantiateFull (NoAbs x a) = NoAbs x <$> instantiateFull a

instance InstantiateFull t => InstantiateFull (Arg t) where
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
    instantiateFull (Clause r tel perm ps b) =
       Clause r <$> instantiateFull tel
       <*> return perm
       <*> instantiateFull ps
       <*> instantiateFull b

instance InstantiateFull Interface where
    instantiateFull (Interface ms mod scope inside
                               sig b hsImports highlighting pragmas patsyns) =
	Interface ms mod scope inside
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
