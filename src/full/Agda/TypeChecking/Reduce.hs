{-# LANGUAGE CPP, PatternGuards, TypeSynonymInstances #-}

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

import {-# SOURCE #-} Agda.TypeChecking.Patterns.Match
import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Match

import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

traceFun :: MonadTCM tcm => String -> tcm a -> tcm a
traceFun s m = do
  reportSLn "tc.inst" 100 $ "[ " ++ s
  x <- m
  reportSLn "tc.inst" 100 $ "]"
  return x

traceFun' :: (Show a, MonadTCM tcm) => String -> tcm a -> tcm a
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
    instantiate :: MonadTCM tcm => t -> tcm t

instance Instantiate Term where
  instantiate t@(MetaV x args) = do
    mi <- mvInstantiation <$> lookupMeta x
    case mi of
      InstV a                        -> instantiate $ a `apply` args
      Open                           -> return t
      BlockedConst _                 -> return t
      PostponedTypeCheckingProblem _ -> return t
      InstS _                        -> __IMPOSSIBLE__
  instantiate (Sort s) = Sort <$> instantiate s
  instantiate t = return t

instance Instantiate a => Instantiate (Blocked a) where
  instantiate v@NotBlocked{} = return v
  instantiate v@(Blocked x u) = do
    mi <- mvInstantiation <$> lookupMeta x
    case mi of
      InstV _                        -> notBlocked <$> instantiate u
      Open                           -> return v
      BlockedConst _                 -> return v
      PostponedTypeCheckingProblem _ -> return v
      InstS _                        -> __IMPOSSIBLE__

instance Instantiate Type where
    instantiate (El s t) = El <$> instantiate s <*> instantiate t

instance Instantiate Sort where
    instantiate s = case s of
	MetaS x as -> do
	    mi <- mvInstantiation <$> lookupMeta x
	    case mi of
		InstS s'                       -> do
                  v <- instantiate (s' `apply` as)
                  case v of
                    Sort s -> return s
                    _      -> __IMPOSSIBLE__
		Open                           -> return s
		InstV{}                        -> __IMPOSSIBLE__
		BlockedConst{}                 -> __IMPOSSIBLE__
                PostponedTypeCheckingProblem{} -> __IMPOSSIBLE__
        _ -> return s

instance Instantiate t => Instantiate (Abs t) where
  instantiate = traverse instantiate

instance Instantiate t => Instantiate (Arg t) where
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
  instantiate (ArgsCmp cmp t as bs) = do
    (t, as, bs) <- instantiate (t, as, bs)
    return $ ArgsCmp cmp t as bs
  instantiate (LevelCmp cmp u v)   = uncurry (LevelCmp cmp) <$> instantiate (u,v)
  instantiate (TypeCmp cmp a b)    = uncurry (TypeCmp cmp) <$> instantiate (a,b)
  instantiate (TelCmp cmp a b)     = uncurry (TelCmp cmp)  <$> instantiate (a,b)
  instantiate (SortCmp cmp a b)    = uncurry (SortCmp cmp) <$> instantiate (a,b)
  instantiate (Guarded c cs)       = uncurry Guarded <$> instantiate (c,cs)
  instantiate (UnBlock m)          = return $ UnBlock m
  instantiate (IsEmpty t)          = IsEmpty <$> instantiate t

instance (Ord k, Instantiate e) => Instantiate (Map k e) where
    instantiate = traverse instantiate


--
-- Reduction to weak head normal form.
--

class Reduce t where
    reduce  :: MonadTCM tcm => t -> tcm t
    reduceB :: MonadTCM tcm => t -> tcm (Blocked t)

    reduce  t = ignoreBlocking <$> reduceB t
    reduceB t = notBlocked <$> reduce t

instance Reduce Type where
    reduce (El s t) = El <$> reduce s <*> reduce t
    reduceB (El s t) = do
      s <- reduce s
      t <- reduceB t
      return (El s <$> t)

instance Reduce Sort where
    reduce s = {-# SCC "reduce<Sort>" #-}
      ifM (not <$> hasUniversePolymorphism) (red sSuc sLub s)
      $ liftTCM $ do
        suc  <- do sc <- primLevelSuc
                   return $ \x -> case x of
                                    Type n -> Type (sc `apply` [Arg NotHidden Relevant n])
                                    _      -> sSuc x
          `catchError` \_ -> return sSuc
        lub <- do mx <- primLevelMax
                  return $ \x y -> case (x, y) of
                    (Type n, Type m) -> Type (mx `apply` List.map (Arg NotHidden Relevant) [n, m])
                    _                -> sLub x y
          `catchError` \_ -> return sLub
        -- need to instantiate all meta to know if we need a DLub or a Lub
        red suc lub =<< instantiateFull s
      where
        red suc lub s = do
          s <- instantiate s
          case s of
            Suc s'     -> suc <$> reduce s'
            Lub s1 s2  -> lub <$> reduce s1 <*> reduce s2
            DLub s1 s2 -> do
              s <- dLub <$> reduce s1 <*> reduce s2
              case s of
                DLub{}  -> return s
                _       -> reduce s   -- TODO: not so nice
            Prop       -> return s
            Type s'    -> Type <$> reduce s'
            MetaS m as -> MetaS m <$> reduce as
            Inf        -> return Inf

instance Reduce t => Reduce (Abs t) where
  reduce b = Abs (absName b) <$> underAbstraction_ b reduce

-- Lists are never blocked
instance Reduce t => Reduce [t] where
    reduce = traverse reduce

instance Reduce t => Reduce (Arg t) where
    reduce  = traverse reduce
    reduceB t = traverse id <$> traverse reduceB t

-- Tuples are never blocked
instance (Reduce a, Reduce b) => Reduce (a,b) where
    reduce (x,y)  = (,) <$> reduce x <*> reduce y

instance (Reduce a, Reduce b,Reduce c) => Reduce (a,b,c) where
    reduce (x,y,z) = (,,) <$> reduce x <*> reduce y <*> reduce z

instance Reduce Term where
    reduceB v =
	{-# SCC "reduce<Term>" #-}
	do  v <- instantiate v
	    case v of
		MetaV x args -> notBlocked . MetaV x <$> reduce args
		Def f args   -> unfoldDefinition False reduceB (Def f []) f args
		Con c args   -> do
                    -- Constructors can reduce when they come from an
                    -- instantiated module.
		    v <- unfoldDefinition False reduceB (Con c []) c args
		    traverse reduceNat v
		Sort s	   -> fmap Sort <$> reduceB s
		Pi _ _	   -> return $ notBlocked v
		Fun _ _    -> return $ notBlocked v
		Lit _	   -> return $ notBlocked v
		Var _ _    -> return $ notBlocked v
		Lam _ _    -> return $ notBlocked v
		DontCare   -> return $ notBlocked v
	where
            -- NOTE: reduceNat can traverse the entire term.
	    reduceNat v@(Con c []) = do
		mz  <- getBuiltin' builtinZero
                mlz <- getBuiltin' builtinLevelZero
		case v of
                  _ | Just v == mz  -> return $ Lit $ LitInt (getRange c) 0
                    | Just v == mlz -> return $ Lit $ LitLevel (getRange c) 0
		  _		    -> return v
	    reduceNat v@(Con c [Arg NotHidden Relevant w]) = do
		ms  <- getBuiltin' builtinSuc
                mls <- getBuiltin' builtinLevelSuc
		case v of
                  _ | Just (Con c []) == ms ||
                      Just (Con c []) == mls -> inc <$> reduce w
		  _	                     -> return v
                  where
                    inc w = case w of
                      Lit (LitInt r n) -> Lit (LitInt (fuseRange c r) $ n + 1)
                      Lit (LitLevel r n) -> Lit (LitLevel (fuseRange c r) $ n + 1)
                      _                  -> Con c [Arg NotHidden Relevant w]
	    reduceNat v = return v

-- | If the first argument is 'True', then a single delayed clause may
-- be unfolded.
unfoldDefinition :: MonadTCM tcm =>
  Bool -> (Term -> tcm (Blocked Term)) ->
  Term -> QName -> Args -> tcm (Blocked Term)
unfoldDefinition unfoldDelayed keepGoing v0 f args =
  {-# SCC "reduceDef" #-} do
  info <- getConstInfo f
  case theDef info of
    Constructor{conSrcCon = c} ->
      return $ notBlocked $ Con (c `withRangeOf` f) args
    Primitive{primAbstr = ConcreteDef, primName = x, primClauses = cls} -> do
      pf <- getPrimitive x
      reducePrimitive x v0 f args pf (defDelayed info)
                      (maybe [] (List.map translatedClause) cls)
                      (defCompiled info)
    _  -> reduceNormal v0 f (map notReduced args) (defDelayed info)
                       (List.map translatedClause $ defClauses info)
                       (defCompiled info)
  where
    reducePrimitive x v0 f args pf delayed cls mcc
        | n < ar    = return $ notBlocked $ v0 `apply` args -- not fully applied
        | otherwise = {-# SCC "reducePrimitive" #-} do
            let (args1,args2) = genericSplitAt ar args
            r <- def args1
            case r of
              NoReduction args1' ->
                reduceNormal v0 f (args1' ++
                                   map notReduced args2)
                             delayed cls mcc
              YesReduction v ->
                keepGoing $ v `apply` args2
        where
            n	= genericLength args
            ar  = primFunArity pf
            def = primFunImplementation pf

    reduceNormal v0 f args delayed def mcc = {-# SCC "reduceNormal" #-} do
        case def of
          _ | Delayed <- delayed,
              not unfoldDelayed -> defaultResult
          [] -> defaultResult -- no definition for head
          cls@(Clause{ clausePats = ps } : _)
            | length ps <= length args -> do
                let (args1,args2') = splitAt (length ps) args
                    args2 = map ignoreReduced args2'
                ev <- maybe (appDef' v0 cls args1)
                            (\cc -> appDef v0 cc args1) mcc
                case ev of
                  NoReduction  v -> return    $ v `apply` args2
                  YesReduction v -> keepGoing $ v `apply` args2
            | otherwise	-> defaultResult -- partial application
      where defaultResult = return $ notBlocked $ v0 `apply` (map ignoreReduced args)

    -- Apply a defined function to it's arguments.
    --   The original term is the first argument applied to the third.
    appDef :: MonadTCM tcm => Term -> CompiledClauses -> MaybeReducedArgs -> tcm (Reduced (Blocked Term) Term)
    appDef v cc args = liftTCM $ do
      r <- matchCompiled cc args
      case r of
        YesReduction t    -> return $ YesReduction t
        NoReduction args' -> return $ NoReduction $ fmap (apply v) args'

    appDef' :: MonadTCM tcm => Term -> [Clause] -> MaybeReducedArgs -> tcm (Reduced (Blocked Term) Term)
    appDef' v cls args = {-# SCC "appDef" #-} do
      goCls cls (map ignoreReduced args) where

        goCls :: MonadTCM tcm => [Clause] -> Args -> tcm (Reduced (Blocked Term) Term)
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

        hasBody (Body _)	 = True
        hasBody NoBody		 = False
        hasBody (Bind (Abs _ b)) = hasBody b
        hasBody (NoBind b)	 = hasBody b

        app []		 (Body v')	     = v'
        app (arg : args) (Bind (Abs _ body)) = {-# SCC "instRHS" #-} app args $ subst arg body -- CBN
        app (_   : args) (NoBind body)	     = app args body
        app  _		  NoBody	     = __IMPOSSIBLE__
        app (_ : _)	 (Body _)	     = __IMPOSSIBLE__
        app []		 (Bind _)	     = __IMPOSSIBLE__
        app []		 (NoBind _)	     = __IMPOSSIBLE__


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
  reduce (ArgsCmp cmp t us vs) = do
    (t,us,vs) <- reduce (t,us,vs)
    return $ ArgsCmp cmp t us vs
  reduce (LevelCmp cmp u v)   = uncurry (LevelCmp cmp) <$> reduce (u,v)
  reduce (TypeCmp cmp a b)    = uncurry (TypeCmp cmp) <$> reduce (a,b)
  reduce (TelCmp  cmp a b)    = uncurry (TelCmp cmp)  <$> reduce (a,b)
  reduce (SortCmp cmp a b)    = uncurry (SortCmp cmp) <$> reduce (a,b)
  reduce (Guarded c cs)       = uncurry Guarded <$> reduce (c,cs)
  reduce (UnBlock m)          = return $ UnBlock m
  reduce (IsEmpty t)          = IsEmpty <$> reduce t

instance (Ord k, Reduce e) => Reduce (Map k e) where
    reduce = traverse reduce

---------------------------------------------------------------------------
-- * Normalisation
---------------------------------------------------------------------------

class Normalise t where
    normalise :: MonadTCM tcm => t -> tcm t

instance Normalise Sort where
    normalise s = do
      s <- reduce s
      case s of
        Suc s'     -> sSuc <$> normalise s'
        Lub s1 s2  -> sLub <$> normalise s1 <*> normalise s2
        DLub s1 s2 -> dLub <$> normalise s1 <*> normalise s2
        Prop       -> return s
        Type s'    -> Type <$> normalise s'
        MetaS m as -> MetaS m <$> normalise as
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
		Lam h b	    -> Lam h <$> normalise b
		Sort s	    -> Sort <$> normalise s
		Pi a b	    -> uncurry Pi <$> normalise (a,b)
		Fun a b     -> uncurry Fun <$> normalise (a,b)
                DontCare    -> return v

instance Normalise ClauseBody where
    normalise (Body   t) = Body   <$> normalise t
    normalise (Bind   b) = Bind   <$> normalise b
    normalise (NoBind b) = NoBind <$> normalise b
    normalise  NoBody	 = return NoBody

instance Normalise t => Normalise (Abs t) where
    normalise a = Abs (absName a) <$> underAbstraction_ a normalise

instance Normalise t => Normalise (Arg t) where
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

instance Normalise a => Normalise (Tele a) where
  normalise EmptyTel        = return EmptyTel
  normalise (ExtendTel a b) = uncurry ExtendTel <$> normalise (a, b)

instance Normalise Constraint where
  normalise (ValueCmp cmp t u v) = do
    (t,u,v) <- normalise (t,u,v)
    return $ ValueCmp cmp t u v
  normalise (ArgsCmp cmp t u v) = do
    (t,u,v) <- normalise (t,u,v)
    return $ ArgsCmp cmp t u v
  normalise (LevelCmp cmp u v)   = uncurry (LevelCmp cmp) <$> normalise (u,v)
  normalise (TypeCmp cmp a b)    = uncurry (TypeCmp cmp) <$> normalise (a,b)
  normalise (TelCmp cmp a b)     = uncurry (TelCmp cmp)  <$> normalise (a,b)
  normalise (SortCmp cmp a b)    = uncurry (SortCmp cmp) <$> normalise (a,b)
  normalise (Guarded c cs)       = uncurry Guarded <$> normalise (c,cs)
  normalise (UnBlock m)          = return $ UnBlock m
  normalise (IsEmpty t)          = IsEmpty <$> normalise t

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
    instantiateFull :: MonadTCM tcm => t -> tcm t

instance InstantiateFull Name where
    instantiateFull = return

instance InstantiateFull Sort where
    instantiateFull s = do
	s <- instantiate s
	case s of
	    MetaS x as -> MetaS x <$> instantiateFull as
	    Type n     -> Type <$> instantiateFull n
	    Prop       -> return s
	    Suc s      -> sSuc <$> instantiateFull s
	    Lub s1 s2  -> sLub <$> instantiateFull s1 <*> instantiateFull s2
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
          Lam h b     -> Lam h <$> instantiateFull b
          Sort s      -> Sort <$> instantiateFull s
          Pi a b      -> uncurry Pi <$> instantiateFull (a,b)
          Fun a b     -> uncurry Fun <$> instantiateFull (a,b)
          DontCare    -> return v

instance InstantiateFull Pattern where
    instantiateFull v@VarP{}       = return v
    instantiateFull (DotP t)       = DotP <$> instantiateFull t
    instantiateFull (ConP n mt ps) = ConP n <$> instantiateFull mt <*> instantiateFull ps
    instantiateFull l@LitP{}       = return l

instance InstantiateFull ClauseBody where
    instantiateFull (Body   t) = Body   <$> instantiateFull t
    instantiateFull (Bind   b) = Bind   <$> instantiateFull b
    instantiateFull (NoBind b) = NoBind <$> instantiateFull b
    instantiateFull  NoBody    = return NoBody

instance InstantiateFull t => InstantiateFull (Abs t) where
    instantiateFull a = Abs (absName a) <$> underAbstraction_ a instantiateFull

instance InstantiateFull t => InstantiateFull (Arg t) where
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

instance InstantiateFull Constraint where
  instantiateFull c = case c of
    ValueCmp cmp t u v -> do
      (t,u,v) <- instantiateFull (t,u,v)
      return $ ValueCmp cmp t u v
    ArgsCmp cmp t u v -> do
      (t,u,v) <- instantiateFull (t,u,v)
      return $ ArgsCmp cmp t u v
    LevelCmp cmp u v   -> uncurry (LevelCmp cmp) <$> instantiateFull (u,v)
    TypeCmp cmp a b    -> uncurry (TypeCmp cmp) <$> instantiateFull (a,b)
    TelCmp cmp a b     -> uncurry (TelCmp cmp)  <$> instantiateFull (a,b)
    SortCmp cmp a b    -> uncurry (SortCmp cmp) <$> instantiateFull (a,b)
    Guarded c cs       -> uncurry Guarded <$> instantiateFull (c,cs)
    UnBlock m          -> return $ UnBlock m
    IsEmpty t          -> IsEmpty <$> instantiateFull t

instance (Ord k, InstantiateFull e) => InstantiateFull (Map k e) where
    instantiateFull = traverse instantiateFull

instance InstantiateFull ModuleName where
    instantiateFull = return

instance InstantiateFull Scope where
    instantiateFull = return

instance InstantiateFull Signature where
  instantiateFull (Sig a b) = uncurry Sig <$> instantiateFull (a, b)

instance InstantiateFull Section where
  instantiateFull (Section tel n) = flip Section n <$> instantiateFull tel

instance InstantiateFull a => InstantiateFull (Tele a) where
  instantiateFull EmptyTel = return EmptyTel
  instantiateFull (ExtendTel a b) = uncurry ExtendTel <$> instantiateFull (a, b)

instance InstantiateFull Char where
    instantiateFull = return

instance InstantiateFull Definition where
    instantiateFull (Defn rel x t df i d) = do
      (t, (df, d)) <- instantiateFull (t, (df, d))
      return $ Defn rel x t df i d

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

instance InstantiateFull a => InstantiateFull (Case a) where
  instantiateFull (Branches cs ls m) =
    Branches <$> instantiateFull cs
             <*> instantiateFull ls
             <*> instantiateFull m

instance InstantiateFull CompiledClauses where
  instantiateFull Fail        = return Fail
  instantiateFull (Done m t)  = Done m <$> instantiateFull t
  instantiateFull (Case n bs) = Case n <$> instantiateFull bs

instance InstantiateFull Clauses where
    instantiateFull (Clauses c tc) =
       Clauses <$> instantiateFull c <*> instantiateFull tc

instance InstantiateFull Clause where
    instantiateFull (Clause r tel perm ps b) =
       Clause r <$> instantiateFull tel
       <*> return perm
       <*> instantiateFull ps
       <*> instantiateFull b

instance InstantiateFull Interface where
    instantiateFull (Interface ms mod scope inside
                               sig b hsImports highlighting pragmas) =
	Interface ms mod scope inside
	    <$> instantiateFull sig
	    <*> instantiateFull b
            <*> return hsImports
            <*> return highlighting
            <*> return pragmas

instance InstantiateFull a => InstantiateFull (Builtin a) where
    instantiateFull (Builtin t) = Builtin <$> instantiateFull t
    instantiateFull (Prim x)	= Prim <$> instantiateFull x

instance InstantiateFull a => InstantiateFull (Maybe a) where
  instantiateFull = mapM instantiateFull

telViewM :: MonadTCM tcm => Type -> tcm TelView
telViewM t = do
  t <- reduce t
  case unEl t of
    Pi a (Abs x b) -> absV a x <$> telViewM b
    Fun a b	   -> absV a "_" <$> telViewM (raise 1 b)
    _		   -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t
