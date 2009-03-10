{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Reduce where

import Prelude hiding (mapM)
import Control.Monad.State hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Applicative
import Data.List as List hiding (sort)
import Data.Map as Map
import Data.Generics
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

import {-# SOURCE #-} Agda.TypeChecking.Patterns.Match

import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Instantiate something.
--   Results in an open meta variable or a non meta.
--   Doesn't do any reduction, and preserves blocking tags (when blocking meta
--   is uninstantiated).
class Instantiate t where
    instantiate :: MonadTCM tcm => t -> tcm t

instance Instantiate Term where
    instantiate t@(MetaV x args) =
	do  mi <- mvInstantiation <$> lookupMeta x
	    case mi of
		InstV a                        -> instantiate $ a `apply` args
		Open                           -> return t
		BlockedConst _                 -> return t
                PostponedTypeCheckingProblem _ -> return t
		InstS _                        -> __IMPOSSIBLE__
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
    instantiate (El s t) = El s <$> instantiate t

instance Instantiate Sort where
    instantiate s = case s of
	MetaS x -> do
	    mi <- mvInstantiation <$> lookupMeta x
	    case mi of
		InstS s'                       -> instantiate s'
		Open                           -> return s
		InstV{}                        -> __IMPOSSIBLE__
		BlockedConst{}                 -> __IMPOSSIBLE__
                PostponedTypeCheckingProblem{} -> __IMPOSSIBLE__
	Type _	  -> return s
	Prop	  -> return s
	Suc s	  -> sSuc <$> instantiate s
	Lub s1 s2 -> sLub <$> instantiate s1 <*> instantiate s2

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

instance Instantiate Constraint where
    instantiate (ValueCmp cmp t u v) =
	do  (t,u,v) <- instantiate (t,u,v)
	    return $ ValueCmp cmp t u v
    instantiate (TypeCmp cmp a b) = uncurry (TypeCmp cmp) <$> instantiate (a,b)
    instantiate (SortCmp cmp a b) = uncurry (SortCmp cmp) <$> instantiate (a,b)
    instantiate (Guarded c cs)    = uncurry Guarded <$> instantiate (c,cs)
    instantiate (UnBlock m)       = return $ UnBlock m
    instantiate (IsEmpty t)       = IsEmpty <$> instantiate t

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
    reduce s =
	{-# SCC "reduce<Sort>" #-}
	do  s <- instantiate s
	    case s of
		Suc s'	  -> sSuc <$> reduce s'
		Lub s1 s2 -> sLub <$> reduce s1 <*> reduce s2
		Prop	  -> return s
		Type _	  -> return s
		MetaS _   -> return s

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
		Def df@(Delayed False f) args ->
                  unfoldDefinition reduceB (Def df []) f args
		Def (Delayed True f) args -> return $ notBlocked v
		Con c args -> do
                    ind <- whatInduction c
                    -- Constructors can reduce when they come from an
                    -- instantiated module.
		    v <- unfoldDefinition __IMPOSSIBLE__ (Con c []) c args
		    traverse reduceNat v
		Sort s	   -> fmap Sort <$> reduceB s
		Pi _ _	   -> return $ notBlocked v
		Fun _ _    -> return $ notBlocked v
		Lit _	   -> return $ notBlocked v
		Var _ _    -> return $ notBlocked v
		Lam _ _    -> return $ notBlocked v
	where
	    reduceNat v@(Con c []) = do
		mz <- getBuiltin' builtinZero
		case mz of
		    Just (Con z []) | c == z -> return $ Lit $ LitInt (getRange c) 0
		    _			     -> return v
	    reduceNat v@(Con c [Arg NotHidden w]) = do
		ms <- getBuiltin' builtinSuc
		case ms of
		    Just (Con s []) | c == s -> do
			w <- reduce w
			case w of
			    Lit (LitInt r n) -> return $ Lit $ LitInt (fuseRange c r) $ n + 1
			    _		     -> return $ Con c [Arg NotHidden w]
		    _	-> return v
	    reduceNat v = return v

unfoldDefinition :: MonadTCM tcm => (Term -> tcm (Blocked Term)) ->
  Term -> QName -> Args -> tcm (Blocked Term)
unfoldDefinition keepGoing v0 f args =
    {-# SCC "reduceDef" #-}
    do  info      <- getConstInfo f
        case theDef info of
            Constructor{conSrcCon = c} ->
              return $ notBlocked $ Con (c `withRangeOf` f) args
            Primitive ConcreteDef x cls -> do
                pf <- getPrimitive x
                reducePrimitive x v0 f args pf cls
            _  -> reduceNormal v0 f args $ defClauses info
  where
    reducePrimitive x v0 f args pf cls
        | n < ar    = return $ notBlocked $ v0 `apply` args -- not fully applied
        | otherwise = do
            let (args1,args2) = genericSplitAt ar args
            r <- def args1
            case r of
                NoReduction args1' -> reduceNormal v0 f (args1' ++ args2) cls
                YesReduction v	   -> keepGoing $ v `apply` args2
        where
            n	= genericLength args
            ar  = primFunArity pf
            def = primFunImplementation pf

    reduceNormal v0 f args def = do
        case def of
            [] -> return $ notBlocked $ v0 `apply` args -- no definition for head
            cls@(Clause{ clausePats = ps } : _)
                | length ps <= length args ->
                    do  let (args1,args2) = splitAt (length ps) args 
                        ev <- appDef v0 cls args1
                        case ev of
                            NoReduction  v -> return    $ v `apply` args2
                            YesReduction v -> keepGoing $ v `apply` args2
                | otherwise	-> return $ notBlocked $ v0 `apply` args -- partial application

    -- Apply a defined function to it's arguments.
    --   The original term is the first argument applied to the third.
    appDef :: MonadTCM tcm => Term -> [Clause] -> Args -> tcm (Reduced (Blocked Term) Term)
    appDef v cls args = goCls cls args where

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
        app (arg : args) (Bind (Abs _ body)) = app args $ subst arg body -- CBN
        app (_   : args) (NoBind body)	     = app args body
        app  _		  NoBody	     = __IMPOSSIBLE__
        app (_ : _)	 (Body _)	     = __IMPOSSIBLE__
        app []		 (Bind _)	     = __IMPOSSIBLE__
        app []		 (NoBind _)	     = __IMPOSSIBLE__


instance Reduce a => Reduce (Closure a) where
    reduce cl = do
	x <- enterClosure cl reduce
	return $ cl { clValue = x }

instance Reduce Constraint where
    reduce (ValueCmp cmp t u v) =
	do  (t,u,v) <- reduce (t,u,v)
	    return $ ValueCmp cmp t u v
    reduce (TypeCmp cmp a b) = uncurry (TypeCmp cmp) <$> reduce (a,b)
    reduce (SortCmp cmp a b) = uncurry (SortCmp cmp) <$> reduce (a,b)
    reduce (Guarded c cs)    = uncurry Guarded <$> reduce (c,cs)
    reduce (UnBlock m)       = return $ UnBlock m
    reduce (IsEmpty t)       = IsEmpty <$> reduce t

instance (Ord k, Reduce e) => Reduce (Map k e) where
    reduce = traverse reduce

---------------------------------------------------------------------------
-- * Normalisation
---------------------------------------------------------------------------

class Normalise t where
    normalise :: MonadTCM tcm => t -> tcm t

instance Normalise Sort where
    normalise = reduce

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

instance Normalise Constraint where
    normalise (ValueCmp cmp t u v) =
	do  (t,u,v) <- normalise (t,u,v)
	    return $ ValueCmp cmp t u v
    normalise (TypeCmp cmp a b) = uncurry (TypeCmp cmp) <$> normalise (a,b)
    normalise (SortCmp cmp a b) = uncurry (SortCmp cmp) <$> normalise (a,b)
    normalise (Guarded c cs)    = uncurry Guarded <$> normalise (c,cs)
    normalise (UnBlock m)       = return $ UnBlock m
    normalise (IsEmpty t)       = IsEmpty <$> normalise t

instance Normalise Pattern where
  normalise p = case p of
    VarP _    -> return p
    LitP _    -> return p
    ConP c ps -> ConP c <$> normalise ps
    DotP v    -> DotP <$> normalise v

instance Normalise DisplayForm where
  normalise (Display n ps v) = Display n <$> normalise ps <*> return v

instance (Ord k, Normalise e) => Normalise (Map k e) where
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
	    MetaS x   -> return $ MetaS x
	    Type _    -> return s
	    Prop      -> return s
	    Suc s     -> sSuc <$> instantiateFull s
	    Lub s1 s2 -> sLub <$> instantiateFull s1 <*> instantiateFull s2

instance InstantiateFull Type where
    instantiateFull (El s t) = El <$> instantiateFull s <*> instantiateFull t

instance InstantiateFull Term where
    instantiateFull v =
	do  v <- instantiate v
	    case v of
		Var n vs   -> Var n <$> instantiateFull vs
		Con c vs   -> Con c <$> instantiateFull vs
		Def f vs   -> Def f <$> instantiateFull vs
		MetaV x vs -> MetaV x <$> instantiateFull vs
		Lit _	   -> return v
		Lam h b    -> Lam h <$> instantiateFull b
		Sort s	   -> Sort <$> instantiateFull s
		Pi a b	   -> uncurry Pi <$> instantiateFull (a,b)
		Fun a b    -> uncurry Fun <$> instantiateFull (a,b)

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
    instantiateFull (ValueCmp cmp t u v) =
	do  (t,u,v) <- instantiateFull (t,u,v)
	    return $ ValueCmp cmp t u v
    instantiateFull (TypeCmp cmp a b) = uncurry (TypeCmp cmp) <$> instantiateFull (a,b)
    instantiateFull (SortCmp cmp a b) = uncurry (SortCmp cmp) <$> instantiateFull (a,b)
    instantiateFull (Guarded c cs)    = uncurry Guarded <$> instantiateFull (c,cs)
    instantiateFull (UnBlock m)       = return $ UnBlock m
    instantiateFull (IsEmpty t)       = IsEmpty <$> instantiateFull t

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

instance InstantiateFull Telescope where
  instantiateFull EmptyTel = return EmptyTel
  instantiateFull (ExtendTel a b) = uncurry ExtendTel <$> instantiateFull (a, b)

instance InstantiateFull Char where
    instantiateFull = return

instance InstantiateFull Definition where
    instantiateFull (Defn x t df i d) = do
      (t, (df, d)) <- instantiateFull (t, (df, d))
      return $ Defn x t df i d

instance InstantiateFull a => InstantiateFull (Open a) where
  instantiateFull (OpenThing n a) = OpenThing n <$> instantiateFull a

instance InstantiateFull DisplayForm where
  instantiateFull (Display n ps v) = uncurry (Display n) <$> instantiateFull (ps, v)

instance InstantiateFull DisplayTerm where
  instantiateFull (DTerm v)	   = DTerm <$> instantiateFull v
  instantiateFull (DWithApp vs ws) = uncurry DWithApp <$> instantiateFull (vs, ws)

instance InstantiateFull Defn where
    instantiateFull d = case d of
      Axiom{} -> return d
      Function{ funClauses = cs } -> do
        cs <- instantiateFull cs
        return $ d { funClauses = cs }
      Datatype{ dataSort = s, dataClause = cl } -> do
	s  <- instantiateFull s
	cl <- instantiateFull cl
	return $ d { dataSort = s, dataClause = cl }
      Record{ recSort = s, recClause = cl, recTel = tel } -> do
        s   <- instantiateFull s
        cl  <- instantiateFull cl
        tel <- instantiateFull tel
        return $ d { recSort = s, recClause = cl, recTel = tel }
      Constructor{} -> return d
      Primitive{ primClauses = cs } -> do
        cs <- instantiateFull cs
        return $ d { primClauses = cs }

instance InstantiateFull Clause where
    instantiateFull (Clause r tel perm ps b) =
       Clause r <$> instantiateFull tel
       <*> return perm
       <*> return ps
       <*> instantiateFull b

instance InstantiateFull Interface where
    instantiateFull (Interface ms mod scope sig b hsImports highlighting) =
	Interface ms mod scope
	    <$> instantiateFull sig
	    <*> instantiateFull b
            <*> return hsImports
            <*> return highlighting

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
