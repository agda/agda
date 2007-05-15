{-# OPTIONS -fglasgow-exts -cpp #-}

module TypeChecking.Rules.LHS where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Data.Monoid
import Data.Traversable
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Syntax.Abstract as A
import Syntax.Internal
import Syntax.Internal.Pattern
import Syntax.Common
import Syntax.Position
import Syntax.Info

import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Substitute
import TypeChecking.Implicit
import TypeChecking.Free
import TypeChecking.Conversion
import TypeChecking.Constraints

import Utils.Permutation
import Utils.Size

#include "../../undefined.h"

data DotPatternInst = DPI A.Expr Term Type
type Substitution   = [Maybe Term]
type FlexibleVars   = [Nat]

data Problem p	    = Problem [NamedArg A.Pattern] p Telescope
data Focus	    = Focus QName [NamedArg A.Pattern] OneHolePatterns QName [Arg Term] [Arg Term]
data SplitProblem   = Split (Problem ()) (Arg Focus) (Abs (Problem ()))

data SplitError	    = TooManyArguments [NamedArg A.Pattern]
		    | NothingToSplit
		    | SplitPanic String

instance Error SplitError where
  noMsg  = NothingToSplit
  strMsg = SplitPanic

instance Monoid p => Monoid (Problem p) where
  mempty = Problem [] mempty EmptyTel
  Problem ps1 qs1 tel1 `mappend` Problem ps2 qs2 tel2 =
    Problem (ps1 ++ ps2) (mappend qs1 qs2) (abstract tel1 tel2)

instance (Monad m, Error err) => Applicative (ErrorT err m) where
  pure	= return
  (<*>) = ap

instance (Error err, MonadTCM tcm) => MonadTCM (ErrorT err tcm) where
  liftTCM = lift . liftTCM

-- | Split a problem at the first constructor of datatype type. Also inserts
--   implicit patterns in the patterns before the split.
splitProblem :: Problem [Arg Pattern] -> TCM (Either SplitError SplitProblem)
splitProblem (Problem ps qs tel) = runErrorT (splitP ps (allHoles qs) tel)
  where
    splitP :: [NamedArg A.Pattern] -> [OneHolePatterns] -> Telescope -> ErrorT SplitError TCM SplitProblem
    splitP _	    []	     (ExtendTel _ _)	    = __IMPOSSIBLE__
    splitP _	    (_:_)     EmptyTel		    = __IMPOSSIBLE__
    splitP []	     _	      _			    = throwError $ NothingToSplit
    splitP ps	    []	      EmptyTel		    = throwError $ TooManyArguments ps
    splitP (p : ps) (q : qs) tel0@(ExtendTel a tel) =
      case insertImplicit p $ map (fmap fst) $ telToList tel0 of
	BadImplicits   -> typeError $ WrongHidingInLHS (unArg a) -- TODO: this is not the type the error expects
	NoSuchName x   -> typeError $ WrongHidingInLHS (unArg a)
	ImpInsert n    -> splitP (replicate n (implicitP (getRange p)) ++ ps) (q : qs) tel0
	NoInsertNeeded -> case namedThing $ unArg p of
	  -- TODO: split on literals
	  A.ConP _ c args -> do
	    a' <- reduce $ unArg a
	    case unEl a' of
	      Def d vs	-> do
		def <- theDef <$> getConstInfo d
		case def of
		  Datatype np _ _ _ _ _ -> do
		    let (pars, ixs) = splitAt np vs
		    return $ Split mempty
				   (fmap (const $ Focus c args q d pars ixs) a)
				   (fmap (Problem ps ()) tel)
		  -- TODO: record patterns
		  _ -> keepGoing
	      _	-> keepGoing
	  _ -> keepGoing
      where
	keepGoing = do
	  let p0 = Problem [p] () (ExtendTel a $ fmap (const EmptyTel) tel)
	  Split p1 foc p2 <- underAbstraction a tel $ \tel -> splitP ps qs tel
	  return $ Split (mappend p0 p1) foc p2

    implicitP = Arg Hidden . unnamed . A.ImplicitP . PatRange

-- | Compute the set of flexible patterns in a list of patterns. The result is
--   the deBruijn indices of the flexible patterns. A pattern is flexible if it
--   is dotted or implicit.
flexiblePatterns :: [NamedArg A.Pattern] -> FlexibleVars
flexiblePatterns nps = [ i | (i, p) <- zip [0..] $ reverse ps, flexible p ]
  where
    ps = map (namedThing . unArg) nps
    flexible (A.DotP _ _)    = True
    flexible (A.ImplicitP _) = True
    flexible _		     = False

-- * Index unification

newtype Unify a = U { unUnify :: StateT Sub TCM a }
  deriving (Monad, MonadIO, Functor, Applicative, MonadReader TCEnv)

type Sub = Map Nat Term

instance MonadState TCState Unify where
  get = U $ lift $ get
  put = U . lift . put

instance MonadTCM Unify where
  liftTCM = U . lift

-- | Includes flexible occurrences, metas need to be solved. TODO: relax?
occursCheck :: Nat -> Term -> Unify ()
occursCheck i u
  | i `freeIn` u = fail "occurs check in index unification"  -- TODO
  | otherwise	 = return ()

(|->) :: Nat -> Term -> Unify ()
i |-> u = do
  occursCheck i u
  U . modify $ Map.insert i u

-- | Compute the unification weak head normal form of a term, i.e. if it's a
-- flexible variable look it up in the current substitution.
ureduce :: Term -> Unify Term
ureduce u = do
  u <- liftTCM $ reduce u
  case u of
    Var i vs -> do
      mv <- U $ gets $ Map.lookup i
      case mv of
	Nothing	-> return u
	Just v	-> ureduce $ v `apply` vs
    _ -> return u

-- | Take a substitution σ and ensure that no variables from the domain appear
--   in the targets. The context of the targets is not changed.
flattenSubstitution :: Substitution -> Substitution
flattenSubstitution s = foldr instantiate s is
  where
    -- instantiated variables
    is = [ i | (i, Just _) <- zip [0..] s ]

    instantiate :: Nat -> Substitution -> Substitution
    instantiate i s = map (fmap $ inst i u) s
      where
	Just u = s !! i

    inst :: Nat -> Term -> Term -> Term
    inst i u v = substs us v
      where us = [var j | j <- [0..i - 1] ] ++ [u] ++ [var j | j <- [i + 1..] ]
	    var j = Var j []

-- | Unify indices.
unifyIndices :: FlexibleVars -> Type -> [Arg Term] -> [Arg Term] -> TCM Substitution
unifyIndices flex a us vs = do
  s <- flip execStateT Map.empty . unUnify $ unifyArgs a us vs
  let n = maximum $ (-1) : flex
  return $ flattenSubstitution [ Map.lookup i s | i <- [0..n] ]
  where
    flexible i = i `elem` flex

    unifyArgs :: Type -> [Arg Term] -> [Arg Term] -> Unify ()
    unifyArgs _ (_ : _) [] = __IMPOSSIBLE__
    unifyArgs _ [] (_ : _) = __IMPOSSIBLE__
    unifyArgs _ [] [] = return ()
    unifyArgs a (arg@(Arg _ u) : us) (Arg _ v : vs) = do
      a <- reduce a
      case funView $ unEl a of
	FunV (Arg _ b) _  -> do
	  unify b u v
	  unifyArgs (a `piApply` [arg]) us vs
	_	  -> __IMPOSSIBLE__

    -- TODO: eta for records here

    unify :: Type -> Term -> Term -> Unify ()
    unify a u v = do
      u <- ureduce u
      v <- ureduce v
      case (u, v) of
	(Var i [], v) | flexible i -> i |-> v
	(u, Var j []) | flexible j -> j |-> u
	(Var i us, Var j vs) | i == j  -> do
	    a <- typeOfBV i
	    unifyArgs a us vs
	(Con c us, Con c' vs) | c == c' -> do
	    -- The type is a datatype or a record.
	    Def d args <- reduce $ unEl a
	    -- Get the number of parameters.
	    def <- theDef <$> getConstInfo d
	    npars <- case def of
	      Datatype n _ _ _ _ _ -> return n
	      Record n _ _ _ _ _   -> return n
	      _			   -> __IMPOSSIBLE__
	    -- The type to compare the arguments at is obtained by
	    -- instantiating the parameters.
	    a <- defType <$> getConstInfo c
	    let a' = piApply a (take npars args)
	    unifyArgs a' us vs
	_  -> noConstraints $ equalTerm a u v

-- | The permutation should permute the corresponding telescope. (left-to-right list)
rename :: Subst t => Permutation -> t -> t
rename p = substs (renaming p)

renaming :: Permutation -> [Term]
renaming p = gamma'
  where
    n	   = size p
    gamma  = permute (reverseP $ invertP $ reverseP p) $ map var [0..]
    gamma' = gamma ++ map var [n..]
    var i  = Var i []

-- | Instantiate a telescope with a substitution. Might reorder the telescope.
--   @instantiateTel (Γ : Tel)(σ : Γ --> Γ) = Γσ~@
instantiateTel :: Substitution -> Telescope -> (Telescope, Permutation, [Term], [Type])
instantiateTel s tel = (tel5, composeP p ps, substs rho' rho, itypes)
  where

    -- Shrinking permutation (removing Justs) (and its complement, and reverse)
    ps  = Perm (size s) [ i | (i, Nothing) <- zip [0..] $ reverse s ]
    psR = reverseP ps
    psC = Perm (size s) [ i | (i, Just _)  <- zip [0..] $ reverse s ]

    -- s' : Substitution Γσ
    s' = rename psR s

    -- rho : [Tm Γσ]Γ
    rho = mkSubst s'

    -- tel1 : [Type Γ]Γ
    tel1 = flattenTel tel

    -- tel2 : [Type Γσ]Γ
    tel2 = substs rho tel1

    -- tel3 : [Type Γσ]Γσ
    tel3 = permute ps tel2

    -- p : Permutation (Γσ -> Γσ~)
    p = reorderTel tel3

    -- rho' : [Term Γσ~]Γσ
    rho' = renaming p

    -- tel4 : [Type Γσ~]Γσ~
    tel4 = substs rho' (permute p tel3)

    -- tel5 = Γσ~
    tel5 = unflattenTel tel4

    -- remember the types of the instantiations
    -- itypes : [Type Γσ~]Γ*
    itypes = substs rho' $ permute psC $ map unArg tel2

    -- Turn a Substitution ([Maybe Term]) into a substitution ([Term])
    -- (The result is an infinite list)
    mkSubst :: [Maybe Term] -> [Term]
    mkSubst s = rho
      where s'  = s ++ repeat Nothing
	    rho = zipWith var [0..] s'
	    var i Nothing  = Var i []
	    var i (Just u) = u

    -- Flatten telescope: (Γ : Tel) -> [Type Γ]
    flattenTel :: Telescope -> [Arg Type]
    flattenTel EmptyTel		 = []
    flattenTel (ExtendTel a tel) = raise (size tel + 1) a : flattenTel (absBody tel)

    -- Reorder: Γ -> Permutation (Γ -> Γ~)
    reorderTel :: [Arg Type] -> Permutation
    reorderTel tel = case topoSort comesBefore tel' of
      Nothing -> __IMPOSSIBLE__
      Just p  -> p
      where
	tel' = reverse $ zip [0..] $ reverse tel
	(i, _) `comesBefore` (_, a) = i `freeIn` a

    -- Unflatten: turns a flattened telescope into a proper telescope.
    unflattenTel :: [Arg Type] -> Telescope
    unflattenTel []	   = EmptyTel
    unflattenTel (a : tel) = ExtendTel a' (Abs "x" tel')
      where
	tel' = unflattenTel tel
	a'   = substs rho a
	rho  = replicate (size tel + 1) __IMPOSSIBLE__ ++ map var [0..]
	  where var i = Var i []

-- | Compute the dot pattern instantiations.
dotPatternInsts :: [Arg A.Pattern] -> Substitution -> [Type] -> [DotPatternInst]
dotPatternInsts ps s as = dpi (map unArg ps) s as
  where
    dpi []	 (_ : _)       _       = __IMPOSSIBLE__
    dpi (_ : _)	 []	       _       = __IMPOSSIBLE__
    dpi (_ : _)  (Just _ : _)  []      = __IMPOSSIBLE__
    dpi []	 []	       _       = []
    dpi (_ : ps) (Nothing : s) as      = dpi ps s as
    dpi (p : ps) (Just u : s) (a : as) = 
      case p of
	A.DotP _ e    -> DPI e u a : dpi ps s as
	A.ImplicitP _ -> dpi ps s as
	_	    -> __IMPOSSIBLE__

