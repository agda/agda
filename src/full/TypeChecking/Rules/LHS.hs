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
import Syntax.Literal

import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Substitute
import TypeChecking.Implicit
import TypeChecking.Free
import TypeChecking.Conversion
import TypeChecking.Constraints
import TypeChecking.Pretty
import TypeChecking.Empty (isEmptyType)
import TypeChecking.Primitive (constructorForm)

import TypeChecking.Rules.Term (checkExpr, litType)

import Utils.Permutation
import Utils.Size
import Utils.Tuple

#include "../../undefined.h"

data DotPatternInst = DPI A.Expr Term Type
data AsBinding	    = AsB Name Term Type
type Substitution   = [Maybe Term]
type FlexibleVars   = [Nat]

data Problem' p	    = Problem { problemInPat  :: [NamedArg A.Pattern]
			      , problemOutPat :: p
			      , problemTel    :: Telescope
			      }
data Focus	    = Focus   { focusCon      :: QName
			      , focusConArgs  :: [NamedArg A.Pattern]
			      , focusRange    :: Range
			      , focusOutPat   :: OneHolePatterns
			      , focusHoleIx   :: Int  -- ^ index of focused variable in the out patterns
			      , focusDatatype :: QName
			      , focusParams   :: [Arg Term]
			      , focusIndices  :: [Arg Term]
			      }
		    | LitFocus Literal OneHolePatterns Int Type
data SplitProblem   = Split ProblemPart [Name]	-- ^ as-bindings for the focus
			    (Arg Focus) (Abs ProblemPart)

data SplitError	    = NothingToSplit
		    | SplitPanic String

type ProblemPart = Problem' ()

-- | The permutation should permute @allHoles@ of the patterns to correspond to
--   the abstract patterns in the problem.
type Problem	 = Problem' (Permutation, [Arg Pattern])

instance Subst DotPatternInst where
  substs us (DPI e v a) = uncurry (DPI e) $ substs us (v,a)

instance PrettyTCM DotPatternInst where
  prettyTCM (DPI e v a) = sep [ prettyA e <+> text "="
			      , nest 2 $ prettyTCM v <+> text ":"
			      , nest 2 $ prettyTCM a
			      ]

instance Subst AsBinding where
  substs us (AsB x v a) = uncurry (AsB x) $ substs us (v, a)

instance Raise AsBinding where
  raiseFrom m k (AsB x v a) = uncurry (AsB x) $ raiseFrom m k (v, a)

instance PrettyTCM AsBinding where
  prettyTCM (AsB x v a) =
    sep [ prettyTCM x <> text "@" <> parens (prettyTCM v)
	, nest 2 $ text ":" <+> prettyTCM a
	]

instance Error SplitError where
  noMsg  = NothingToSplit
  strMsg = SplitPanic

instance Monoid p => Monoid (Problem' p) where
  mempty = Problem [] mempty EmptyTel
  Problem ps1 qs1 tel1 `mappend` Problem ps2 qs2 tel2 =
    Problem (ps1 ++ ps2) (mappend qs1 qs2) (abstract tel1 tel2)

instance (Monad m, Error err) => Applicative (ErrorT err m) where
  pure	= return
  (<*>) = ap

instance (Error err, MonadTCM tcm) => MonadTCM (ErrorT err tcm) where
  liftTCM = lift . liftTCM

-- | Insert implicit patterns in a problem.
insertImplicitProblem :: Problem -> TCM Problem
insertImplicitProblem (Problem ps qs tel) = do
  reportSDoc "tc.lhs.imp" 15 $
    sep [ text "insertImplicits"
	, nest 2 $ brackets $ fsep $ punctuate comma $ map prettyA ps
	, nest 2 $ prettyTCM tel
	]
  ps' <- insertImplicitPatterns ps tel
  return $ Problem ps' qs tel

-- | Insert implicit patterns in a list of patterns.
insertImplicitPatterns :: [NamedArg A.Pattern] -> Telescope -> TCM [NamedArg A.Pattern]
insertImplicitPatterns ps EmptyTel = return ps
insertImplicitPatterns ps tel@(ExtendTel _ tel') = case ps of
  [] -> do
    i <- insImp dummy tel
    case i of
      Just n	-> return $ replicate n implicitP
      Nothing	-> return []
  p : ps -> do
    i <- insImp p tel
    case i of
      Just 0	-> __IMPOSSIBLE__
      Just n	-> insertImplicitPatterns (replicate n implicitP ++ p : ps) tel
      Nothing	-> (p :) <$> insertImplicitPatterns ps (absBody tel')
  where
    dummy = Arg NotHidden $ unnamed ()

    insImp x tel = case insertImplicit x $ map (fmap fst) $ telToList tel of
      BadImplicits   -> typeError $ WrongHidingInLHS (telePi tel $ sort Prop)
      NoSuchName x   -> typeError $ WrongHidingInLHS (telePi tel $ sort Prop)
      ImpInsert n    -> return $ Just n
      NoInsertNeeded -> return Nothing

    implicitP = Arg Hidden . unnamed . A.ImplicitP . PatRange $ noRange

-- | TODO: move to Syntax.Abstract.View
asView :: A.Pattern -> ([Name], A.Pattern)
asView (A.AsP _ x p) = (x :) -*- id $ asView p
asView p	     = ([], p)

-- | Split a problem at the first constructor of datatype type. Implicit
--   patterns should have been inserted.
splitProblem :: Problem -> TCM (Either SplitError SplitProblem)
splitProblem (Problem ps (perm, qs) tel) = runErrorT $
    splitP ps (permute perm $ zip [0..] $ allHoles qs) tel
  where
    splitP :: [NamedArg A.Pattern] -> [(Int, OneHolePatterns)] -> Telescope -> ErrorT SplitError TCM SplitProblem
    splitP _	    []		 (ExtendTel _ _)	 = __IMPOSSIBLE__
    splitP _	    (_:_)	  EmptyTel		 = __IMPOSSIBLE__
    splitP []	     _		  _			 = throwError $ NothingToSplit
    splitP ps	    []		  EmptyTel		 = __IMPOSSIBLE__
    splitP (p : ps) ((i, q) : qs) tel0@(ExtendTel a tel) =
      case asView $ namedThing $ unArg p of
	(xs, A.LitP lit)  -> do
	  b <- lift $ litType lit
	  ok <- lift $ do
	      noConstraints (equalType (unArg a) b)
	      return True
	    `catchError` \_ -> return False
	  if ok
	    then return $
	      Split mempty
		    xs
		    (fmap (LitFocus lit q i) a)
		    (fmap (Problem ps ()) tel)
	    else keepGoing
	(xs, A.ConP _ c args) -> do
	  a' <- reduce $ unArg a
	  case unEl a' of
	    Def d vs	-> do
	      def <- theDef <$> getConstInfo d
	      case def of
		Datatype np _ _ _ _ _ -> do
		  let (pars, ixs) = splitAt np vs
		  reportSDoc "tc.lhs.split" 10 $
		    vcat [ sep [ text "splitting on"
			       , nest 2 $ fsep [ prettyA p, text ":", prettyTCM a ]
			       ]
			 , nest 2 $ text "pars =" <+> fsep (punctuate comma $ map prettyTCM pars)
			 , nest 2 $ text "ixs  =" <+> fsep (punctuate comma $ map prettyTCM ixs)
			 ]
		  return $ Split mempty
				 xs
				 (fmap (const $ Focus c args (getRange p) q i d pars ixs) a)
				 (fmap (Problem ps ()) tel)
		-- TODO: record patterns
		_ -> keepGoing
	    _	-> keepGoing
	p -> keepGoing
      where
	keepGoing = do
	  let p0 = Problem [p] () (ExtendTel a $ fmap (const EmptyTel) tel)
	  Split p1 xs foc p2 <- underAbstraction a tel $ \tel -> splitP ps qs tel
	  return $ Split (mappend p0 p1) xs foc p2


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
occursCheck :: Nat -> Term -> Type -> Unify ()
occursCheck i u a
  | i `freeIn` u = typeError $ UnequalTerms (Var i []) u a
  | otherwise	 = return ()

(|->) :: Nat -> (Term, Type) -> Unify ()
i |-> (u, a) = do
  occursCheck i u a
  reportSDoc "tc.lhs.unify" 15 $ prettyTCM (Var i []) <+> text ":=" <+> prettyTCM u
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
  reportSDoc "tc.lhs.uni" 10 $
    sep [ text "unifyIndices"
	, nest 2 $ text (show flex)
	, nest 2 $ parens (prettyTCM a)
	, nest 2 $ brackets $ fsep $ punctuate comma $ map prettyTCM us
	, nest 2 $ brackets $ fsep $ punctuate comma $ map prettyTCM vs
	]
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
      reportSDoc "tc.lhs.uni" 15 $
	sep [ text "unify"
	    , nest 2 $ parens $ prettyTCM u
	    , nest 2 $ parens $ prettyTCM v
	    , nest 2 $ text ":" <+> prettyTCM a
	    ]
      case (u, v) of
	(Var i [], v) | flexible i -> i |-> (v, a)
	(u, Var j []) | flexible j -> j |-> (u, a)
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

-- | If @permute π : [a]Γ -> [a]Δ@, then @substs (renaming π) : Term Γ -> Term Δ@
renaming :: Permutation -> [Term]
renaming p = gamma'
  where
    n	   = size p
    gamma  = permute (reverseP $ invertP $ reverseP p) $ map var [0..]
    gamma' = gamma ++ map var [n..]
    var i  = Var i []

-- | If @permute π : [a]Γ -> [a]Δ@, then @substs (renamingR π) : Term Δ -> Term Γ@
renamingR :: Permutation -> [Term]
renamingR p@(Perm n _) = permute (reverseP p) (map var [0..]) ++ map var [n..]
  where
    var i  = Var i []

-- | Instantiate a telescope with a substitution. Might reorder the telescope.
--   @instantiateTel (Γ : Tel)(σ : Γ --> Γ) = Γσ~@
--   Monadic only for debugging purposes.
instantiateTel :: Substitution -> Telescope -> TCM (Telescope, Permutation, [Term], [Type])
instantiateTel s tel = do

  reportSDoc "tc.lhs.inst" 10 $ sep
    [ text "instantiateTel "
    , nest 2 $ fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) s
    , nest 2 $ prettyTCM tel
    ]

  -- Shrinking permutation (removing Justs) (and its complement, and reverse)
  let ps  = Perm (size s) [ i | (i, Nothing) <- zip [0..] $ reverse s ]
      psR = reverseP ps
      psC = Perm (size s) [ i | (i, Just _)  <- zip [0..] $ reverse s ]

  reportS "tc.lhs.inst" 10 $ unlines
    [ "ps  = " ++ show ps
    , "psR = " ++ show psR
    , "psC = " ++ show psC
    ]

  -- s' : Substitution Γσ
  let s' = rename psR s

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $ 
    text "s'   =" <+> fsep (punctuate comma $ map (maybe (text "_") prettyTCM) s')

  -- rho : [Tm Γσ]Γ
  let rho = mkSubst s'

  -- tel1 : [Type Γ]Γ
  let tel1   = flattenTel tel
      names1 = map (fst . unArg) $ telToList tel

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $ 
    text "tel1 =" <+> brackets (fsep $ punctuate comma $ map prettyTCM tel1)

  -- tel2 : [Type Γσ]Γ
  let tel2 = substs rho tel1

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $ 
    text "tel2 =" <+> brackets (fsep $ punctuate comma $ map prettyTCM tel2)

  -- tel3 : [Type Γσ]Γσ
  let tel3   = permute ps tel2
      names3 = permute ps names1

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $ 
    text "tel3 =" <+> brackets (fsep $ punctuate comma $ map prettyTCM tel3)

  -- p : Permutation (Γσ -> Γσ~)
  let p = reorderTel tel3

  reportSLn "tc.lhs.inst" 10 $ "p   = " ++ show p

  -- rho' : [Term Γσ~]Γσ
  let rho' = renaming (reverseP p)

  -- tel4 : [Type Γσ~]Γσ~
  let tel4   = substs rho' (permute p tel3)
      names4 = permute p names3

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $ 
    text "tel4 =" <+> brackets (fsep $ punctuate comma $ map prettyTCM tel4)

  -- tel5 = Γσ~
  let tel5 = unflattenTel names4 tel4

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $ 
    text "tel5 =" <+> prettyTCM tel5

  -- remember the types of the instantiations
  -- itypes : [Type Γσ~]Γ*
  let itypes = substs rho' $ permute psC $ map unArg tel2

  return (tel5, composeP p ps, substs rho' rho, itypes)
  where

    -- Turn a Substitution ([Maybe Term]) into a substitution ([Term])
    -- (The result is an infinite list)
    mkSubst :: [Maybe Term] -> [Term]
    mkSubst s = rho 0 s'
      where s'  = s ++ repeat Nothing
	    rho i (Nothing : s) = Var i [] : rho (i + 1) s
	    rho i (Just u  : s) = u : rho i s
	    rho _ []		= __IMPOSSIBLE__

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
    unflattenTel :: [String] -> [Arg Type] -> Telescope
    unflattenTel []	  []	    = EmptyTel
    unflattenTel (x : xs) (a : tel) = ExtendTel a' (Abs x tel')
      where
	tel' = unflattenTel xs tel
	a'   = substs rho a
	rho  = replicate (size tel + 1) __IMPOSSIBLE__ ++ map var [0..]
	  where var i = Var i []
    unflattenTel [] (_ : _) = __IMPOSSIBLE__
    unflattenTel (_ : _) [] = __IMPOSSIBLE__

-- | Produce a nice error message when splitting failed
nothingToSplitError :: Problem -> TCM a
nothingToSplitError (Problem ps _ tel) = splitError ps tel
  where
    splitError []	EmptyTel    = __IMPOSSIBLE__
    splitError (_:_)	EmptyTel    = __IMPOSSIBLE__
    splitError []	ExtendTel{} = __IMPOSSIBLE__
    splitError (p : ps) (ExtendTel a tel)
      | isBad p   = traceCall (CheckPattern (strip p) EmptyTel (unArg a)) $ case strip p of
	  A.DotP _ e -> typeError $ UninstantiatedDotPattern e
	  p	     -> typeError $ IlltypedPattern p (unArg a)
      | otherwise = underAbstraction a tel $ \tel -> splitError ps tel
      where
	strip = snd . asView . namedThing . unArg
	isBad p = case strip p of
	  A.DotP _ _   -> True
	  A.ConP _ _ _ -> True
	  A.LitP _     -> True
	  _	       -> False


-- | Compute the dot pattern instantiations.
dotPatternInsts :: [NamedArg A.Pattern] -> Substitution -> [Type] -> [DotPatternInst]
dotPatternInsts ps s as = dpi (map (namedThing . unArg) ps) (reverse s) as
  where
    dpi (_ : _)	 []	       _       = __IMPOSSIBLE__
    dpi (_ : _)  (Just _ : _)  []      = __IMPOSSIBLE__
    -- the substitution also contains entries for module parameters, so it can
    -- be longer than the pattern
    dpi []	 _	       _       = []
    dpi (_ : ps) (Nothing : s) as      = dpi ps s as
    dpi (p : ps) (Just u : s) (a : as) = 
      case p of
	A.DotP _ e    -> DPI e u a : dpi ps s as
	A.ImplicitP _ -> dpi ps s as
	_	    -> __IMPOSSIBLE__

-- | Check if a problem is solved. That is, if the patterns are all variables.
isSolvedProblem :: Problem -> Bool
isSolvedProblem = all (isVar . snd . asView . namedThing . unArg) . problemInPat
  where
    isVar (A.VarP _)	  = True
    isVar (A.WildP _)	  = True
    isVar (A.ImplicitP _) = True
    isVar (A.AbsurdP _)	  = True
    isVar _		  = False

-- | Check that a dot pattern matches it's instantiation.
checkDotPattern :: DotPatternInst -> TCM ()
checkDotPattern (DPI e v a) =
  traceCall (CheckDotPattern e v) $ do
  reportSDoc "tc.lhs.dot" 15 $
    sep [ text "checking dot pattern"
	, nest 2 $ prettyA e
	, nest 2 $ text "=" <+> prettyTCM v
	, nest 2 $ text ":" <+> prettyTCM a
	]
  u <- checkExpr e a
  noConstraints $ equalTerm a u v

-- | Bind the variables in a left hand side. Precondition: the patterns should
--   all be 'A.VarP', 'A.WildP', or 'A.ImplicitP' and the telescope should have
--   the same size as the pattern list.
bindLHSVars :: [NamedArg A.Pattern] -> Telescope -> TCM a -> TCM a
bindLHSVars []	     (ExtendTel _ _)   _   = __IMPOSSIBLE__
bindLHSVars (_ : _)   EmptyTel	       _   = __IMPOSSIBLE__
bindLHSVars []	      EmptyTel	       ret = ret
bindLHSVars (p : ps) (ExtendTel a tel) ret =
  case namedThing $ unArg p of
    A.VarP x	  -> addCtx x a $ bindLHSVars ps (absBody tel) ret
    A.WildP _	  -> bindDummy (absName tel)
    A.ImplicitP _ -> bindDummy (absName tel)
    A.AbsurdP _	  -> do
      isEmptyType $ unArg a
      bindDummy (absName tel)
    _		  -> __IMPOSSIBLE__
    where
      name "_" = freshNoName_
      name s   = freshName_ ("_" ++ s)
      bindDummy s = do
	x <- name s
	addCtx x a $ bindLHSVars ps (absBody tel) ret

-- | Bind as patterns
bindAsPatterns :: [AsBinding] -> TCM a -> TCM a
bindAsPatterns []		 ret = ret
bindAsPatterns (AsB x v a : asb) ret =
  addLetBinding x v a $ bindAsPatterns asb ret

-- | Check a LHS. Main function.
checkLeftHandSide :: [NamedArg A.Pattern] -> Type ->
		     (Telescope -> Telescope -> [Term] -> [String] -> [Arg Pattern] -> Type -> Permutation -> TCM a) -> TCM a
checkLeftHandSide ps a ret = do
  a <- normalise a
  let TelV tel0 b0 = telView a
  ps <- insertImplicitPatterns ps tel0
  unless (size tel0 >= size ps) $ typeError $ TooManyArgumentsInLHS (size ps) a
  let (as, bs) = splitAt (size ps) $ telToList tel0
      gamma    = telFromList as
      b	       = telePi (telFromList bs) b0

      -- internal patterns start as all variables
      ips      = map (fmap (VarP . fst)) as

      problem  = Problem ps (idP $ size ps, ips) gamma

  reportSDoc "tc.lhs.top" 10 $
    vcat [ text "checking lhs:"
	 , nest 2 $ vcat
	   [ text "ps    =" <+> fsep (map prettyA ps)
	   , text "a     =" <+> prettyTCM a
	   , text "a'    =" <+> prettyTCM (telePi tel0 b0)
	   , text "tel0  =" <+> prettyTCM tel0
	   , text "b0    =" <+> prettyTCM b0
	   , text "gamma =" <+> prettyTCM gamma
	   , text "b	 =" <+> addCtxTel gamma (prettyTCM b)
	   ]
	 ]

  let idsub = [ Var i [] | i <- [0..] ]

  (Problem ps (perm, qs) delta, sigma, dpi, asb) <- checkLHS problem idsub [] []
  let b' = substs sigma b

  reportSDoc "tc.lhs.top" 10 $
    vcat [ text "checked lhs:"
	 , nest 2 $ vcat
	   [ text "ps    = " <+> fsep (map prettyA ps)
	   , text "perm  = " <+> text (show perm)
	   , text "delta = " <+> prettyTCM delta
	   , text "dpi	 = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi)
	   , text "asb	 = " <+> brackets (fsep $ punctuate comma $ map prettyTCM asb)
	   ]
         ]
  bindLHSVars ps delta $ bindAsPatterns asb $ do
    reportSDoc "tc.lhs.top" 10 $ nest 2 $ text "type  = " <+> prettyTCM b'
    mapM_ checkDotPattern dpi
    let rho = renamingR perm -- I'm not certain about this...
	Perm n _ = perm
	xs  = replicate n "z" -- map (fst . unArg) $ telToList tel
    ret gamma delta rho xs qs b' perm
  where
    checkLHS :: Problem -> [Term] -> [DotPatternInst] -> [AsBinding] ->
		TCM (Problem, [Term], [DotPatternInst], [AsBinding])
    checkLHS problem sigma dpi asb
      | isSolvedProblem problem	= do
	problem <- insertImplicitProblem problem -- inserting implicit patterns preserve solvedness
	return (problem, sigma, dpi, asb)
      | otherwise		= do
	sp <- splitProblem =<< insertImplicitProblem problem
	case sp of
	  Left NothingToSplit	-> nothingToSplitError problem
	  Left (SplitPanic err) -> __IMPOSSIBLE__

	  -- Split on literal pattern
	  Right (Split p0 xs (Arg h (LitFocus lit iph hix a)) p1) -> do

	    -- plug the hole with a lit pattern
	    let ip    = plugHole (LitP lit) iph
		iperm = expandP hix 0 $ fst (problemOutPat problem)

	    -- substitute the literal in p1 and sigma and dpi and asb
	    let delta1 = problemTel p0
		delta2 = absApp (fmap problemTel p1) (Lit lit)
		rho    = [ var i | i <- [0..size delta2 - 1] ]
		      ++ [ raise (size delta2) $ Lit lit ]
		      ++ [ var i | i <- [size delta2 ..] ]
		  where
		    var i = Var i []
		sigma'	 = substs rho sigma
		dpi'	 = substs rho dpi
		asb0	 = substs rho asb

	    -- Compute the new problem
	    let ps'	 = problemInPat p0 ++ problemInPat (absBody p1)
		delta'	 = abstract delta1 delta2
		problem' = Problem ps' (iperm, ip) delta'
		asb'	 = raise (size delta2) (map (\x -> AsB x (Lit lit) a) xs) ++ asb0
	    checkLHS problem' sigma' dpi' asb'

	  -- Split on constructor pattern
	  Right (Split p0 xs (Arg h
		  ( Focus { focusCon	  = c
			  , focusConArgs  = qs
			  , focusRange	  = r
			  , focusOutPat	  = iph
			  , focusHoleIx	  = hix
			  , focusDatatype = d
			  , focusParams	  = vs
			  , focusIndices  = ws
			  }
		  )) p1
		) -> traceCall (CheckPattern (A.ConP (PatRange r) c qs) (problemTel p0)
			       (El Prop $ Def d $ vs ++ ws)) $ do

	    let delta1 = problemTel p0

	    reportSDoc "tc.lhs.top" 10 $ sep
	      [ text "checking lhs"
	      , nest 2 $ text "tel =" <+> prettyTCM (problemTel problem)
	      ]

	    reportSDoc "tc.lhs.split" 15 $ sep
	      [ text "split problem"
	      , nest 2 $ vcat
		[ text "delta1 = " <+> prettyTCM delta1
		, text "delta2 = " <+> prettyTCM (problemTel $ absBody p1)
		]
	      ]

	    Con c [] <- constructorForm =<< normalise (Con c [])

	    -- Lookup the type of the constructor at the given parameters
	    a <- normalise =<< (`piApply` vs) . defType <$> getConstInfo c

	    -- It will end in an application of the datatype
	    let TelV gamma ca@(El _ (Def d' us)) = telView a

	    -- This should be the same datatype as we split on
	    unless (d == d') $ typeError $ ShouldBeApplicationOf ca d'

	    -- Insert implicit patterns
	    qs' <- insertImplicitPatterns qs gamma

	    unless (size qs' == size gamma) $
	      typeError $ WrongNumberOfConstructorArguments c (size gamma) (size qs')

	    -- Get the type of the datatype.
	    da <- normalise =<< (`piApply` vs) . defType <$> getConstInfo d

	    -- Compute the flexible variables
	    let flex = flexiblePatterns (problemInPat p0 ++ qs')

	    reportSDoc "tc.lhs.top" 15 $ addCtxTel delta1 $
	      sep [ text "preparing to unify"
		  , nest 2 $ vcat
		    [ text "c	  =" <+> prettyTCM c <+> text ":" <+> prettyTCM a
		    , text "d	  =" <+> prettyTCM d <+> text ":" <+> prettyTCM da
		    , text "gamma =" <+> prettyTCM gamma
		    , text "vs	  =" <+> brackets (fsep $ punctuate comma $ map prettyTCM vs)
		    , text "ws	  =" <+> brackets (fsep $ punctuate comma $ map prettyTCM ws)
		    ]
		  ]

	    -- Unify constructor target and given type (in Δ₁Γ)
	    sub0 <- addCtxTel (delta1 `abstract` gamma) $
		    unifyIndices flex da (drop (size vs) us) (raise (size gamma) ws)

	    -- We should subsitute c ys for x in Δ₂ and sigma
	    let ys     = reverse [ Arg h (Var i []) | (i, Arg h _) <- zip [0..] $ reverse (telToList gamma) ]
		delta2 = absApp (raise (size gamma) $ fmap problemTel p1) (Con c ys)
		rho0 = [ var i | i <- [0..size delta2 - 1] ]
		    ++ [ raise (size delta2) $ Con c ys ]
		    ++ [ var i | i <- [size delta2 + size gamma ..] ]
		  where
		    var i = Var i []
		sigma0 = substs rho0 sigma
		dpi0   = substs rho0 dpi
		asb0   = substs rho0 asb

	    reportSDoc "tc.lhs.top" 15 $ addCtxTel (delta1 `abstract` gamma) $ nest 2 $ vcat
	      [ text "delta2 =" <+> prettyTCM delta2
	      , text "sub0   =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub0)
	      ]
	    reportSDoc "tc.lhs.top" 15 $ addCtxTel (delta1 `abstract` gamma `abstract` delta2) $
	      nest 2 $ vcat
		[ text "dpi0 = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi0)
		]

	    -- Plug the hole in the out pattern with c ys
	    let ysp = map (fmap (VarP . fst)) $ telToList gamma
		ip  = plugHole (ConP c ysp) iph

	    -- Δ₁Γ ⊢ sub0, we need something in Δ₁ΓΔ₂
	    -- Also needs to be padded with Nothing's to have the right length.
	    let pad n xs x = xs ++ replicate (max 0 $ n - size xs) x
		newTel = problemTel p0 `abstract` (gamma `abstract` delta2)
		sub    = replicate (size delta2) Nothing ++
			 pad (size delta1 + size gamma) (raise (size delta2) sub0) Nothing

	    reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
	      [ text "newTel =" <+> prettyTCM newTel
	      , addCtxTel newTel $ text "sub =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub)
	      ]

	    -- Instantiate the new telescope with the given substitution
	    (delta', perm, rho, instTypes) <- instantiateTel sub newTel

	    reportSDoc "tc.lhs.inst" 12 $
	      vcat [ sep [ text "instantiateTel"
			 , nest 4 $ brackets $ fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub
			 , nest 4 $ prettyTCM newTel
			 ]
		   , nest 2 $ text "delta' =" <+> prettyTCM delta'
		   , nest 2 $ text "perm   =" <+> text (show perm)
		   , nest 2 $ text "itypes =" <+> fsep (punctuate comma $ map prettyTCM instTypes)
		   ]

	    -- Compute the new dot pattern instantiations
	    let ps0'   = problemInPat p0 ++ qs' ++ problemInPat (absBody p1)
		newDpi = dotPatternInsts ps0' (substs rho sub) instTypes

	    reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
	      [ text "subst rho sub =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) (substs rho sub))
	      , text "ps0' =" <+> brackets (fsep $ punctuate comma $ map prettyA ps0')
	      ]

	    -- The final dpis are the new ones plus the old ones substituted by ρ
	    let dpi' = substs rho dpi0 ++ newDpi

	    -- Add the new as-bindings
	    let asb' = raise (size delta2) (map (\x -> AsB x (Con c ys) ca) xs) ++ asb0

	    reportSDoc "tc.lhs.top" 15 $ nest 2 $
	      text "dpi' = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi')

	    -- Apply the substitution to the type
	    let sigma'   = substs rho sigma0

	    reportSDoc "tc.lhs.inst" 15 $
	      nest 2 $ text "ps0 = " <+> brackets (fsep $ punctuate comma $ map prettyA ps0')

	    -- Permute the in patterns
	    let ps'  = permute perm ps0'

	   -- Compute the new permutation of the out patterns. This is the composition of
	    -- the new permutation with the expansion of the old permutation to
	    -- reflect the split.
	    let perm'  = expandP hix (size gamma) $ fst (problemOutPat problem)
		iperm' = perm `composeP` perm'

	    -- Construct the new problem
	    let problem' = Problem ps' (iperm', ip) delta'

	    reportSDoc "tc.lhs.top" 12 $ sep
	      [ text "new problem"
	      , nest 2 $ vcat
		[ text "ps'    = " <+> fsep (map prettyA ps')
		, text "delta' = " <+> prettyTCM delta'
		]
	      ]

	    reportSDoc "tc.lhs.top" 14 $ nest 2 $ vcat
	      [ text "perm'  =" <+> text (show perm')
	      , text "iperm' =" <+> text (show iperm')
	      ]

	    -- Continue splitting
	    checkLHS problem' sigma' dpi' asb'

