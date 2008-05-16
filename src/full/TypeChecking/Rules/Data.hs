{-# OPTIONS -cpp #-}

module TypeChecking.Rules.Data where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans

import qualified Syntax.Abstract as A
import Syntax.Internal
import Syntax.Common
import Syntax.Position
import qualified Syntax.Info as Info

import TypeChecking.Monad
import TypeChecking.Conversion
import TypeChecking.Substitute
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Constraints
import TypeChecking.Pretty

import TypeChecking.Rules.Term ( isType_ )

import Interaction.Options

import Utils.Monad
import Utils.Size
import Utils.Tuple

#include "../../undefined.h"
import Utils.Impossible

---------------------------------------------------------------------------
-- * Datatypes
---------------------------------------------------------------------------

-- | Type check a datatype definition. Assumes that the type has already been
--   checked.
checkDataDef :: Info.DefInfo -> QName -> [A.LamBinding] -> [A.Constructor] -> TCM ()
checkDataDef i name ps cs =
    traceCall (CheckDataDef (getRange i) (qnameName name) ps cs) $ do -- TODO!! (qnameName)
	let npars = size ps

	-- Look up the type of the datatype.
	t <- typeOfConst name

	-- The parameters are in scope when checking the constructors. 
	(nofIxs, s) <- bindParameters ps t $ \tel t0 -> do

	    -- Parameters are always hidden in constructors
	    let tel' = hideTel tel

	    -- The type we get from bindParameters is Θ -> s where Θ is the type of
	    -- the indices. We count the number of indices and return s.
	    (nofIxs, s) <- splitType =<< normalise t0

	    -- Change the datatype from an axiom to a datatype with no constructors.
	    escapeContext (size tel) $
	      addConstant name ( Defn name t (defaultDisplayForm name) 0
			       $ Datatype npars nofIxs Nothing []
					  s (Info.defAbstract i)
			       )

	    -- Check the types of the constructors
	    mapM_ (checkConstructor name tel' nofIxs s) cs

	    -- Return the target sort and the number of indices
	    return (nofIxs, s)

	-- If proof irrelevance is enabled we have to check that datatypes in
	-- Prop contain at most one element.
	do  proofIrr <- proofIrrelevance
	    case (proofIrr, s, cs) of
		(True, Prop, _:_:_) -> typeError PropMustBeSingleton
		_		    -> return ()

	-- Add the datatype to the signature as a datatype. It was previously
	-- added as an axiom.
	addConstant name (Defn name t (defaultDisplayForm name) 0 $
                            Datatype npars nofIxs Nothing (map cname cs)
				     s (Info.defAbstract i)
			 )
    where
	cname (A.ScopedDecl _ [d]) = cname d
	cname (A.Axiom _ x _)	   = x
	cname _			   = __IMPOSSIBLE__ -- constructors are axioms

	hideTel  EmptyTel		  = EmptyTel
	hideTel (ExtendTel (Arg _ t) tel) = ExtendTel (Arg Hidden t) $ hideTel <$> tel

	splitType (El _ (Pi _ b))  = ((+ 1) -*- id) <$> splitType (absBody b)
	splitType (El _ (Fun _ b)) = ((+ 1) -*- id) <$> splitType b
	splitType (El _ (Sort s))  = return (0, s)
	splitType (El _ t)	   = typeError $ DataMustEndInSort t

-- | Type check a constructor declaration. Checks that the constructor targets
--   the datatype and that it fits inside the declared sort.
checkConstructor :: QName -> Telescope -> Int -> Sort -> A.Constructor -> TCM ()
checkConstructor d tel nofIxs s (A.ScopedDecl scope [con]) = do
  setScope scope
  checkConstructor d tel nofIxs s con
checkConstructor d tel nofIxs s con@(A.Axiom i c e) =
    traceCall (CheckConstructor d tel s con) $ do
	t <- isType_ e
	n <- size <$> getContextTelescope
	verbose 5 $ do
	    td <- prettyTCM t
	    liftIO $ putStrLn $ "checking that " ++ show td ++ " ends in " ++ show d
	    liftIO $ putStrLn $ "  nofPars = " ++ show n
	constructs n t d
	verbose 5 $ do
	    d <- prettyTCM s
	    liftIO $ putStrLn $ "checking that the type fits in " ++ show d
	t `fitsIn` s
	escapeContext (size tel)
	    $ addConstant c
	    $ Defn c (telePi tel t) (defaultDisplayForm c) 0
	    $ Constructor (size tel) c d Nothing $ Info.defAbstract i
checkConstructor _ _ _ _ _ = __IMPOSSIBLE__ -- constructors are axioms


-- | Bind the parameters of a datatype. The bindings should be domain free.
bindParameters :: [A.LamBinding] -> Type -> (Telescope -> Type -> TCM a) -> TCM a
bindParameters [] a ret = ret EmptyTel a
bindParameters (A.DomainFree h x : ps) (El _ (Pi (Arg h' a) b)) ret
    | h /= h'	=
	__IMPOSSIBLE__
    | otherwise = addCtx x arg $ bindParameters ps (absBody b) $ \tel s ->
		    ret (ExtendTel arg $ Abs (show x) tel) s
  where
    arg = Arg h a
bindParameters (A.DomainFree h x : ps) (El _ (Fun (Arg h' a) b)) ret
    | h /= h'	=
	__IMPOSSIBLE__
    | otherwise = addCtx x arg $ bindParameters ps (raise 1 b) $ \tel s ->
		    ret (ExtendTel arg $ Abs (show x) tel) s
  where
    arg = Arg h a
bindParameters _ _ _ = __IMPOSSIBLE__


-- | Check that the arguments to a constructor fits inside the sort of the datatype.
--   The first argument is the type of the constructor.
fitsIn :: Type -> Sort -> TCM ()
fitsIn t s =
    do	t <- instantiate t
	case funView $ unEl t of
	    FunV arg@(Arg h a) _ -> do
		let s' = getSort a
                s' `leqSort` s
		x <- freshName_ (argName t)
		let v  = Arg h $ Var 0 []
		    t' = piApply (raise 1 t) [v]
		addCtx x arg $ fitsIn t' s
	    _		     -> return ()

-- | Check that a type constructs something of the given datatype. The first
--   argument is the number of parameters to the datatype.
--   TODO: what if there's a meta here?
constructs :: Int -> Type -> QName -> TCM ()
constructs nofPars t q = constrT 0 t
    where
	constrT n (El s v) = constr n s v

	constr n s v = do
	    v <- reduce v
	    case v of
		Pi a b	-> underAbstraction a b $ \t ->
			   constrT (n + 1) t
		Fun _ b -> constrT n b
		Def d vs
		    | d == q -> checkParams n =<< reduce (take nofPars vs)
						    -- we only check the parameters
		_ -> bad $ El s v

	bad t = typeError $ ShouldEndInApplicationOfTheDatatype t

	checkParams n vs = zipWithM_ sameVar (map unArg vs) ps
	    where
		def = Def q []
		ps = reverse [ i | (i,Arg h _) <- zip [n..] vs ]

		sameVar v i = do
		    t <- typeOfBV i
		    noConstraints $ equalTerm t v (Var i [])


-- | Force a type to be a specific datatype.
forceData :: MonadTCM tcm => QName -> Type -> tcm Type
forceData d (El s0 t) = liftTCM $ do
    t' <- reduce t
    d  <- canonicalName d
    case t' of
	Def d' _
	    | d == d'   -> return $ El s0 t'
	    | otherwise	-> fail $ "wrong datatype " ++ show d ++ " != " ++ show d'
	MetaV m vs	    -> do
	    Defn _ t _ _ Datatype{dataSort = s} <- getConstInfo d
	    ps <- newArgsMeta t
	    noConstraints $ equalType (El s0 t') (El s (Def d ps)) -- TODO: too strict?
	    reduce $ El s0 t'
	_ -> typeError $ ShouldBeApplicationOf (El s0 t) d

