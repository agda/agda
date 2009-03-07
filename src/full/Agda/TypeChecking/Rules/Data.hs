{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.Data where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import qualified System.IO.UTF8 as UTF8

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as Info

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Polarity

import Agda.TypeChecking.Rules.Term ( isType_ )

import Agda.Interaction.Options

import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "../../undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Datatypes
---------------------------------------------------------------------------

-- | Type check a datatype definition. Assumes that the type has already been
--   checked.
checkDataDef :: Info.DefInfo -> Induction -> QName -> [A.LamBinding] -> [A.Constructor] -> TCM ()
checkDataDef i ind name ps cs =
    traceCall (CheckDataDef (getRange i) (qnameName name) ps cs) $ do -- TODO!! (qnameName)
	let npars = size ps

	-- Look up the type of the datatype.
	t <- instantiateFull =<< typeOfConst name

	-- The parameters are in scope when checking the constructors. 
	dataDef <- bindParameters ps t $ \tel t0 -> do

	    -- Parameters are always hidden in constructors
	    let tel' = hideTel tel

	    -- The type we get from bindParameters is Θ -> s where Θ is the type of
	    -- the indices. We count the number of indices and return s.
            (nofIxs, s) <- splitType =<< normalise t0

	    -- Change the datatype from an axiom to a datatype with no constructors.
            let dataDef = Datatype { dataPars           = npars
                                   , dataIxs            = nofIxs
                                   , dataInduction      = ind
                                   , dataClause         = Nothing
                                   , dataCons           = []     -- Constructors are added later
				   , dataSort           = s
                                   , dataHsType         = Nothing
                                   , dataAbstr          = Info.defAbstract i
                                   , dataPolarity       = []
                                   , dataArgOccurrences = []
                                   }

	    escapeContext (size tel) $ do
	      addConstant name ( Defn name t (defaultDisplayForm name) 0 dataDef )

	    -- Check the types of the constructors
	    mapM_ (checkConstructor name tel' nofIxs s ind) cs

	    -- Return the data definition
	    return dataDef

        let nofIxs = dataIxs dataDef
            s      = dataSort dataDef

	-- If proof irrelevance is enabled we have to check that datatypes in
	-- Prop contain at most one element.
	do  proofIrr <- proofIrrelevance
	    case (proofIrr, s, cs) of
		(True, Prop, _:_:_) -> setCurrentRange (getRange $ map conName cs) $
                                        typeError PropMustBeSingleton
                  where conName (A.Axiom _ c _) = c
                        conName (A.ScopedDecl _ (d:_)) = conName d
                        conName _ = __IMPOSSIBLE__
		_		    -> return ()

	-- Add the datatype to the signature with its constructors. It was previously
	-- added without them.
	addConstant name (Defn name t (defaultDisplayForm name) 0 $
                            dataDef { dataCons = map cname cs }
			 )
        computePolarity name
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
checkConstructor :: QName -> Telescope -> Nat -> Sort
                 -> Induction -- ^ Is the constructor inductive or coinductive?
                 -> A.Constructor -> TCM ()
checkConstructor d tel nofIxs s ind (A.ScopedDecl scope [con]) = do
  setScope scope
  checkConstructor d tel nofIxs s ind con
checkConstructor d tel nofIxs s ind con@(A.Axiom i c e) =
    traceCall (CheckConstructor d tel s con) $ do
	t <- isType_ e
	n <- size <$> getContextTelescope
	verboseS "tc.data.con" 15 $ do
	    td <- prettyTCM t
	    liftIO $ UTF8.putStrLn $ "checking that " ++ show td ++ " ends in " ++ show d
	    liftIO $ UTF8.putStrLn $ "  nofPars = " ++ show n
	constructs n t d
	verboseS "tc.data.con" 15 $ do
	    d <- prettyTCM s
	    liftIO $ UTF8.putStrLn $ "checking that the type fits in " ++ show d
	t `fitsIn` s
	escapeContext (size tel)
	    $ addConstant c
	    $ Defn c (telePi tel t) (defaultDisplayForm c) 0
	    $ Constructor (size tel) c d Nothing (Info.defAbstract i) ind
checkConstructor _ _ _ _ _ _ = __IMPOSSIBLE__ -- constructors are axioms


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
		    | force d == q -> checkParams n =<< reduce (take nofPars vs)
						    -- we only check the parameters
		_ -> bad $ El s v

	bad t = typeError $ ShouldEndInApplicationOfTheDatatype t

	checkParams n vs = zipWithM_ sameVar (map unArg vs) ps
	    where
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
	    | d == force d' -> return $ El s0 t'
	    | otherwise	    -> fail $ "wrong datatype " ++ show d ++ " != " ++ show d'
	MetaV m vs	    -> do
	    Defn _ t _ _ Datatype{dataSort = s} <- getConstInfo d
	    ps <- newArgsMeta t
	    noConstraints $ equalType (El s0 t') (El s (Def (NotDelayed d) ps)) -- TODO: too strict?
	    reduce $ El s0 t'
	_ -> typeError $ ShouldBeApplicationOf (El s0 t) d

-- | Is the type coinductive? Returns 'Nothing' if the answer cannot
-- be determined.

isCoinductive :: MonadTCM tcm => Type -> tcm (Maybe Bool)
isCoinductive t = do
  El _ t <- normalise t
  case t of
    Def q _ -> do
      def <- getConstInfo (force q)
      case theDef def of
        Axiom       {} -> return (Just False)
        Function    {} -> return Nothing
        Datatype    { dataInduction = CoInductive } -> return (Just True)
        Datatype    { dataInduction = Inductive   } -> return (Just False)
        Record      {} -> return (Just False)
        Constructor {} -> __IMPOSSIBLE__
        Primitive   {} -> __IMPOSSIBLE__
    Var   {} -> return Nothing
    Lam   {} -> __IMPOSSIBLE__
    Lit   {} -> __IMPOSSIBLE__
    Con   {} -> __IMPOSSIBLE__
    Pi    {} -> return (Just False)
    Fun   {} -> return (Just False)
    Sort  {} -> return (Just False)
    MetaV {} -> return Nothing
