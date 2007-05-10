{-# OPTIONS -cpp #-}

module TypeChecking.Rules.Pattern where

import Control.Applicative
import Control.Monad.Trans

import qualified Syntax.Abstract as A
import Syntax.Internal
import Syntax.Common
import Syntax.Position
import Syntax.Translation.AbstractToConcrete
import Syntax.Info

import TypeChecking.Monad
import TypeChecking.Patterns.Monad
import TypeChecking.Pretty
import TypeChecking.Reduce
import TypeChecking.Conversion
import TypeChecking.Substitute
import TypeChecking.MetaVars
import TypeChecking.Constraints

import TypeChecking.Rules.Term ( checkLiteral, inferDef, forcePi )

#include "../../undefined.h"

-- | Check the patterns of a left-hand-side. Binds the variables of the pattern.
checkPatterns :: [NamedArg A.Pattern] -> Type -> CheckPatM r ([NamedArg A.Pattern], [Arg Pattern], [Arg Term], Type)
checkPatterns [] t =
    traceCall (CheckPatterns [] t) $ do
    t' <- instantiate t
    case funView $ unEl t' of
	FunV (Arg Hidden _) _   -> do
	    r <- getCurrentRange
	    checkPatterns [Arg Hidden $ unnamed $ A.ImplicitP $ PatRange r] t'
	_ -> return ([], [], [], t)

checkPatterns ps0@(Arg h np:ps) t =
    traceCall (CheckPatterns ps0 t) $ do

    -- Make sure the type is a function type
    (t', cs) <- forcePi h (name np) t
    opent'   <- makeOpen t'

    -- Add any resulting constraints to the global constraint set
    addNewConstraints cs

    -- If np is named then np = {x = p'}
    let p' = namedThing np

    -- We might have to insert wildcards for implicit arguments
    case funView $ unEl t' of

	-- There is a hidden argument missing here (either because the next
	-- pattern is non-hidden, or it's a named hidden pattern with the wrong name).
	-- Insert a {_} and re-type check.
	FunV (Arg Hidden _) _
	    | h == NotHidden ||
	      not (sameName (nameOf np) (nameInPi $ unEl t')) ->
	    checkPatterns (Arg Hidden (unnamed $ A.ImplicitP $ PatRange $ getRange np) : Arg h np : ps) t'

	-- No missing arguments.
	FunV (Arg h' a) _ | h == h' -> do

	    -- Check the first pattern
	    (p0, p, v) <- checkPattern h (argName t') p' a
	    openv      <- makeOpen v

	    -- We're now in an extended context so we have lift t' accordingly.
	    t0 <- getOpen opent'

	    -- Check the rest of the patterns. If the type of all the patterns were
	    -- (x : A)Δ, then we check the rest against Δ[v] where v is the
	    -- value of the first pattern (piApply (Γ -> B) vs == B[vs/Γ]).
	    (ps0, ps, vs, t'') <- checkPatterns ps (piApply t0 [Arg h' v])

	    -- Additional variables have been added to the context.
	    v' <- getOpen openv

	    -- Combine the results
	    return (Arg h (fmap (const p0) np) : ps0, Arg h p : ps, Arg h v':vs, t'')

	_ -> typeError $ WrongHidingInLHS t'
    where
	name (Named _ (A.VarP x)) = show x
	name (Named (Just x) _)   = x
	name _			  = "x"

	sameName Nothing _  = True
	sameName n1	 n2 = n1 == n2

	nameInPi (Pi _ b)  = Just $ absName b
	nameInPi (Fun _ _) = Nothing
	nameInPi _	   = __IMPOSSIBLE__


-- | Type check a pattern and bind the variables. First argument is a name
--   suggestion for wildcard patterns.
checkPattern :: Hiding -> String -> A.Pattern -> Type -> CheckPatM r (A.Pattern, Pattern, Term)
checkPattern h name p t =
    traceCall (CheckPattern name p t) $
    case p of

	-- Variable. Simply bind the variable.
	A.VarP x    -> do
	    bindPatternVar x (Arg h t)
	    return (p, VarP (show x), Var 0 [])

	-- Wild card. Create and bind a fresh name.
	A.WildP i   -> do
	    x <- freshName (getRange i) name
	    bindPatternVar x (Arg h t)
	    return (p, VarP name, Var 0 [])

	-- Implicit pattern. Create a new meta variable.
	A.ImplicitP i -> do
	    x <- addPatternMeta normalMetaPriority t
	    return (p, WildP, MetaV x [])

	-- Dot pattern. Create a meta variable.
	A.DotP i _ -> do
	    -- we should always instantiate dotted patterns first
	    x <- addPatternMeta highMetaPriority t
	    return (p, WildP, MetaV x [])

	-- Constructor. This is where the action is.
	A.ConP i c ps -> do

	    -- We're gonna need t in a different context so record the current
	    -- one.
	    ot <- makeOpen t

-- 	    (t', vs) <- do
-- 		-- Get the type of the constructor and the target datatype. The
-- 		-- type is the full lambda lifted type.
-- 		Defn _ t' (Constructor _ _ d _) <- getConstInfo c
-- 
-- 		-- Make sure that t is an application of the datatype to its
-- 		-- parameters (and some indices). This will include module
-- 		-- parameters.
-- 		Def d' _ <- reduce (Def d [])
-- 
-- 		verbose 10 $ do
-- 		  t <- prettyTCM t
-- 		  liftIO $ putStrLn $ "checking constructor " ++ show c ++
-- 				" of type " ++ show d ++ " (" ++ show d' ++ ")"
-- 		  liftIO $ putStrLn $ "  against type " ++ show t
-- 		  
-- 
-- 		El _ (Def _ vs)	<- forceData d' t
-- 
-- 		-- Get the number of parameters of the datatype, including
-- 		-- parameters to enclosing modules.
-- 		Datatype nofPars _ _ _ _ _ <- theDef <$> getConstInfo d
-- 
-- 		-- Throw away the indices
-- 		let vs' = take nofPars vs
-- 		return (t', vs')
-- 
-- 	    -- Compute the canonical form of the constructor (it might go
-- 	    -- through a lot of module instantiations).
-- 	    Con c' [] <- constructorForm =<< reduce (Con c [])

	    -- Infer the type of the constructor
	    (_, a) <- liftTCM $ inferDef Con c

	    Constructor n _ _ _ <- theDef <$> (instantiateDef =<< getConstInfo c)

	    liftTCM $ verbose 20 $ do
	      da  <- prettyTCM a
	      pds <- mapM pretty =<< mapM abstractToConcrete_ ps
	      liftIO $ putStrLn $ "checking pattern " ++ show c ++ " " ++ show pds
		      ++ "\n  type         " ++ show da
		      ++ "\n  nof pars     " ++ show n

	    -- Create meta variables for the parameters
	    a' <- let createMetas 0 a = return a
		      createMetas n a = do
			a <- reduce a
			case funView $ unEl a of
			  FunV (Arg h b) _ -> do
			    m <- newValueMeta b
			    createMetas (n - 1) (a `piApply` [Arg h m])
			  _   -> do
			    d <- prettyTCM a
			    fail $ show d ++ " should have had " ++ show n ++ " more arguments"
			    __IMPOSSIBLE__
		  in  createMetas n a

	    liftTCM $ verbose 20 $ do
	      da' <- prettyTCM a'
	      liftIO $ putStrLn $ "  instantiated " ++ show da'


	    -- Check the arguments against that type
	    (aps, ps', ts', rest) <- checkPatterns ps a' -- (piApply t' vs)

	    -- Compute the corresponding value (possibly blocked by constraints)
	    v <- do
		tn  <- getOpen ot
		blockTerm tn (Con c ts') $ equalType rest tn

	    -- Get the canonical name for the constructor
	    Constructor _ c' _ _ <- theDef <$> getConstInfo c

	    return (A.ConP i c' aps, ConP c' ps', v)
	    where
		hide (Arg _ x) = Arg Hidden x

	-- Absurd pattern. Make sure that the type is empty. Otherwise treat as
	-- an anonymous variable.
	A.AbsurdP i -> do
	    thisTypeShouldBeEmpty t
	    x <- freshName (getRange i) name
	    bindPatternVar x (Arg h t)
	    return (p, AbsurdP, Var 0 [])

	-- As pattern. Create a let binding for the term corresponding to the
	-- pattern.
	A.AsP i x p -> do
	    ot	       <- makeOpen t
	    (p0, p, v) <- checkPattern h name p t
	    t	       <- getOpen ot
	    verbose 15 $ do
		dt <- prettyTCM t
		dv <- prettyTCM v
		dctx <- prettyTCM =<< getContext
		liftIO $ putStrLn $ show dctx ++ " |-"
		liftIO $ putStrLn $ "  " ++ show x ++ " : " ++ show dt
		liftIO $ putStrLn $ "  " ++ show x ++ " = " ++ show dv
	    liftPatCPS_ (addLetBinding x v t)
	    return (A.AsP i x p0, p, v)

	-- Literal.
	A.LitP l    -> do
	    v <- liftTCM $ checkLiteral l t
	    return (p, LitP l, v)

	-- Defined patterns are not implemented.
	A.DefP i f ps ->
	    typeError $ NotImplemented "defined patterns"


