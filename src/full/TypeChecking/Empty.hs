
module TypeChecking.Empty where

import Control.Monad
import Control.Monad.Trans

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Errors
import TypeChecking.Primitive
import Utils.Function

-- | Make sure that a type is empty.
isEmptyType :: MonadTCM tcm => Type -> tcm ()
isEmptyType t = do
    t <- reduce t
    case t of
	El _ (Def d vs) -> do
	    Defn _ _ di <- getConstInfo d
	    case di of
		-- No constructors
		Datatype _ _ [] _ _		    -> return ()

		-- Inductive family. Check that the type at the given index is
		-- uninhabited.
		Datatype nPs nIxs cs _ _ | nIxs > 0 -> do
		    ixs <- normalise $ map unArg $ drop nPs vs
		    verbose 10 $ do
			ds <- mapM prettyTCM ixs
			liftIO $ putStrLn $ "empty inductive family?"
			liftIO $ putStrLn $ "nIxs = " ++ show nIxs
			liftIO $ print ds
		    mapM_ (impossibleConstr t ixs) cs

		-- Otherwise, it's not empty
		_ -> notEmpty t
	_ -> notEmpty t

notEmpty :: MonadTCM tcm => Type -> tcm a
notEmpty t = typeError $ ShouldBeEmpty t

-- | Make sure that a constructor cannot produce an element at the given index.
impossibleConstr :: MonadTCM tcm => Type -> [Term] -> QName -> tcm ()
impossibleConstr a ixs c = do
    reportLn 10 $ "impossible constructor " ++ show c ++ " ?"
    t <- normalise =<< typeOfConst c
    let Def _ vs = stripPi $ unEl t
	ixs'	 = map unArg $ reverse $ zipWith const (reverse vs) ixs
    zipWithM_ (distinct a) ixs ixs'
    where
	stripPi t = case t of
	    Pi _ b  -> stripPi $ unEl $ absBody b
	    Fun _ b -> stripPi $ unEl b
	    _	    -> t

-- | Make sure that two terms are distinct under any substitution.
--   Invariant: The terms should be on normal form.
distinct :: MonadTCM tcm => Type -> Term -> Term -> tcm ()
distinct a u v = do
    u <- constructorForm u
    v <- constructorForm v
    case (u, v) of
	(Con c us, Con c' vs)
	    | c /= c'	-> return ()
	    | otherwise	-> (zipWithM_ (distinct a) `on` map unArg) us vs
	_ -> notEmpty a

