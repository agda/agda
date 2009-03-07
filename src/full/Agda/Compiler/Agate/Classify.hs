{-# LANGUAGE CPP #-}

{-| Classify type familes and constants
    TODO: optimize by getting rid of !'s
-}

module Agda.Compiler.Agate.Classify where

#include "../../undefined.h"
import Agda.Utils.Impossible

import Agda.Compiler.Agate.TranslateName
import Agda.Compiler.Agate.Common

import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Abstract.Name

import Data.Map ((!), Map)
import qualified Data.Map as Map

import Control.Monad
import Agda.Utils.Monad

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM f xs = liftM and $ mapM f xs

andM :: Monad m => m Bool -> m Bool -> m Bool
andM x y = ifM x y $ return False

----------------------------------------------------------------

enumTypeFamilies :: Map QName Definition -> TCM [QName]
enumTypeFamilies definitions = fmap concat $ mapM f $ Map.toList definitions
    where
      f (name,d) = do
	--let def = theDef d
	let ty = defType d
	(_,ty2) <- splitType ty
	(El sort term) <- reduce ty2
	case term of
	    Sort _ -> return [name]
	    _      -> return []

enumCompilableTypeFamilies :: Map QName Definition -> TCM [QName]
enumCompilableTypeFamilies definitions = do
    names <- enumTypeFamilies definitions
    computeGreatestFixedPoint f names where
    f :: [QName] -> QName -> TCM Bool
    f names name = do
	let d = definitions ! name
	let def = theDef d
	case def of
	    Axiom{}                                       -> return False -- IO should get True
	    Primitive{}                                   -> return False -- String should get True
	    Function{funClauses = []}                     -> __IMPOSSIBLE__
	    Function{funClauses = [Clause{ clauseBody = NoBody }]}  -> return False
	    Function{funClauses = [Clause{}]}             -> return False -- TODO
	    Function{}                                    -> return False
	    Constructor{}                                 -> return False -- ctor is not a typefam
	    Datatype{dataCons = cnames} -> do
	    	ty <- instantiate $ defType d
	    	andM (isCompilableType ty) $
	    	    allM ( \cname ->
	    	             do let d = definitions ! cname
			    	ty <- instantiate $ defType d
				isCompilableType ty ) cnames
	    Record{} -> return True
	where -- TODO: implement correctly
--	isCompilableType (El s tm) = isCompilableTypeFamily tm
	
	isCompilableType :: Type -> TCM Bool
	isCompilableType (El s tm) = isCompilableTypeFamily tm
	
	isCompilableTypeFamily :: Term -> TCM Bool
	isCompilableTypeFamily tm = do
	    tm <- reduce tm
	    case tm of
		Var n args -> allM (isCompilableTypeFamily . unArg) args
		Sort _     -> return True
		Lam h abs  -> return False -- this can be too strong
		Def c args -> andM (return $ elem (force c) names) $
		    allM (isCompilableTypeFamily . unArg) args
		Pi arg abs -> andM (isCompilableType $ unArg arg) $
		    underAbstraction_ abs isCompilableType
		Fun arg ty -> andM (isCompilableType $ unArg arg) $
		    isCompilableType ty
		Lit lit    -> return False
		Con c args -> return False
		MetaV _ _  -> return __IMPOSSIBLE__

----------------------------------------------------------------

enumOptimizableConstants :: Map QName Definition -> [QName] -> TCM [QName]
enumOptimizableConstants definitions names = do
	computeGreatestFixedPoint f names
	where
	f :: [QName] -> QName -> TCM Bool
	f names name = return True -- All constants are optimized at the moment
	-- TODO: implement correctly


----------------------------------------------------------------

computeGreatestFixedPoint :: ([QName] -> QName -> TCM Bool)-> [QName] -> TCM [QName]
computeGreatestFixedPoint f names = go names True where
    go names False = return names
    go names True  = go2 names names [] False
    go2 keptNames []           namesNext changed = go namesNext changed
    go2 keptNames (name:names) namesNext changed = do
	b <- f keptNames name
	case b of
	    True  -> go2 keptNames names (name : namesNext) changed
	    -- name is kept
	    False -> go2 keptNames names namesNext True
	    -- name is removed

computeLeastFixedPoint :: ([QName] -> QName -> TCM Bool) -> [QName] -> TCM [QName]
computeLeastFixedPoint f names = go names [] True where
    go names grantedNames False = return grantedNames
    go names grantedNames True  = go2 names [] grantedNames False
    go2 []           namesNext grantedNames changed =
	go namesNext grantedNames changed
    go2 (name:names) namesNext grantedNames changed = do
	b <- f grantedNames name 
	case b of
	    True  -> go2 names namesNext (name : grantedNames) True
	    -- name is granted to be okay
	    False -> go2 names (name : namesNext) grantedNames changed
	    -- name is unsettled

--
	    
