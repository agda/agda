{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| Classify type familes and constants
    TODO: optimize by getting rid of !'s
-}

module Compiler.Agate.Classify where

import Compiler.Agate.TranslateName
import Compiler.Agate.Common

import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Monad

import Syntax.Common
import Syntax.Internal
import Syntax.Abstract.Name

import Data.Map ((!), Map)
import qualified Data.Map as Map


----------------------------------------------------------------

enumTypeFamilies :: Map QName Definition -> TCM [QName]
enumTypeFamilies definitions = fmap concat $ mapM f $ Map.toList definitions
    where
      f (name,d) = do
	--let def = theDef d
	let ty = defType d
	(_,ty2) <- splitType ty
	(El sort term) <- reduce ty2
	case ignoreBlocking term of
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
	    Axiom                        -> return False -- IO should get True
	    Primitive a pf _             -> return False -- String should get True
	    Function [] a                -> return False -- __IMPOSSIBLE__
	    Function clauses a           -> return False -- TODO
	    Constructor np _ tname a     -> return False -- ctor is not a typefam
	    Datatype np ni _ cnames s a  -> do
	    	let ty = defType d
	    	ty <- reduce ty
	    	ok <- isCompilableType ty
	    	if ok then return True {-(
	    	  fmap and (mapM ( \cname ->
	    	      (do
	    	  	let d = definitions ! cname
	    	  	ty <- defType d
	    	  	isCompilableType ty)) cnames ))
	    	 -} else return False
	    Record np claus flds tel s a -> return True
	where -- TODO: implement correctly
	isCompilableType :: Type -> TCM Bool
	isCompilableType (El s t) = isCompilableTypeFamily t
	
	isCompilableTypeFamily :: Term -> TCM Bool
	isCompilableTypeFamily tm = do
	    tm <- reduce tm
	    case ignoreBlocking tm of
		Var n args -> return True
		Sort _     -> return True
		Lam h abs  -> return False -- this can be too strong
		Def c args ->
		    if elem c names then
			fmap and $ mapM (isCompilableTypeFamily . unArg) args
		      else return False
		Pi arg abs -> do
		    ok <- isCompilableType $ unArg arg
		    if ok then underAbstraction_ abs isCompilableType
		      else return False
		Fun arg ty -> do
		    ok <- isCompilableType $ unArg arg
		    if ok then isCompilableType ty
		      else return False
		Lit lit    -> return False
		Con c args -> return False
		MetaV _ _  -> return __IMPOSSIBLE__
		BlockedV _ -> return __IMPOSSIBLE__
    
    
    
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
	    
