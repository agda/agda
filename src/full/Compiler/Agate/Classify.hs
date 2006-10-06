{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| Classify type familes and constants
-}

module Compiler.Agate.Classify where

import Compiler.Agate.TranslateName
import TypeChecking.MetaVars

import qualified Data.Map as Map

import TypeChecking.Monad
import Syntax.Abstract.Name

----------------------------------------------------------------

enumDatatypes :: Definitions -> [Name]
enumDatatypes definitions = do
	let ndefs = Map.toList definitions
	concatMap f ndefs
	where
	f (name,d) = 
		let def = theDef d in
		case def of
			(Datatype np cs s a) -> [name]
			_ -> []

enumCompilableDatatypes :: Definitions -> [Name] -> TCM [Name]
enumCompilableDatatypes definitions names = do
	computeGreatestFixedPoint f names
	where
	f :: [Name] -> Name -> TCM Bool
	f names name = return True -- All datatypes are compilable at the moment
	-- TODO: implement correctly

----------------------------------------------------------------


enumOptimizableConstants :: Definitions -> [Name] -> TCM [Name]
enumOptimizableConstants definitions names = do
	computeGreatestFixedPoint f names
	where
	f :: [Name] -> Name -> TCM Bool
	f names name = return True -- All constants are optimized at the moment
	-- TODO: implement correctly


--

computeGreatestFixedPoint :: ([Name] -> Name -> TCM Bool)-> [Name] -> TCM [Name]
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

computeLeastFixedPoint :: ([Name] -> Name -> TCM Bool) -> [Name] -> TCM [Name]
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
	    
