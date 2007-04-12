{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| Classify type familes and constants
-}

module Compiler.Agate.Classify where

import Compiler.Agate.TranslateName
import TypeChecking.MetaVars

import Data.Map (Map)
import qualified Data.Map as Map

import TypeChecking.Monad
import Syntax.Abstract.Name

----------------------------------------------------------------

enumDatatypes :: Map QName Definition -> [QName]
enumDatatypes definitions = do
	let ndefs = Map.toList definitions
	concatMap f ndefs
	where
	f (name,d) = 
		let def = theDef d in
		case def of
			Datatype np ni cs s a -> [name]
			_ -> []

enumCompilableDatatypes :: Map QName Definition -> [QName] -> TCM [QName]
enumCompilableDatatypes definitions names = do
	computeGreatestFixedPoint f names
	where
	f :: [QName] -> QName -> TCM Bool
	f names name = return True -- All datatypes are compilable at the moment
	-- TODO: implement correctly

----------------------------------------------------------------


enumOptimizableConstants :: Map QName Definition -> [QName] -> TCM [QName]
enumOptimizableConstants definitions names = do
	computeGreatestFixedPoint f names
	where
	f :: [QName] -> QName -> TCM Bool
	f names name = return True -- All constants are optimized at the moment
	-- TODO: implement correctly


--

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
	    
