{-# OPTIONS -cpp -fglasgow-exts #-}

module TypeChecking.Monad.Name where

import Control.Monad.Reader
import Control.Monad.State

import Utils.Monad
import Utils.Fresh

import Syntax.Common
import Syntax.Position
import Syntax.Concrete.Name as CN
import Syntax.Abstract.Name as AN

import TypeChecking.Monad

#include "../../undefined.h"


-- | Generate a fresh unique identifier for a name
refreshName :: Range -> String -> TCM AN.Name
refreshName r s = do
    i <- fresh
    let x = parseName s
    return $ AN.Name i (CN.Name r x)
    where
	parseName :: String -> [NamePart]
	parseName []	  = []
	parseName ('_':s) = Hole : parseName s
	parseName s	  = case break (== '_') s of
	    (s0, s1) -> Id s0 : parseName s1

refreshName_ :: String -> TCM AN.Name
refreshName_ = refreshName noRange

