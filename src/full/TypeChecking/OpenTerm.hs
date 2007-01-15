{-# OPTIONS_GHC -cpp #-}

module TypeChecking.OpenTerm
	( OpenTerm
	, makeOpenTerm
	, getOpenTerm
	) where

import Control.Applicative
import Control.Monad

import Syntax.Common

import TypeChecking.Substitute
import TypeChecking.Monad

#include "../undefined.h"

-- | A value tagged with the number of free variables
data OpenTerm a = OpenTerm Nat a

-- | Create an open term in the current context.
makeOpenTerm :: a -> TCM (OpenTerm a)
makeOpenTerm x = do
    n <- length <$> getContextTelescope
    return $ OpenTerm n x

-- | Extract the value from an open term. Must be done in an extension of the
--   context in which the term was created.
getOpenTerm :: Raise a => OpenTerm a -> TCM a
getOpenTerm (OpenTerm n x) = do
    m <- length <$> getContextTelescope
    unless (m >= n) $ __IMPOSSIBLE__
    return $ raise (m - n) x

