{-# OPTIONS_GHC -cpp #-}

module TypeChecking.Monad.Open
	( makeOpen
	, getOpen
	) where

import Control.Applicative
import Control.Monad

import Syntax.Common

import TypeChecking.Substitute
import TypeChecking.Monad.Base
import TypeChecking.Monad.Context

#include "../../undefined.h"

-- | Create an open term in the current context.
makeOpen :: MonadTCM tcm => a -> tcm (Open a)
makeOpen x = do
    n <- length <$> getContextTelescope
    return $ OpenThing n x

-- | Create an open term which is closed.
makeClosed :: a -> Open a
makeClosed = OpenThing 0

-- | Extract the value from an open term. Must be done in an extension of the
--   context in which the term was created.
getOpen :: (MonadTCM tcm, Raise a) => Open a -> tcm a
getOpen (OpenThing 0 x) = return x
getOpen (OpenThing n x) = do
    m <- length <$> getContextTelescope
    unless (m >= n) $ __IMPOSSIBLE__
    return $ raise (m - n) x

