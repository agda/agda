{-# OPTIONS_GHC -cpp #-}

module TypeChecking.Monad.Open
	( makeOpen
	, makeClosed
	, getOpen
	, tryOpen
	) where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Data.List

import Syntax.Common

import TypeChecking.Substitute
import TypeChecking.Monad.Base

#ifndef __HADDOCK__
import {-# SOURCE #-} TypeChecking.Monad.Context
#endif

#include "../../undefined.h"

-- | Create an open term in the current context.
makeOpen :: MonadTCM tcm => a -> tcm (Open a)
makeOpen x = do
    ctx <- getContextId
    return $ OpenThing ctx x

-- | Create an open term which is closed.
makeClosed :: a -> Open a
makeClosed = OpenThing []


-- | Extract the value from an open term. Must be done in an extension of the
--   context in which the term was created.
getOpen :: (MonadTCM tcm, Raise a) => Open a -> tcm a
getOpen (OpenThing []  x) = return x
getOpen (OpenThing ctx x) = do
  ctx' <- getContextId
  unless (ctx `isPrefixOf` ctx') $ fail $ "thing out of context (" ++ show ctx ++ " not prefix of " ++ show ctx' ++ ")"
  return $ raise (length ctx' - length ctx) x

tryOpen :: (MonadTCM tcm, Raise a) => Open a -> tcm (Maybe a)
tryOpen o = liftTCM $
  (Just <$> getOpen o)
  `catchError` \_ -> return Nothing

