-- {-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Open
        ( makeOpen
        , makeClosed, isClosed
        , getOpen
        , tryOpen
        ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import qualified Data.List as List

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Base

import {-# SOURCE #-} Agda.TypeChecking.Monad.Context

import Agda.Utils.Except ( MonadError(catchError) )

-- | Create an open term in the current context.
makeOpen :: a -> TCM (Open a)
makeOpen x = do
    ctx <- getContextId
    return $ OpenThing ctx x

-- | Create an open term which is closed.
makeClosed :: a -> Open a
makeClosed = OpenThing []

-- | Check if an 'Open' is closed.
isClosed :: Open a -> Bool
isClosed (OpenThing cxt _) = null cxt

-- | Extract the value from an open term. Must be done in an extension of the
--   context in which the term was created.
getOpen :: (Subst t a, MonadReader TCEnv m) => Open a -> m a
getOpen (OpenThing []  x) = return x
getOpen (OpenThing ctx x) = do
  ctx' <- getContextId
  unless (ctx `List.isSuffixOf` ctx') $ fail $ "thing out of context (" ++ show ctx ++ " is not a sub context of " ++ show ctx' ++ ")"
  return $ raise (length ctx' - length ctx) x

-- | Try to use an 'Open' the current context.
--   Returns 'Nothing' if current context is not an extension of the
--   context in which the 'Open' was created.
tryOpen :: (Subst t a, MonadReader TCEnv m) => Open a -> m (Maybe a)
tryOpen (OpenThing []  x) = return $ Just x
tryOpen (OpenThing ctx x) = do
  ctx' <- getContextId
  if (ctx `List.isSuffixOf` ctx')
    then return $ Just $ raise (length ctx' - length ctx) x
    else return Nothing
