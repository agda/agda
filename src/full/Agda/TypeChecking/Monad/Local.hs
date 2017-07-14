{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Monad.Local where

import Control.Applicative
import Control.Monad
import Data.Monoid

import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Free
import {-# SOURCE #-} Agda.TypeChecking.Monad.Signature (inFreshModuleIfFreeParams, lookupSection)

import Agda.Utils.Size
import Agda.Utils.Impossible
#include "undefined.h"

-- | Precondition: must not be called if the module parameter of the current
--   module have been refined or (touched at all).
makeLocal :: Free a => a -> TCM (Local a)
makeLocal x | closed x = return $ Global x
            | otherwise = inFreshModuleIfFreeParams $ do
  m <- currentModule
  return (Local m x)

makeGlobal :: Free a => a -> TCM (Local a)
makeGlobal x | closed x  = return $ Global x
             | otherwise = __IMPOSSIBLE__

getLocal :: Subst Term a => Local a -> TCM (Maybe a)
getLocal (Global x) = return (Just x)
getLocal l@(Local m x) = do
  m' <- currentModule
  if m' == m || isSubModuleOf m' m
    then Just . (`applySubst` x) <$> getModuleParameterSub m
    else return Nothing

