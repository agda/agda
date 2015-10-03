{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Converts Agda names to Haskell/Core names.
--
-- There are the following type of names in Agda:
-- - function names
-- - datatype names
-- - constructor names
--
-- All names in a Agda module are passed to the `assignCoreNames` function,
-- which will determine the Core name for each module-level Agda name.
--
-- At the moment, auto-generated names are used for all identifiers. Manual
-- forcing of a Core name is possible, but currently not used.
--
-- We also try to incorporate the original Agda name into the generated name
-- as far as possible.
--

module Agda.Compiler.UHC.Naming
  ( FreshNameT
  , evalFreshNameT
  , freshLocalName
  )
where

import Data.Char
import Data.List
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative

#if __GLASGOW_HASKELL__ <= 708
import Data.Monoid
#endif

import Data.Typeable (Typeable)

import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Monad

import Agda.Compiler.UHC.Bridge

#include "undefined.h"
import Agda.Utils.Impossible



------------------------------------
---- local fresh names
------------------------------------

newtype FreshNameT m a = FreshNameT
  { unFreshNameT :: StateT FreshNameState m a}
  deriving (Monad, MonadTrans, Functor, MonadFix, MonadPlus, MonadIO, Applicative, Alternative)

data FreshNameState
  = FreshNameState
  { fnNameSupply :: Integer
  , fnPrefix :: String    -- prefix to use
  }


evalFreshNameT :: Monad m
    => String    -- ^ The name prefix to use.
    -> FreshNameT m a
    -> m a
evalFreshNameT prefix comp = evalStateT (unFreshNameT comp) (FreshNameState 0 prefix)

freshLocalName :: Monad m => FreshNameT m HsName
freshLocalName = FreshNameT $ do
    i <- gets fnNameSupply
    prefix' <- gets fnPrefix
    modify (\s -> s { fnNameSupply = i + 1 } )
    return $ mkUniqueHsName prefix' [] ("gen_loc_" ++ show i)

instance MonadReader s m => MonadReader s (FreshNameT m) where
  ask = lift ask
  local f (FreshNameT x) = FreshNameT $ local f x

instance MonadState s m => MonadState s (FreshNameT m) where
  get = lift get
  put = lift . put

instance (MonadTCM tcm) => MonadTCM (FreshNameT tcm) where
  liftTCM = lift . liftTCM
