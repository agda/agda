{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Packaging.Monad where

{-
  ( module Control.Monad.Reader
  , AgdaPkg (..)
  , asksM ) where

-- Standard Library Imports
import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader

-- Local Imports
import Agda.Packaging.Config

--------------------------------------------------------------------------------

-- Parametric in `opt' only so that the environment can be decoupled
-- from the concrete CLI tool
newtype AgdaPkg opt a
  =     AgdaPkg
  { runAgdaPkg :: ReaderT (AgdaPkgConfig opt) IO a }
  deriving
    ( Functor
    , Monad
    , MonadError IOError
    , MonadReader (AgdaPkgConfig opt)
    , MonadIO )

instance Applicative (AgdaPkg opt) where
  pure  = return
  (<*>) = ap

asksM :: (MonadReader r m) => (r -> m a) -> m a
asksM = join . asks
-}
