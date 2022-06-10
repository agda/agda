{-# LANGUAGE KindSignatures #-}

module Agda.TypeChecking.Heterogeneous where

import Data.Data (Data, Typeable)
import Data.Sequence (Seq)

import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base

import Agda.Utils.Size (Sized)

drop :: Int -> ContextHet -> ContextHet
length :: ContextHet -> Int
(!!!) :: ContextHet -> Int -> Maybe (Dom (Name, TwinT))
