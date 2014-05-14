module Impl.Definition
    ( -- * 'Clause'
      Clause
    , ClauseBody
    , Definition.Pattern(..)
      -- * 'Definition'
    , Definition
    , Definition.ConstantKind(..)
    ) where

import           Bound
import           Data.Void                        (Void)

import qualified Definition
import           Term
import           Impl.Term
import           Impl.Telescope

type Clause = Definition.Clause ClauseBody

type ClauseBody = Scope (Named Int) Term Void

type Definition =
    Definition.Definition ClosedType (ClosedTelescope Type) Field ClauseBody
