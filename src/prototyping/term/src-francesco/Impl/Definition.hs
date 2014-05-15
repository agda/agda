module Impl.Definition
    ( -- * 'Clause'
      TermClause
    , ClauseBody
      -- * 'Definition'
    , TermDefinition
    ) where

import           Bound
import           Data.Void                        (Void)

import           Definition
import           Term
import           Impl.Term
import qualified Impl.Context                     as Ctx

type TermClause = Clause ClauseBody

type ClauseBody = Scope (Named Int) Term Void

type TermDefinition =
    Definition ClosedType ClauseBody (Ctx.ClosedTelescope Type)
