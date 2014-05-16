module Types.Definition
    ( -- * 'Clause'
      Clause(..)
    , ClauseBody
    , Pattern(..)
      -- * 'Definition'
    , Definition(..)
    , ConstantKind(..)
    ) where

import           Data.Void                        (Void)

import           Bound
import           Syntax.Abstract                  (Name)
import           Types.Term
import qualified Types.Telescope                  as Tel

-- Clauses
------------------------------------------------------------------------

type ClauseBody term = Scope (Named Int) term Void

-- | One clause of a function definition.
data Clause term = Clause [Pattern] (ClauseBody term)
    deriving (Eq)

data Pattern
    = VarP
    | ConP Name [Pattern]
    deriving (Eq)

-- Definition
------------------------------------------------------------------------

data Definition term
    = Constant Name ConstantKind (ClosedType term)
    | Constructor Name Name (Tel.ClosedIdTel term)
    -- ^ Constructor name, data type name, parameter context with
    -- resulting type.
    | Projection Name Field Name (Tel.ClosedIdTel term)
    -- ^ Projection name, field number, record type name, parameter
    -- context with resulting type.
    | Function Name (ClosedType term) [Clause term]

data ConstantKind = Postulate | Data | Record
  deriving (Eq, Show)
