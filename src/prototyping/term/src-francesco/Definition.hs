module Definition
    ( -- * 'Clause'
      Clause(..)
    , Pattern(..)
      -- * 'Definition'
    , Definition(..)
    , ConstantKind(..)
    ) where

import           Syntax.Abstract                  (Name)
import           Term

-- Clauses
------------------------------------------------------------------------

-- | One clause of a function definition.
data Clause clauseBody = Clause [Pattern] clauseBody
    deriving (Eq, Ord)

data Pattern
    = VarP
    | ConP Name [Pattern]
    deriving (Eq, Ord)

-- Definition
------------------------------------------------------------------------

data Definition type_ clauseBody ctx
    = Constant Name ConstantKind type_
    | Constructor Name Name ctx
    -- ^ Constructor name, data type name, parameter context with
    -- resulting type.
    | Projection Name Field Name ctx
    -- ^ Projection name, field number, record type name, parameter
    -- context with resulting type.
    | Function Name type_ [Clause clauseBody]

data ConstantKind = Postulate | Data | Record
  deriving Show
