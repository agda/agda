module Definition
    ( -- * 'Clause'
      Clause(..)
    , Pattern(..)
      -- * 'Definition'
    , Definition(..)
    , ConstantKind(..)
    ) where

import           Syntax.Abstract                  (Name)

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

data Definition type_ tele field clauseBody
    = Constant Name ConstantKind type_
    | Constructor Name Name tele
    -- ^ Constructor name, data type name, parameter telescope.
    | Projection Name field Name tele
    -- ^ Projection name, field number, record type name, parameter
    -- telescope.
    | Function Name type_ [Clause clauseBody]

data ConstantKind = Postulate | Data | Record
  deriving Show
