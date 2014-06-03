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
import qualified Types.Telescope                  as Tel
import           Types.Var
import qualified Text.PrettyPrint.Extended        as PP

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

instance PP.Pretty Pattern where
  prettyPrec p e = case e of
    VarP      -> PP.text "_"
    ConP c es -> PP.prettyApp p (PP.pretty c) es

-- Definition
------------------------------------------------------------------------

data Definition term
    = Constant ConstantKind (Closed term)
    | Constructor Name (Tel.ClosedIdTel term)
    -- ^ Data type name, parameter context with resulting type.
    | Projection Field Name (Tel.ClosedIdTel term)
    -- ^ Field number, record type name, parameter context with resulting type.
    | Function (Closed term) [Clause term]

data ConstantKind
    = Postulate
    | Data [Name]                 -- Constructor list
    | Record Name [(Name, Field)] -- Constructor and projection list
  deriving (Eq, Show)

instance PP.Pretty ConstantKind where
  pretty = PP.text . show
