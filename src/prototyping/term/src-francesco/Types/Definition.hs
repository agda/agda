module Types.Definition
    ( -- * 'Clause'
      Clause(..)
    , ClauseBody
    , Pattern(..)
      -- * 'Definition'
    , Definition(..)
    , ConstantKind(..)
    , Injectivity(..)
    ) where

import           Bound
import           Data.Typeable                    (Typeable)
import           Data.Monoid                      (Monoid, mappend, mempty)

import           Syntax.Abstract                  (Name)
import qualified Types.Telescope                  as Tel
import           Types.Var
import qualified Text.PrettyPrint.Extended        as PP

-- Clauses
------------------------------------------------------------------------

type ClauseBody t v = Scope (Named Int) t v

-- | One clause of a function definition.
data Clause t v = Clause [Pattern] (ClauseBody t v)
    deriving (Eq, Typeable)

instance Bound Clause where
  Clause pats body >>>= f = Clause pats (body >>>= f)

data Pattern
    = VarP
    | ConP Name [Pattern]
    deriving (Eq, Show)

instance PP.Pretty Pattern where
  prettyPrec p e = case e of
    VarP      -> PP.text "_"
    ConP c es -> PP.prettyApp p (PP.pretty c) es

-- Definition
------------------------------------------------------------------------

data Definition t v
    = Constant ConstantKind (t v)
    | Constructor Name (Tel.IdTel t v)
    -- ^ Data type name, parameter context with resulting type.
    | Projection Field Name (Tel.IdTel t v)
    -- ^ Field number, record type name, parameter context with resulting type.
    | Function (t v) Injectivity [Clause t v]
    deriving (Typeable)

instance Bound Definition where
  Constant kind t              >>>= f = Constant kind (t >>= f)
  Constructor tyCon type_      >>>= f = Constructor tyCon (type_ >>>= f)
  Projection field tyCon type_ >>>= f = Projection field tyCon (type_ >>>= f)
  Function type_ inj clauses   >>>= f = Function (type_ >>= f) inj (map (>>>= f) clauses)

data ConstantKind
    = Postulate
    | Data [Name]                 -- Constructor list
    | Record Name [(Name, Field)] -- Constructor and projection list
  deriving (Eq, Show, Typeable)

data Injectivity = Injective | NotInjective
  deriving (Eq, Show, Typeable)

instance Monoid Injectivity where
  mempty = Injective

  NotInjective `mappend` _            = NotInjective
  _            `mappend` NotInjective = NotInjective
  _            `mappend` _            = Injective

instance PP.Pretty ConstantKind where
  pretty = PP.text . show
