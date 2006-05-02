{-# OPTIONS -fglasgow-exts #-}

{-| Some common syntactic entities are defined in this module.
-}
module Syntax.Common where

import Data.Generics (Typeable, Data)

data Hiding  = Hidden | NotHidden
    deriving (Typeable, Data, Show, Eq)

-- | A function argument can be hidden.
data Arg e  = Arg Hiding e
    deriving (Typeable, Data, Show, Eq)

-- | Functions can be defined in both infix and prefix style. See
--   'Syntax.Concrete.LHS'.
data IsInfix = InfixDef | PrefixDef
    deriving (Typeable, Data, Show, Eq)

-- | Access modifier.
data Access = PrivateAccess | PublicAccess
    deriving (Typeable, Data, Show, Eq)

type Nat    = Int
type Arity  = Nat

