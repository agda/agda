{-# OPTIONS -fglasgow-exts #-}

{-| Some common syntactic entities are defined in this module.
-}
module Syntax.Common where

import Data.Generics (Typeable, Data)

data Hiding  = Hidden | NotHidden
    deriving (Typeable, Data, Show, Eq)

-- | A function argument can be hidden.
data Arg e  = Arg Hiding e
    deriving (Typeable, Data, Eq)

instance Show a => Show (Arg a) where
    show (Arg Hidden x) = "{" ++ show x ++ "}"
    show (Arg NotHidden x) = "(" ++ show x ++ ")"

-- | Functions can be defined in both infix and prefix style. See
--   'Syntax.Concrete.LHS'.
data IsInfix = InfixDef | PrefixDef
    deriving (Typeable, Data, Show, Eq)

-- | Access modifier.
data Access = PrivateAccess | PublicAccess
    deriving (Typeable, Data, Show, Eq)

-- | Abstract or concrete
data IsAbstract = AbstractDef | ConcreteDef
    deriving (Typeable, Data, Show, Eq)

type Nat    = Int
type Arity  = Nat

