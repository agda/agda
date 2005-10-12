{-# OPTIONS -fglasgow-exts #-}

{-| Some common syntactic entities are defined in this module.
-}
module Syntax.Common where

import Data.Generics

import Syntax.Position

data Hiding  = Hidden | NotHidden
    deriving (Typeable, Data, Show, Eq)

-- | Functions can be defined in both infix and prefix style. See
--   'Syntax.Concrete.LHS'.
data IsInfix = InfixDef | PrefixDef
    deriving (Typeable, Data, Show, Eq)

-- | Access modifier.
data Access = PrivateDecl | PublicDecl
    deriving (Typeable, Data, Show, Eq)

-- | Equality and ordering on @Name@ are defined to ignore range so same names
--   in different locations are equal.
data Name = Name Range String
    deriving (Typeable, Data)

instance Eq Name where
    (Name _ x) == (Name _ y) = x == y

instance Ord Name where
    compare (Name _ x) (Name _ y) = compare x y


instance Show Name where
    show (Name _ x) = x

-- | @QName@ is a list of namespaces and the name of the constant.
--   For the moment assumes namespaces are just NameID and not
--     explicitly applied modules.
--   Also assumes namespaces are generative by just using derived
--     equality. We will have to define an equality instance to
--     non-generative namespaces (as well as having some sort of
--     lookup table for namespace names).
data QName = Qual Name QName
           | QName Name 
  deriving (Typeable, Data, Show, Eq)


type Nat = Int


data Literal = LitInt Range Integer
	     | LitFloat Range Double
	     | LitString Range String
	     | LitChar Range Char
    deriving (Typeable, Data, Eq, Show)


instance HasRange Name where
    getRange (Name r _)	= r

instance HasRange QName where
    getRange (QName x)  = getRange x
    getRange (Qual n x)	= fuseRange n x

instance HasRange Literal where
    getRange (LitInt r _)	= r
    getRange (LitFloat r _)	= r
    getRange (LitString r _)	= r
    getRange (LitChar r _)	= r

