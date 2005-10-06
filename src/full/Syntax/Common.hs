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

data Name = Name Range String
    deriving (Typeable, Data, Show)

-- | Define equality on @Name@ to ignore range so same names in different
--     locations are equal.
--
--   Is there a reason not to do this? -Jeff
--
instance Eq Name where
    (Name _ x) == (Name _ y) = x == y

-- | @QName@ is a list of namespaces and the name of the constant.
--   For the moment assumes namespaces are just NameID and not
--     explicitly applied modules.
--   Also assumes namespaces are generative by just using derived
--     equality. We will have to define an equality instance to
--     non-generative namespaces (as well as having some sort of
--     lookup table for namespace names).
--
-- data QName = Qual Name QName
--            | QName Name 
--   deriving (Typeable, Data, Show, Eq)

-- Ulf's version of QName

-- | A name can be qualified by a name space. Name spaces are hierarchical
--   so we use a list of strings to represent them.
data QName = QName [String] Name
    deriving (Typeable, Data, Eq, Show)

--


type Nat = Int


data Literal = LitInt Range Integer
	     | LitFloat Range Double
	     | LitString Range String
	     | LitChar Range Char
    deriving (Typeable, Data, Eq, Show)


-- | Explanations should contain enough information to 
--   reconstruct a derivation
--
data Expl = InCode Range
	  | DefinedAt Range
	  | Expl :+: Expl
	  | Duh -- ^ this is a default for development which should disappear
  deriving (Typeable, Data, Show)

instance HasRange Expl where
    getRange (InCode r) = r
    getRange (DefinedAt r) = r
    getRange (ex1 :+: ex2) = fuseRange ex1 ex2
    getRange Duh = noRange

instance HasRange Name where
    getRange (Name r _)	    = r

instance HasRange QName where
    getRange (QName _ x)    = getRange x

instance HasRange Literal where
    getRange (LitInt r _)	= r
    getRange (LitFloat r _)	= r
    getRange (LitString r _)	= r
    getRange (LitChar r _)	= r

