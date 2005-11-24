{-# OPTIONS -fglasgow-exts #-}

{-| Some common syntactic entities are defined in this module.
-}
module Syntax.Common where

import Data.Generics hiding (Fixity, GT)

import Syntax.Position

data Hiding  = Hidden | NotHidden
    deriving (Typeable, Data, Show, Eq)

-- | Functions can be defined in both infix and prefix style. See
--   'Syntax.Concrete.LHS'.
data IsInfix = InfixDef | PrefixDef
    deriving (Typeable, Data, Show, Eq)

-- | Access modifier.
data Access = PrivateAccess | PublicAccess
    deriving (Typeable, Data, Show, Eq)

-- | Equality and ordering on @Name@ are defined to ignore range so same names
--   in different locations are equal.
data Name = Name Range String
	  | NoName Range	-- ^ instead of @Name r \"_\"@
    deriving (Typeable, Data)

-- | @noName = 'NoName' 'noRange'@
noName :: Name
noName = NoName noRange

-- | @qualify "A.B" "x" == "A.B.x"@
qualify :: QName -> Name -> QName
qualify (QName m) x	= Qual m (QName x)
qualify (Qual m m') x	= Qual m $ qualify m' x

-- Define equality on @Name@ to ignore range so same names in different
--     locations are equal.
--
--   Is there a reason not to do this? -Jeff
--
--   No. But there are tons of reasons to do it. For instance, when using
--   names as keys in maps you really don't want to have to get the range
--   right to be able to do a lookup. -Ulf

instance Eq Name where
    (Name _ x) == (Name _ y) = x == y
    (NoName _) == (NoName _) = True	-- we really shouldn't compare NoNames...
    _ == _  = False

instance Ord Name where
    compare (Name _ x) (Name _ y) = compare x y
    compare (NoName _) (Name _ _) = LT
    compare (Name _ _) (NoName _) = GT
    compare (NoName _) (NoName _) = EQ


-- | @QName@ is a list of namespaces and the name of the constant.
--   For the moment assumes namespaces are just @Name@s and not
--     explicitly applied modules.
--   Also assumes namespaces are generative by just using derived
--     equality. We will have to define an equality instance to
--     non-generative namespaces (as well as having some sort of
--     lookup table for namespace names).
data QName = Qual  Name QName
           | QName Name 
  deriving (Typeable, Data, Eq)


instance Show Name where
    show (Name _ x) = x
    show (NoName _) = "_"

instance Show QName where
    show (Qual m x) = show m ++ "." ++ show x
    show (QName x)  = show x


type Nat    = Int
type Arity  = Nat

data Literal = LitInt    Range Integer
	     | LitFloat  Range Double
	     | LitString Range String
	     | LitChar   Range Char
    deriving (Typeable, Data, Eq, Show)


-- | Fixity of infix operators.
data Fixity = LeftAssoc  Range Int
	    | RightAssoc Range Int
	    | NonAssoc   Range Int
    deriving (Typeable, Data, Eq, Show)

-- | The default fixity. Currently defined to be @'LeftAssoc' 20@.
defaultFixity :: Fixity
defaultFixity = LeftAssoc noRange 20


instance HasRange Name where
    getRange (Name r _)	= r
    getRange (NoName r)	= r

instance HasRange QName where
    getRange (QName  x) = getRange x
    getRange (Qual n x)	= fuseRange n x

instance HasRange Literal where
    getRange (LitInt    r _)	= r
    getRange (LitFloat  r _)	= r
    getRange (LitString r _)	= r
    getRange (LitChar   r _)	= r

instance HasRange Fixity where
    getRange (LeftAssoc  r _)	= r
    getRange (RightAssoc r _)	= r
    getRange (NonAssoc   r _)	= r

