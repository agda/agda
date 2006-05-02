{-# OPTIONS -fglasgow-exts #-}

{-| Names in the concrete syntax are just strings (or lists of strings for
    qualified names).
-}
module Syntax.Concrete.Name where

import Data.Generics (Typeable, Data)

import Syntax.Position

-- | Equality and ordering on @Name@ are defined to ignore range so same names
--   in different locations are equal.
data Name = Name Range String
	  | NoName Range	-- ^ instead of @Name r \"_\"@
    deriving (Typeable, Data)

-- | @noName = 'NoName' 'noRange'@
noName :: Name
noName = NoName noRange

-- | @qualify A.B x == A.B.x@
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

instance HasRange Name where
    getRange (Name r _)	= r
    getRange (NoName r)	= r

instance HasRange QName where
    getRange (QName  x) = getRange x
    getRange (Qual n x)	= fuseRange n x

