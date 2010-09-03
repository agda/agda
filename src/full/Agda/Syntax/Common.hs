{-# LANGUAGE CPP, FlexibleInstances, DeriveDataTypeable #-}

{-| Some common syntactic entities are defined in this module.
-}
module Agda.Syntax.Common where

import Data.Generics (Typeable, Data)
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Test.QuickCheck

import Agda.Syntax.Position
import Agda.Utils.Monad
import Agda.Utils.Size

#include "../undefined.h"
import Agda.Utils.Impossible

data Induction = Inductive | CoInductive
  deriving (Typeable, Data, Show, Eq, Ord)

data Hiding  = Hidden | NotHidden
    deriving (Typeable, Data, Show, Eq, Ord)

data Relevance = Relevant | Irrelevant
    deriving (Typeable, Data, Show, Eq, Ord)

instance KillRange Induction where killRange = id
instance KillRange Hiding    where killRange = id

-- | A function argument can be hidden.
data Arg e  = Arg 
  { argHiding    :: Hiding
  , argRelevance :: Relevance
  , unArg :: e 
  } deriving (Typeable, Data, Eq, Ord)

defaultArg :: a -> Arg a
defaultArg = Arg NotHidden Relevant

isHiddenArg :: Arg a -> Bool
isHiddenArg arg = argHiding arg == Hidden

instance Functor Arg where
    fmap f a = a { unArg = f (unArg a) }

instance Foldable Arg where
    foldr f z a = f (unArg a) z

instance Traversable Arg where
    traverse f (Arg h r x) = Arg h r <$> f x

instance HasRange a => HasRange (Arg a) where
    getRange = getRange . unArg

instance KillRange a => KillRange (Arg a) where
  killRange = fmap killRange

instance Sized a => Sized (Arg a) where
  size = size . unArg

instance Show a => Show (Arg a) where
    show (Arg Hidden    Relevant   x) = "{" ++ show x ++ "}"
    show (Arg NotHidden Relevant   x) = "(" ++ show x ++ ")"
    show (Arg Hidden    Irrelevant x) = ".{" ++ show x ++ "}"
    show (Arg NotHidden Irrelevant x) = ".(" ++ show x ++ ")"

data Named name a =
    Named { nameOf     :: Maybe name
	  , namedThing :: a
	  }
    deriving (Eq, Ord, Typeable, Data)

unnamed :: a -> Named name a
unnamed = Named Nothing

named :: name -> a -> Named name a
named = Named . Just

instance Functor (Named name) where
    fmap f (Named n x) = Named n $ f x

instance Foldable (Named name) where
    foldr f z (Named _ x) = f x z

instance Traversable (Named name) where
    traverse f (Named n x) = Named n <$> f x

instance HasRange a => HasRange (Named name a) where
    getRange = getRange . namedThing

instance KillRange a => KillRange (Named name a) where
  killRange = fmap killRange

instance Sized a => Sized (Named name a) where
  size = size . namedThing

instance Show a => Show (Named String a) where
    show (Named Nothing x)  = show x
    show (Named (Just n) x) = n ++ " = " ++ show x

-- | Only 'Hidden' arguments can have names.
type NamedArg a = Arg (Named String a)

-- | Functions can be defined in both infix and prefix style. See
--   'Agda.Syntax.Concrete.LHS'.
data IsInfix = InfixDef | PrefixDef
    deriving (Typeable, Data, Show, Eq, Ord)

-- | Access modifier.
data Access = PrivateAccess | PublicAccess
    deriving (Typeable, Data, Show, Eq, Ord)

-- | Abstract or concrete
data IsAbstract = AbstractDef | ConcreteDef
    deriving (Typeable, Data, Show, Eq, Ord)

type Nat    = Integer
type Arity  = Nat

-- | The unique identifier of a name. Second argument is the top-level module
--   identifier.
data NameId = NameId Nat Integer
    deriving (Eq, Ord, Typeable, Data)

instance Enum NameId where
  succ (NameId n m)	= NameId (n + 1) m
  pred (NameId n m)	= NameId (n - 1) m
  toEnum n		= __IMPOSSIBLE__  -- should not be used
  fromEnum (NameId n _) = fromIntegral n

newtype Constr a = Constr a

------------------------------------------------------------------------
-- Arbitrary and CoArbitrary instances

instance Arbitrary Induction where
  arbitrary = elements [Inductive, CoInductive]

instance CoArbitrary Induction where
  coarbitrary Inductive   = variant 0
  coarbitrary CoInductive = variant 1
