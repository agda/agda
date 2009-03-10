{-# LANGUAGE CPP, FlexibleInstances, DeriveDataTypeable #-}

{-| Some common syntactic entities are defined in this module.
-}
module Agda.Syntax.Common where

import Data.Generics (Typeable, Data)
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.Function
import Test.QuickCheck

import Agda.Syntax.Position
import Agda.Utils.Monad
import Agda.Utils.Size

#include "../undefined.h"
import Agda.Utils.Impossible

data Induction = Inductive | CoInductive
  deriving (Typeable, Data, Show, Eq)

data Hiding  = Hidden | NotHidden
    deriving (Typeable, Data, Show, Eq)

instance KillRange Induction where killRange = id
instance KillRange Hiding    where killRange = id

-- | A function argument can be hidden.
data Arg e  = Arg { argHiding :: Hiding, unArg :: e }
    deriving (Typeable, Data, Eq)

instance Functor Arg where
    fmap f (Arg h x) = Arg h $ f x

instance Foldable Arg where
    foldr f z (Arg _ x) = f x z

instance Traversable Arg where
    traverse f (Arg h x) = Arg h <$> f x

instance HasRange a => HasRange (Arg a) where
    getRange = getRange . unArg

instance KillRange a => KillRange (Arg a) where
  killRange = fmap killRange

instance Sized a => Sized (Arg a) where
  size = size . unArg

instance Show a => Show (Arg a) where
    show (Arg Hidden x)    = "{" ++ show x ++ "}"
    show (Arg NotHidden x) = "(" ++ show x ++ ")"

data Named name a =
    Named { nameOf     :: Maybe name
	  , namedThing :: a
	  }
    deriving (Eq, Typeable, Data)

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
    deriving (Typeable, Data, Show, Eq)

-- | Access modifier.
data Access = PrivateAccess | PublicAccess
    deriving (Typeable, Data, Show, Eq)

-- | Abstract or concrete
data IsAbstract = AbstractDef | ConcreteDef
    deriving (Typeable, Data, Show, Eq)

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

-- | Used to mark things which may need to be delayed. Delayed names
-- are not unfolded. Delayed things are made non-delayed by pattern
-- matching on coinductive constructors (pattern matching on one
-- \"coconstructor\" undelays names which are under that coconstructor
-- but not under yet another coconstructor).
--
-- The 'Eq' and 'Ord' instances ignore the 'isDelayed' field.

-- TODO: Is not it dangerous to equate f and .f?
data Delayed a = Delayed { isDelayed :: Bool
                         , force     :: a
                         }
  deriving (Typeable, Data, Show)

instance Eq a => Eq (Delayed a) where
  (==) = (==) `on` force

instance Ord a => Ord (Delayed a) where
  compare = compare `on` force

instance Functor Delayed where
  fmap f d = d { force = f (force d) }

instance HasRange a => HasRange (Delayed a) where
  getRange = getRange . force

instance KillRange a => KillRange (Delayed a) where
  killRange = fmap killRange

------------------------------------------------------------------------
-- Arbitrary and CoArbitrary instances

instance Arbitrary Induction where
  arbitrary = elements [Inductive, CoInductive]

instance CoArbitrary Induction where
  coarbitrary Inductive   = variant 0
  coarbitrary CoInductive = variant 1
