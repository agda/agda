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

-- | A function argument can be relevant or irrelevant.
data Relevance
  = Relevant    -- ^ the argument is (possibly) relevant at compile-time
  | Irrelevant  -- ^ the argument is irrelevant at compile- and runtime
  | Forced      -- ^ the argument can be skipped during equality checking
    deriving (Typeable, Data, Show, Eq, Ord)

-- | For comparing @Relevance@ ignoring @Forced@.
ignoreForced :: Relevance -> Relevance
ignoreForced Forced     = Relevant
ignoreForced Relevant   = Relevant
ignoreForced Irrelevant = Irrelevant

-- | @Relevance@ from @Bool@.
irrelevant :: Bool -> Relevance
irrelevant True  = Irrelevant
irrelevant False = Relevant

instance KillRange Induction where killRange = id
instance KillRange Hiding    where killRange = id

-- | A function argument can be hidden and/or irrelevant.
data Arg e  = Arg
  { argHiding    :: Hiding
  , argRelevance :: Relevance
  , unArg :: e
  } deriving (Typeable, Data, Ord)

instance Eq a => Eq (Arg a) where
  Arg h1 _ x1 == Arg h2 _ x2 = (h1, x1) == (h2, x2)

hide :: Arg a -> Arg a
hide a = a { argHiding = Hidden }

defaultArg :: a -> Arg a
defaultArg = Arg NotHidden Relevant

isHiddenArg :: Arg a -> Bool
isHiddenArg arg = argHiding arg == Hidden

makeIrrelevant :: Arg a -> Arg a
makeIrrelevant a = a { argRelevance = Irrelevant }

makeRelevant :: Arg a -> Arg a
makeRelevant a = if argRelevance a == Irrelevant
                  then a { argRelevance = Relevant }
                  else a

-- | Compose two relevance flags.
--   This function is used to update the relevance information
--   on pattern variables @a@ after a match against something @rel@.
applyRelevance :: Relevance -> Arg a -> Arg a
applyRelevance Irrelevant a | argRelevance a == Relevant =
  a { argRelevance = Irrelevant }
applyRelevance Forced a | argRelevance a == Relevant =
  a { argRelevance = Forced }
applyRelevance rel a = a -- ^ do nothing if rel == Relevant or a is
                         -- already Forced or Irrelevant

-- | @xs `withArgsFrom` args@ translates @xs@ into a list of 'Arg's,
-- using the elements in @args@ to fill in the non-'unArg' fields.
--
-- Precondition: The two lists should have equal length.

withArgsFrom :: [a] -> [Arg b] -> [Arg a]
xs `withArgsFrom` args =
  zipWith (\x arg -> fmap (const x) arg) xs args

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
    show (Arg h r x) = showR r $ showH h $ show x
      where
        showH Hidden     s = "{" ++ s ++ "}"
        showH NotHidden  s = "(" ++ s ++ ")"
        showR Irrelevant s = "." ++ s
        showR Forced     s = "!" ++ s
        showR Relevant   s = "r" ++ s -- Andreas: I want to see it explicitly

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
