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

data Hiding  = Hidden | Instance | NotHidden
    deriving (Typeable, Data, Show, Eq, Ord)

-- | A function argument can be relevant or irrelevant.
--   See 'Agda.TypeChecking.Irrelevance'.
data Relevance
  = Relevant    -- ^ the argument is (possibly) relevant at compile-time
  | NonStrict   -- ^ the argument may never flow into evaluation position.
                --   Therefore, it is irrelevant at run-time.
                --   It is treated relevantly during equality checking.
  | Irrelevant  -- ^ the argument is irrelevant at compile- and runtime
  | Forced      -- ^ the argument can be skipped during equality checking
    deriving (Typeable, Data, Show, Eq)

instance Ord Relevance where
  (<=) = moreRelevant

-- | Information ordering.
-- @Relevant `moreRelevant` Forced `moreRelevant` NonStrict `moreRelevant` Irrelevant@
moreRelevant :: Relevance -> Relevance -> Bool
moreRelevant r r' =
  case (r, r') of
    -- top
    (_, Irrelevant) -> True
    (Irrelevant, _) -> False
    -- bottom
    (Relevant, _)   -> True
    (_, Relevant)   -> False
    -- second bottom
    (Forced, _)     -> True
    (_, Forced)     -> False
    -- remaining case
    (NonStrict,NonStrict) -> True

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

makeInstance :: Arg a -> Arg a
makeInstance a = a { argHiding = Instance }

hide :: Arg a -> Arg a
hide a = a { argHiding = Hidden }

defaultArg :: a -> Arg a
defaultArg = Arg NotHidden Relevant

isHiddenArg :: Arg a -> Bool
isHiddenArg arg = argHiding arg /= NotHidden

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
        showH Instance   s = "{{" ++ s ++ "}}"
        showR Irrelevant s = "." ++ s
        showR NonStrict  s = "?" ++ s
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
