
module Data.Monoid.New
    ( module Data.Monoid
    , Dual(..)
    , Endo(..)
    , All(..)
    , Any(..)
    , Sum(..)
    , Product(..)
    ) where

import Data.Monoid

-- | The dual of a monoid, obtained by swapping the arguments of 'mappend'.
newtype Dual a = Dual { getDual :: a }

instance Monoid a => Monoid (Dual a) where
	mempty = Dual mempty
	Dual x `mappend` Dual y = Dual (y `mappend` x)

-- | The monoid of endomorphisms under composition.
newtype Endo a = Endo { appEndo :: a -> a }

instance Monoid (Endo a) where
	mempty = Endo id
	Endo f `mappend` Endo g = Endo (f . g)

-- | Boolean monoid under conjunction.
newtype All = All { getAll :: Bool }
	deriving (Eq, Ord, Read, Show, Bounded)

instance Monoid All where
	mempty = All True
	All x `mappend` All y = All (x && y)

-- | Boolean monoid under disjunction.
newtype Any = Any { getAny :: Bool }
	deriving (Eq, Ord, Read, Show, Bounded)

instance Monoid Any where
	mempty = Any False
	Any x `mappend` Any y = Any (x || y)

-- | Monoid under addition.
newtype Sum a = Sum { getSum :: a }
	deriving (Eq, Ord, Read, Show, Bounded)

instance Num a => Monoid (Sum a) where
	mempty = Sum 0
	Sum x `mappend` Sum y = Sum (x + y)

-- | Monoid under multiplication.
newtype Product a = Product { getProduct :: a }
	deriving (Eq, Ord, Read, Show, Bounded)

instance Num a => Monoid (Product a) where
	mempty = Product 1
	Product x `mappend` Product y = Product (x * y)
