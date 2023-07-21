{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Agda.Utils.IndexedList where

import Data.Kind ( Type )
import Agda.Utils.Lens

-- | Existential wrapper for indexed types.
data Some :: (k -> Type) -> Type where
  Some :: f i -> Some f

-- | Unpacking a wrapped value.
withSome :: Some b -> (forall i. b i -> a) -> a
withSome (Some x) f = f x

-- | Lists indexed by a type-level list. A value of type @All p [x₁..xₙ]@ is a
--   sequence of values of types @p x₁@, .., @p xₙ@.
data All :: (x -> Type) -> [x] -> Type where
  Nil  :: All p '[]
  Cons :: p x -> All p xs -> All p (x ': xs)

-- | Constructing an indexed list from a plain list.
makeAll :: (a -> Some b) -> [a] -> Some (All b)
makeAll f [] = Some Nil
makeAll f (x : xs) =
  case (f x, makeAll f xs) of
    (Some y, Some ys) -> Some (Cons y ys)

-- | Turning an indexed list back into a plain list.
forgetAll :: (forall x. b x -> a) -> All b xs -> [a]
forgetAll f Nil         = []
forgetAll f (Cons x xs) = f x : forgetAll f xs

-- | An index into a type-level list.
data Index :: [x] -> x -> Type where
  Zero :: Index (x ': xs) x
  Suc  :: Index xs x -> Index (y ': xs) x

-- | Indices are just natural numbers.
forgetIndex :: Index xs x -> Int
forgetIndex Zero    = 0
forgetIndex (Suc i) = 1 + forgetIndex i

-- | Mapping over an indexed list.
mapWithIndex :: (forall x. Index xs x -> p x -> q x) -> All p xs -> All q xs
mapWithIndex f Nil = Nil
mapWithIndex f (Cons p ps) = Cons (f Zero p) $ mapWithIndex (f . Suc) ps

-- | If you have an index you can get a lens for the given element.
lIndex :: Index xs x -> Lens' (All p xs) (p x)
lIndex Zero    f (Cons x xs) = f x           <&> \ x  -> Cons x xs
lIndex (Suc i) f (Cons x xs) = lIndex i f xs <&> \ xs -> Cons x xs

-- | Looking up an element in an indexed list.
lookupIndex :: All p xs -> Index xs x -> p x
lookupIndex = flip ix
  where
    -- -Wincomplete-patterns fails for the other argument order!
    ix :: Index xs x -> All p xs -> p x
    ix Zero    (Cons x xs) = x
    ix (Suc i) (Cons x xs) = ix i xs

-- | All indices into an indexed list.
allIndices :: All p xs -> All (Index xs) xs
allIndices = mapWithIndex const
