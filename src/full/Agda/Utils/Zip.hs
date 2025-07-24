-- | Overloaded 'zip' and 'zipWith'.
--
-- This module provides the 'Zip' class to overload zipping functions
-- for variants of the list type ('[]', 'List1', 'List2', 'ListInf').
--
-- Motivation:
-- In practice, we often zip a finite list with an infinite list,
-- e.g. @zipWith f xs (ys ++ repeat z)@.
-- We can know statically in this case that the resulting considers
-- each @xs@ by rewriting this to @zipWith f xs (ListInf.pad ys z)@
-- statically exposing the infinite nature of the second list.
-- To avoid cluttering the namespace with 4*4 variants of 'zipWith'
-- for all combination of our list types, we introduce an overloaded version.
--
-- Import this module as follows:
--
-- @
-- import Prelude hiding (zip, zipWith)
-- import Agda.Utils.Zip
-- @

module Agda.Utils.Zip where

import Prelude (map, uncurry)

import Data.List qualified as List

-- import Agda.Utils.List    ( pattern (:) )
import Agda.Utils.List1   ( List1, pattern (:|) )
import Agda.Utils.List2   ( List2, pattern List2 )
import Agda.Utils.ListInf ( ListInf, pattern (:<) )

import Agda.Utils.List    qualified as List
import Agda.Utils.List1   qualified as List1
import Agda.Utils.List2   qualified as List2
import Agda.Utils.ListInf qualified as ListInf

class Zip f g h | f g -> h where
  zip :: f a -> g b -> h (a, b)
  zip = zipWith (,)

  zipWith :: (a -> b -> c) -> f a -> g b -> h c
  -- zipWith f as bs = map (uncurry f) (zip as bs) -- needs Functor h

  {-# MINIMAL zipWith #-}

-- List instances

-- 0/0
instance Zip [] [] [] where
  zipWith = List.zipWith
  zip     = List.zip

-- 0/1
instance Zip [] List1 [] where
  zipWith _ [] _ = []
  zipWith f (a : as) (b :| bs) = f a b : zipWith f as bs

-- 1/0
instance Zip List1 [] [] where
  zipWith _ _ [] = []
  zipWith f (a :| as) (b : bs) = f a b : zipWith f as bs

-- 0/2
instance Zip [] List2 [] where
  zipWith _ []  _ = []
  zipWith f (a1 : as) (List2 b1 b2 bs) = f a1 b1 : zipWith f as (b2 :| bs)

-- 2/0
instance Zip List2 [] [] where
  zipWith _ _ [] = []
  zipWith f (List2 a1 a2 as) (b1 : bs) = f a1 b1 : zipWith f (a2 :| as) bs

-- 0/∞
instance Zip [] ListInf [] where
  zipWith f = go
    where
      go [] _ = []
      go (a : as) (b :< bs) = f a b : go as bs

-- ∞/0
instance Zip ListInf [] [] where
  zipWith f = go
    where
      go _ [] = []
      go (a :< as) (b : bs) = f a b : go as bs

-- List1 instances

-- 1/1
instance Zip List1 List1 List1 where
  zipWith = List1.zipWith
  zip     = List1.zip

-- 1/2
instance Zip List1 List2 List1 where
  zipWith f (a1 :| as) (List2 b1 b2 bs) = f a1 b1 :| zipWith f as (b2 :| bs)

-- 2/1
instance Zip List2 List1 List1 where
  zipWith f (List2 a1 a2 as) (b1 :| bs) = f a1 b1 :| zipWith f (a2 :| as) bs

-- 1/∞
instance Zip List1 ListInf List1 where
  zipWith f (a :| as) (b :< bs) = f a b :| zipWith f as bs

-- ∞/1
instance Zip ListInf List1 List1 where
  zipWith f (a :< as) (b :| bs) = f a b :| zipWith f as bs

-- List2 instances

-- 2/2
instance Zip List2 List2 List2 where
  zipWith = List2.zipWith
  zip     = List2.zip

-- 2/∞
instance Zip List2 ListInf List2 where
  zipWith f (List2 a1 a2 as) (b1 :< b2 :< bs) = List2 (f a1 b1) (f a2 b2) (zipWith f as bs)

-- ∞/2
instance Zip ListInf List2 List2 where
  zipWith f (a1 :< a2 :< as) (List2 b1 b2 bs) = List2 (f a1 b1) (f a2 b2) (zipWith f as bs)

-- ListInf instances

-- ∞/∞
instance Zip ListInf ListInf ListInf where
  zipWith = ListInf.zipWith
  zip     = ListInf.zip
