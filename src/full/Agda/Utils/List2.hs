{-# LANGUAGE TypeFamilies #-}  -- for IsList instance

-- | Lists of length at least 2.
--
--   Import as:
--   @
--      import Agda.Utils.List2 (List2(List2))
--      import qualified Agda.Utils.List2 as List2
--   @

module Agda.Utils.List2
  ( module Agda.Utils.List2
  , module Reexport
  ) where

import Control.DeepSeq

import Data.Data                       ( Data )
import qualified Data.List as List

import GHC.Exts                        ( IsList(..) )
import qualified GHC.Exts  as Reexport ( toList )

import Agda.Utils.List1                ( List1, pattern (:|) )

import Agda.Utils.Impossible

-- | Lists of length ≥2.
data List2 a = List2 a a [a]
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)

-- | Safe.
head :: List2 a -> a
head (List2 a _ _) = a

-- | Safe.
tail :: List2 a -> [a]
tail (List2 a b cs) = b : cs

-- | Safe.
tail1 :: List2 a -> List1 a
tail1 (List2 a b cs) = b :| cs

instance IsList (List2 a) where
  type Item (List2 a) = a

  -- | Unsafe!
  fromList :: [a] -> List2 a
  fromList (a : b : cs) = List2 a b cs
  fromList _            = __IMPOSSIBLE__

  toList :: List2 a -> [a]
  toList (List2 a b cs) = a : b : cs

toList1 :: List2 a -> List1 a
toList1 (List2 a b cs) = a :| b : cs

-- | Unsafe!
fromList1 :: List1 a -> List2 a
fromList1 (a :| b : cs) = List2 a b cs
fromList1 _             = __IMPOSSIBLE__

break :: (a -> Bool) -> List2 a -> ([a],[a])
break p = List.break p . toList

instance NFData a => NFData (List2 a) where
  rnf (List2 a b cs) = rnf a `seq` rnf b `seq` rnf cs
