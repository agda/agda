{-# LANGUAGE UndecidableInstances, MagicHash #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wunused-matches #-}
{-# OPTIONS_GHC -Wunused-binds #-}

{-# OPTIONS_GHC -ddump-to-file -ddump-simpl -dsuppress-all -dno-suppress-type-signatures #-}

-- | Serializing types that are not Agda-specific.

module Agda.TypeChecking.Serialise.Instances.General where

import Agda.Utils.Monad
import Control.Monad.Reader (asks, ReaderT(..), runReaderT)

import qualified Data.Foldable as Fold
import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import Data.Int (Int32)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Strict.Tuple (Pair(..))
import qualified Data.Text      as T
import qualified Data.Text.Lazy as TL
import Data.Typeable
import Data.Void
import Data.Word (Word32, Word64)

import Agda.TypeChecking.Serialise.Base

import Agda.Utils.BiMap (BiMap)
import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.DocTree qualified as DocTree
import Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.List2 (List2)
import qualified Agda.Utils.List2 as List2
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.SmallSet (SmallSet(..))
import Agda.Utils.Set1 (Set1)
import qualified Agda.Utils.Set1 as Set1
import Agda.Utils.Trie (Trie(..))
import Agda.Utils.VarSet (VarSet(..))
import Agda.Utils.WithDefault
import qualified Agda.Utils.MinimalArray.Lifted as AL

---------------------------------------------------------------------------
-- Base types

instance EmbPrj Void where
  icod_ = absurd
  value = vcase valu where valu _ = malformed

instance EmbPrj () where
  icod_ () = pure 0

  value 0 = pure ()
  value _ = malformed

instance EmbPrj Bool where
  icod_ False = pure 0
  icod_ True  = pure 1

  value 0 = pure False
  value 1 = pure True
  value _ = malformed

instance EmbPrj Char where
  icod_ c = return $! fromIntegral $ fromEnum c
  value i = return $! toEnum $ fromInteger $ toInteger i

-- Numeric types

instance EmbPrj Double where
  icod_   = icodeDouble
  value i = flip AL.unsafeIndex (fromIntegral i) <$!> asks doubleA

-- Andreas, Agda Hackathon 2024-10-15
-- Are we sure we never use an Int that does not fit into 32 bits?
instance EmbPrj Int where
  icod_ i = return $! fromIntegral i
  value i = return $! fromIntegral i

instance EmbPrj Int32 where
  icod_ i = return $! fromIntegral i
  value i = return $! fromIntegral i

instance EmbPrj Integer where
  icod_   = icodeInteger
  value i = flip AL.unsafeIndex (fromIntegral i) <$!> asks integerA

instance EmbPrj Word32 where
  icod_ i = return i
  value i = return i

instance EmbPrj Word64 where
  icod_ i = icodeN' (undefined :: Word32 -> Word32 -> Word32) (word32 q) (word32 r)
    where (q, r) = quotRem i (2 ^ 32)
          word32 :: Word64 -> Word32
          word32 = fromIntegral

  value = vcase valu where
    valu (N2 a b) = return $! n * fromIntegral a + fromIntegral b
    valu _        = malformed
    n = 2 ^ 32

-- Text types

instance {-# OVERLAPPING #-} EmbPrj String where
  icod_   = icodeString
  value i = flip AL.unsafeIndex (fromIntegral i) <$!> asks stringA

instance EmbPrj TL.Text where
  icod_   = icodeX lTextD lTextC
  value i = flip AL.index (fromIntegral i) <$!> asks lTextA

instance EmbPrj T.Text where
  icod_   = icodeX sTextD sTextC
  value i = flip AL.index (fromIntegral i) <$!> asks sTextA

---------------------------------------------------------------------------
-- Non-recursive types

instance (EmbPrj a, EmbPrj b) => EmbPrj (a, b) where
  icod_ (a, b) = icodeN' (,) a b

  value = valueN (,)

instance (EmbPrj a, EmbPrj b) => EmbPrj (Pair a b) where
  icod_ (a :!: b) = icodeN' (:!:) a b

  value = valueN (:!:)

instance (EmbPrj a, EmbPrj b, EmbPrj c) => EmbPrj (a, b, c) where
  icod_ (a, b, c) = icodeN' (,,) a b c

  value = valueN (,,)

instance (EmbPrj a, EmbPrj b) => EmbPrj (Either a b) where
  icod_ (Left  x) = icodeN 0 Left x
  icod_ (Right x) = icodeN 1 Right x

  value = vcase valu where
    valu (N2 0 x) = valuN Left  x
    valu (N2 1 x) = valuN Right x
    valu _        = malformed

instance EmbPrj a => EmbPrj (Maybe a) where
  icod_ Nothing  = icodeN' Nothing
  icod_ (Just x) = icodeN' Just x

  value = vcase valu where
    valu N0     = valuN Nothing
    valu (N1 x) = valuN Just x
    valu _      = malformed

instance EmbPrj a => EmbPrj (Strict.Maybe a) where
  icod_ m = icode (Strict.toLazy m)
  value m = Strict.toStrict <$!> value m

instance (EmbPrj a, Typeable b) => EmbPrj (WithDefault' a b) where
  icod_ = \case
    Default -> icodeN' Default
    Value b -> icodeN' Value b

  value = vcase $ \case
    N0   -> valuN Default
    N1 a -> valuN Value a
    _    -> malformed

---------------------------------------------------------------------------
-- Sequences

{-# INLINABLE icodeList #-}
icodeList :: EmbPrj a => [a] -> S Node
icodeList as = ReaderT \r -> case as of
  []             -> pure N0
  a:[]           -> runReaderT (N1 <$!> icode a) r
  a:b:[]         -> runReaderT (N2 <$!> icode a <*!> icode b) r
  a:b:c:[]       -> runReaderT (N3 <$!> icode a <*!> icode b <*!> icode c) r
  a:b:c:d:[]     -> runReaderT (N4 <$!> icode a <*!> icode b <*!> icode c <*!> icode d) r
  a:b:c:d:e:[]   -> runReaderT (N5 <$!> icode a <*!> icode b
                                   <*!> icode c <*!> icode d <*!> icode e) r
  a:b:c:d:e:f:as -> runReaderT (N6 <$!> icode a <*!> icode b <*!> icode c
                                   <*!> icode d <*!> icode e <*!> icode f <*!> icodeList as) r

valueList :: EmbPrj a => Node -> R [a]
valueList as = ReaderT \r -> case as of
  N0   -> pure []
  N1 a -> flip runReaderT r do
    !a <- value a
    pure [a]
  N2 a b -> flip runReaderT r do
    !a <- value a
    !b <- value b
    pure [a, b]
  N3 a b c -> flip runReaderT r do
    !a <- value a
    !b <- value b
    !c <- value c
    pure [a, b, c]
  N4 a b c d -> flip runReaderT r do
    !a <- value a
    !b <- value b
    !c <- value c
    !d <- value d
    pure [a, b, c, d]
  N5 a b c d e -> flip runReaderT r do
    !a <- value a
    !b <- value b
    !c <- value c
    !d <- value d
    !e <- value e
    pure [a, b, c, d, e]
  N6 a b c d e f as -> flip runReaderT r do
    !a  <- value a
    !b  <- value b
    !c  <- value c
    !d  <- value d
    !e  <- value e
    !f  <- value f
    !as <- valueList as
    pure (a:b:c:d:e:f:as)

instance {-# OVERLAPPABLE #-} EmbPrj a => EmbPrj [a] where
  {-# INLINE icod_ #-}
  icod_ xs = icodeNode =<< icodeList xs where
  {-# INLINE value #-}
  value = vcase valueList

instance EmbPrj a => EmbPrj (List1 a) where
  icod_ = icod_ . List1.toList
  value = maybe malformed return . List1.nonEmpty <=< value

instance EmbPrj a => EmbPrj (List2 a) where
  icod_ = icod_ . List2.toList
  value = maybe malformed return . List2.fromListMaybe <=< value

instance EmbPrj a => EmbPrj (Seq a) where
  icod_ s = icode (Fold.foldr' (:) [] s)
  value s = Seq.fromList <$!> value s

data KVS a b = Cons a b !(KVS a b) | Nil

icodeListPair :: EmbPrj k => EmbPrj v => KVS k v -> S Node
icodeListPair as = ReaderT \r -> case as of
  Nil ->
    pure N0
  Cons a b Nil -> flip runReaderT r $
    N2 <$!> icode a <*!> icode b
  Cons a b (Cons c d Nil) -> flip runReaderT r $
    N4 <$!> icode a <*!> icode b <*!> icode c <*!> icode d
  Cons a b (Cons c d (Cons e f as)) -> flip runReaderT r $
    N6 <$!> icode a <*!> icode b <*!> icode c
       <*!> icode d <*!> icode e <*!> icode f <*!> icodeListPair as

{-# INLINABLE valueListPair #-}
valueListPair :: EmbPrj k => EmbPrj v => Node -> R [(k, v)]
valueListPair as = ReaderT \r -> case as of
  N0     -> pure []
  N2 a b -> flip runReaderT r do
    !a <- value a
    !b <- value b
    pure [(a, b)]
  N4 a b c d -> flip runReaderT r do
    !a <- value a
    !b <- value b
    !c <- value c
    !d <- value d
    pure [(a, b), (c, d)]
  N6 a b c d e f as -> flip runReaderT r do
    !a  <- value a
    !b  <- value b
    !c  <- value c
    !d  <- value d
    !e  <- value e
    !f  <- value f
    !as <- valueListPair as
    pure ((a, b):(c, d):(e, f):as)
  _ -> malformedIO

---------------------------------------------------------------------------
-- Maps

instance (EmbPrj k, EmbPrj v, EmbPrj (BiMap.Tag v)) =>
         EmbPrj (BiMap k v) where
  icod_ m = icode (BiMap.toDistinctAscendingLists m)
  value m = BiMap.fromDistinctAscendingLists <$!> value m

instance (Eq k, Hashable k, EmbPrj k, EmbPrj v) => EmbPrj (HashMap k v) where
  icod_ m = icodeNode =<< icodeListPair (HMap.foldrWithKey' (\ k v !acc -> Cons k v acc) Nil m)
  value = vcase ((HMap.fromList <$!>) . valueListPair)

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Map a b) where
  icod_ m = icodeNode =<< icodeListPair (Map.foldrWithKey' (\ k v !acc -> Cons k v acc) Nil m)
  value = vcase ((Map.fromAscList <$!>) . valueListPair)

---------------------------------------------------------------------------
-- Sets

instance EmbPrj IntSet where
  icod_ s = icode (IntSet.foldr' (:) [] s)
  value s = IntSet.fromDistinctAscList <$!> value s

instance (Ord a, EmbPrj a) => EmbPrj (Set a) where
  icod_ s = icode (Set.foldr' (:) [] s)
  value s = Set.fromDistinctAscList <$!> value s

instance (Ord a, EmbPrj a) => EmbPrj (Set1 a) where
  icod_ s = icode (Set1.foldr' (:) [] s)
  value s = Set1.fromDistinctAscList <$!> value s

instance Typeable a => EmbPrj (SmallSet a) where
  icod_ (SmallSet a) = icodeN' SmallSet a
  value = valueN SmallSet

instance EmbPrj VarSet where
  icod_   = icodeVarSet
  value i = flip AL.index (fromIntegral i) <$!> asks varSetA

---------------------------------------------------------------------------
-- Trees

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Trie a b) where
  icod_ (Trie a b) = icodeN' Trie a b
  value = valueN Trie

instance EmbPrj a => EmbPrj (DocTree.DocTree a) where
  icod_ = \case
    DocTree.Text a   -> icodeN' DocTree.Text a
    DocTree.Node a b -> icodeN' DocTree.Node a b

  value = vcase \case
    N1 a   -> valuN DocTree.Text a
    N2 a b -> valuN DocTree.Node a b
    _      -> malformed
