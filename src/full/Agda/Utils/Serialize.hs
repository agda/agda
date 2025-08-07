
{-# LANGUAGE
    Strict
  , MagicHash
  , UnboxedTuples
  , AllowAmbiguousTypes
  , TypeApplications
  , CPP
  #-}

{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}

module Agda.Utils.Serialize (
    Serialize(..)
  , serialize
  , deserialize
  , ensure
  , Get(..)
  , Put(..)
  , putByteArray#
  , getByteArray#
  ) where

import GHC.Exts
import GHC.ForeignPtr
import GHC.Types
import GHC.Word

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import qualified Data.Text as T
import qualified Data.Text.Array as T
import qualified Data.Text.Internal as T
import qualified Data.Text.Internal.Lazy as TL
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Unsafe as T

import Data.Bits

#include "MachDeps.h"

type RW = State# RealWorld
newtype Put = Put {unPut :: Addr# -> RW -> (# Addr#, RW #)}
newtype Get a = Get {unGet :: Addr# -> Addr# -> RW -> (# Addr#, RW, a #)}

class Serialize a where
  size :: a -> Int
  put  :: a -> Put
  get  :: Get a

instance Semigroup Put where
  {-# INLINE (<>) #-}
  Put f <> Put g = Put \p s -> case f p s of (# p, s #) -> g p s

instance Monoid Put where
  {-# INLINE mempty #-}
  mempty = Put \p s -> (# p, s #)
  {-# INLINE mappend #-}
  mappend = (<>)
  mconcat = error "Put: mconcat not implemented"

instance Functor Get where
  {-# INLINE fmap #-}
  fmap f (Get g) = Get \e p s -> case g e p s of
    (# p, s, a #) -> let b = f a in (# p, s, b #)

instance Applicative Get where
  {-# INLINE pure #-}
  pure a = Get \e p s -> (# p, s, a #)
  {-# INLINE (<*>) #-}
  Get ff <*> Get fa = Get \e p s -> case ff e p s of
    (# p, s, f #) -> case fa e p s of
      (# p, s, a #) -> let b = f a in (# p, s, b #)

instance Monad Get where
  {-# INLINE return #-}
  return = pure
  {-# INLINE (>>=) #-}
  Get ma >>= f = Get \e p s -> case ma e p s of
    (# p, s, a #) -> unGet (f a) e p s

-- ensure that we have N bytes to read.
ensure :: Int -> (Addr# -> Get a) -> Get a
ensure (I# n) k = Get \e p s ->
  let p' = plusAddr# p n in
  case leAddr# p' e of
    1# -> unGet (k p') e p s
    _  -> error "deserialize: not enough input"
{-# INLINE ensure #-}

serialize :: Serialize a => a -> IO B.ByteString
serialize a = do
  let sz = size a
  fptr@(ForeignPtr addr fp) <- B.mallocByteString sz
  str <- IO \s -> keepAlive# fp s \s -> case unPut (put a) addr s of
    (# p, s #) -> (# s, B.BS fptr (I# (minusAddr# p addr)) #)
  if B.length str == sz
    then pure str
    else error "serialize: impossible mismatch of computed and written size"

deserialize :: forall a. Serialize a => B.ByteString -> IO a
deserialize (B.BS (ForeignPtr p fp) (I# l)) =
  IO \s -> keepAlive# fp s \s ->
    let e = plusAddr# p l in
    case unGet (get @a) (plusAddr# p l) p s of
      (# p, s, a #) -> case ltAddr# p e of
        1# -> error "deserialize: not all input was consumed"
        _  -> case eqAddr# p e of
          1# -> (# s, a #)
          _  -> error "deserialize: impossible out of bounds access"

testTrip :: forall a. Show a => Eq a => Serialize a => a -> IO ()
testTrip a = do
  a' <- deserialize =<< serialize a
  print a'
  if a == a' then putStrLn "OK"
             else putStrLn "mismatch"

--------------------------------------------------------------------------------

instance Serialize () where
  size _ = 0
  put _ = mempty
  get = pure ()

instance Serialize Int where
  {-# INLINE size #-}
  size _ = SIZEOF_HSINT
  {-# INLINE put #-}
  put (I# n) = Put \p s -> case writeIntOffAddr# p 0# n s of
    s -> (# plusAddr# p SIZEOF_HSINT#, s #)
  {-# INLINE get #-}
  get = ensure SIZEOF_HSINT \p' -> Get \e p s ->
    case readIntOffAddr# p 0# s of
      (# s, n #) -> (# p', s, I# n #)

instance Serialize Double where
  {-# INLINE size #-}
  size _ = SIZEOF_HSDOUBLE
  {-# INLINE put #-}
  put (D# n) = Put \p s -> case writeDoubleOffAddr# p 0# n s of
    s -> (# plusAddr# p SIZEOF_HSDOUBLE#, s #)
  {-# INLINE get #-}
  get = ensure SIZEOF_HSDOUBLE \p' -> Get \e p s -> case readDoubleOffAddr# p 0# s of
    (# s, n #) -> (# p', s, D# n #)

instance Serialize Word where
  {-# INLINE size #-}
  size _ = SIZEOF_HSWORD
  {-# INLINE put #-}
  put (W# n) = Put \p s -> case writeWordOffAddr# p 0# n s of
    s -> (# plusAddr# p SIZEOF_HSWORD#, s #)
  {-# INLINE get #-}
  get = ensure SIZEOF_HSWORD \p' -> Get \e p s -> case readWordOffAddr# p 0# s of
    (# s, n #) -> (# p', s, W# n #)

instance Serialize Word8 where
  {-# INLINE size #-}
  size _ = SIZEOF_WORD8
  {-# INLINE put #-}
  put (W8# n) = Put \p s -> case writeWord8OffAddr# p 0# n s of
    s -> (# plusAddr# p SIZEOF_WORD8#, s #)
  {-# INLINE get #-}
  get = ensure SIZEOF_WORD8 \p' -> Get \e p s -> case readWord8OffAddr# p 0# s of
    (# s, n #) -> (# p', s, W8# n #)

instance Serialize Word16 where
  {-# INLINE size #-}
  size _ = SIZEOF_WORD16
  {-# INLINE put #-}
  put (W16# n) = Put \p s -> case writeWord16OffAddr# p 0# n s of
    s -> (# plusAddr# p SIZEOF_WORD16#, s #)
  {-# INLINE get #-}
  get = ensure SIZEOF_WORD16 \p' -> Get \e p s -> case readWord16OffAddr# p 0# s of
    (# s, n #) -> (# p', s, W16# n #)

instance Serialize Word32 where
  {-# INLINE size #-}
  size _ = SIZEOF_WORD32
  {-# INLINE put #-}
  put (W32# n) = Put \p s -> case writeWord32OffAddr# p 0# n s of
    s -> (# plusAddr# p SIZEOF_WORD32#, s #)
  {-# INLINE get #-}
  get = ensure SIZEOF_WORD32 \p' -> Get \e p s -> case readWord32OffAddr# p 0# s of
    (# s, n #) -> (# p', s, W32# n #)

instance Serialize Word64 where
  {-# INLINE size #-}
  size _ = SIZEOF_WORD64
  {-# INLINE put #-}
  put (W64# n) = Put \p s -> case writeWord64OffAddr# p 0# n s of
    s -> (# plusAddr# p SIZEOF_WORD64#, s #)
  {-# INLINE get #-}
  get = ensure SIZEOF_WORD64 \p' -> Get \e p s -> case readWord64OffAddr# p 0# s of
    (# s, n #) -> (# p', s, W64# n #)

instance Serialize Char where
  {-# INLINE size #-}
  size _ = SIZEOF_HSCHAR
  {-# INLINE put #-}
  put (C# n) = Put \p s -> case writeCharOffAddr# p 0# n s of
    s -> (# plusAddr# p SIZEOF_HSCHAR#, s #)
  {-# INLINE get #-}
  get = ensure SIZEOF_HSCHAR \p' -> Get \e p s -> case readCharOffAddr# p 0# s of
    (# s, n #) -> (# p', s, C# n #)

instance Serialize a => Serialize [a] where
  size = go (size (0::Int)) where
    go :: Int -> [a] -> Int
    go acc []     = acc
    go acc (a:as) = go (acc + size a) as
  {-# INLINE put #-}

  -- this is a bit fancy: we remember the address of the length header,
  -- do a single traversal over the list, then write the length back to
  -- the header.
  put as = Put \pHeader s ->

    let go :: [a] -> Addr# -> RW -> Int# -> (# Addr#, RW, Int# #)
        go ~as p s len = case as of
          []   -> (# p, s, len #)
          a:as -> case unPut (put a) p s of (# p, s #) -> go as p s (len +# 1#)

    in case go as (plusAddr# pHeader SIZEOF_HSINT#) s 0# of
      (# p, s, len #) -> case writeIntOffAddr# pHeader 0# len s of
        s -> (# p, s #)

  {-# INLINE get #-}
  get = do {l <- get @Int; go l} where
    go n = Get \p s -> case n of
      0 -> unGet (pure []) p s
      n -> unGet ((:) <$> get <*> go (n - 1)) p s

instance (Serialize a, Serialize b) => Serialize (a, b) where
  {-# INLINE size #-}
  size (a, b) = size a + size b
  {-# INLINE put #-}
  put (a, b) = put a <> put b
  {-# INLINE get #-}
  get = (,) <$> get <*> get

instance (Serialize a, Serialize b, Serialize c) => Serialize (a, b, c) where
  {-# INLINE size #-}
  size (a, b, c) = size a + size b + size c
  {-# INLINE put #-}
  put (a, b, c) = put a <> put b <> put c
  {-# INLINE get #-}
  get = (,,) <$> get <*> get <*> get

instance (Serialize a, Serialize b, Serialize c, Serialize d) => Serialize (a, b, c, d) where
  {-# INLINE size #-}
  size (a, b, c, d) = size a + size b + size c + size d
  {-# INLINE put #-}
  put (a, b, c, d) = put a <> put b <> put c <> put d
  {-# INLINE get #-}
  get = (,,,) <$> get <*> get <*> get <*> get

instance (Serialize a, Serialize b, Serialize c, Serialize d, Serialize e)
      => Serialize (a, b, c, d, e) where
  {-# INLINE size #-}
  size (a, b, c, d, e) = size a + size b + size c + size d + size e
  {-# INLINE put #-}
  put (a, b, c, d, e) = put a <> put b <> put c <> put d <> put e
  {-# INLINE get #-}
  get = (,,,,) <$> get <*> get <*> get <*> get <*> get

instance (Serialize a, Serialize b, Serialize c, Serialize d, Serialize e, Serialize f)
      => Serialize (a, b, c, d, e, f) where
  {-# INLINE size #-}
  size (a, b, c, d, e, f) = size a + size b + size c + size d + size e + size f
  {-# INLINE put #-}
  put (a, b, c, d, e, f) = put a <> put b <> put c <> put d <> put e <> put f
  {-# INLINE get #-}
  get = (,,,,,) <$> get <*> get <*> get <*> get <*> get <*> get

instance ( Serialize a, Serialize b, Serialize c
         , Serialize d, Serialize e, Serialize f, Serialize g)
      => Serialize (a, b, c, d, e, f, g) where
  {-# INLINE size #-}
  size (a, b, c, d, e, f, g) = size a + size b + size c + size d + size e + size f + size g
  {-# INLINE put #-}
  put (a, b, c, d, e, f, g) = put a <> put b <> put c <> put d <> put e <> put f <> put g
  {-# INLINE get #-}
  get = (,,,,,,) <$> get <*> get <*> get <*> get <*> get <*> get <*> get

instance ( Serialize a, Serialize b, Serialize c
         , Serialize d, Serialize e, Serialize f, Serialize g, Serialize h)
      => Serialize (a, b, c, d, e, f, g, h) where
  {-# INLINE size #-}
  size (a, b, c, d, e, f, g, h) =
    size a + size b + size c + size d + size e + size f + size g + size h
  {-# INLINE put #-}
  put (a, b, c, d, e, f, g, h) =
    put a <> put b <> put c <> put d <> put e <> put f <> put g <> put h
  {-# INLINE get #-}
  get = (,,,,,,,) <$> get <*> get <*> get <*> get <*> get <*> get <*> get <*> get

-- low-level ByteArray# helpers
-- Write a ByteArray# to buffer, with offset + length.
{-# INLINE putByteArray# #-}
putByteArray# :: ByteArray# -> Int# -> Int# -> Put
putByteArray# arr start len = Put \p s ->
  case copyByteArrayToAddr# arr start p len s of
    s -> (# plusAddr# p len, s #)

-- Read a ByteArray# of length "len" from buffer
{-# INLINE getByteArray# #-}
getByteArray# :: Int# -> (ByteArray# -> Get a) -> Get a
getByteArray# len k = ensure (I# len) \p' -> Get \e p s ->
  case newByteArray# len s of
    (# s, arr #) -> case copyAddrToByteArray# p arr 0# len s of
      s -> case unsafeFreezeByteArray# arr s of
        (# s, arr #) -> unGet (k arr) e p' s

instance Serialize T.Text where
  {-# INLINE size #-}
  size t = size (0::Int) + T.lengthWord8 t

  put (T.Text (T.ByteArray arr) (I# start) (I# len)) =
    put (I# len) <> putByteArray# arr start len

  get = do
    I# l <- get
    getByteArray# l \arr -> Get \e p s ->
      (# p, s, T.Text (T.ByteArray arr) 0 (I# l) #)

lTextBytes :: TL.Text -> Int
lTextBytes t = go t 0 where
  go TL.Empty        acc = acc
  go (TL.Chunk t ts) acc = go ts (T.lengthWord8 t + acc)

instance Serialize TL.Text where
  size t = size (0::Int) + lTextBytes t
  put t = Put \pHeader s -> let

    go :: TL.Text -> Addr# -> RW -> Int# -> (# Addr#, RW, Int# #)
    go TL.Empty        p s len = (# p, s, len #)
    go (TL.Chunk t ts) p s len = case t of
      T.Text (T.ByteArray arr) (I# start) (I# l) ->
        case unPut (putByteArray# arr start l) p s of
          (# p , s #) -> go ts p s (len +# l)

    in case go t (plusAddr# pHeader SIZEOF_HSINT#) s 0# of
      (# p, s, len #) -> case writeIntOffAddr# pHeader 0# len s of
        s -> (# p, s #)

  get = TL.fromStrict <$> get
