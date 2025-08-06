{-# LANGUAGE Strict, MagicHash, AllowAmbiguousTypes, UnboxedTuples, CPP #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}

module Agda.TypeChecking.Serialise.Node where

import GHC.Exts
import GHC.Types
import GHC.Word
import Agda.Utils.Serializer
import Data.Hashable
import Data.Bits

#include "MachDeps.h"

-- | Constructor tag (maybe omitted) and argument indices.
data Node
  = N0
  | N1# !Word32
  | N2# !Word64
  | N3# !Word64 !Word32
  | N4# !Word64 !Word64
  | N5# !Word64 !Word64 !Word32
  | (:*:) !Word32 !Node
  deriving (Eq, Show)
infixr 5 :*:

splitW64 :: Word64 -> (Word32, Word32)
splitW64 x = let !a = fromIntegral (unsafeShiftR x 32)
                 !b = fromIntegral (x .&. 0x00000000ffffffff)
             in (a, b)
{-# INLINE splitW64 #-}

packW64 :: Word32 -> Word32 -> Word64
packW64 a b = unsafeShiftL (fromIntegral a) 32 .|. fromIntegral b
{-# INLINE packW64 #-}

pattern N1 :: Word32 -> Node
pattern N1 a = N1# a

pattern N2 :: Word32 -> Word32 -> Node
pattern N2 a b <- N2# (splitW64 -> (a, b)) where
  N2 a b = N2# (packW64 a b)

pattern N3 :: Word32 -> Word32 -> Word32 -> Node
pattern N3 a b c <- N3# (splitW64 -> (a, b)) c where
  N3 a b c = N3# (packW64 a b) c

pattern N4 :: Word32 -> Word32 -> Word32 -> Word32 -> Node
pattern N4 a b c d <- N4# (splitW64 -> (a, b)) (splitW64 -> (c, d)) where
  N4 a b c d = N4# (packW64 a b) (packW64 c d)

pattern N5 :: Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> Node
pattern N5 a b c d e <- N5# (splitW64 -> (a, b)) (splitW64 -> (c, d)) e where
  N5 a b c d e = N5# (packW64 a b) (packW64 c d) e
{-# complete N0, N1, N2, N3, N4, N5, (:*:) #-}

instance Hashable Node where
  -- Adapted from https://github.com/tkaitchuck/aHash/wiki/AHash-fallback-algorithm
  hashWithSalt h n = fromIntegral (go (fromIntegral h) n) where
    xor (W# x) (W# y) = W# (xor# x y)

    foldedMul :: Word -> Word -> Word
    foldedMul (W# x) (W# y) = case timesWord2# x y of (# hi, lo #) -> W# (xor# hi lo)

    combine :: Word -> Word -> Word
    combine x y = foldedMul (xor x y) factor where
      -- We use a version of fibonacci hashing, where our multiplier is the
      -- nearest prime to 2^64/phi or 2^32/phi. See https://stackoverflow.com/q/4113278.
#if WORD_SIZE_IN_BITS == 64
      factor = 11400714819323198549
#else
      factor = 2654435741
#endif

    go :: Word -> Node -> Word
    go !h N0           = h
    go  h (N1# a)      = h `combine` fromIntegral a
    go  h (N2# a)      = h `combine` fromIntegral a
    go  h (N3# a b)    = h `combine` fromIntegral a `combine` fromIntegral b
    go  h (N4# a b)    = h `combine` fromIntegral a `combine` fromIntegral b
    go  h (N5# a b c)  = h `combine` fromIntegral a `combine` fromIntegral b `combine` fromIntegral c
    go  h ((:*:) n ns) = go (combine h (fromIntegral n)) ns

  hash = hashWithSalt seed where
#if WORD_SIZE_IN_BITS == 64
      seed = 3032525626373534813
#else
      seed = 1103515245
#endif

--------------------------------------------------------------------------------

instance Serialize Node where

  size x = size (0::Int) + go 0 x where
    go acc N0         = acc
    go acc N1#{}      = acc + SIZEOF_WORD32
    go acc N2#{}      = acc + SIZEOF_WORD64
    go acc N3#{}      = acc + SIZEOF_WORD64 + SIZEOF_WORD32
    go acc N4#{}      = acc + SIZEOF_WORD64 + SIZEOF_WORD64
    go acc N5#{}      = acc + SIZEOF_WORD64 + SIZEOF_WORD64 + SIZEOF_WORD32
    go acc (n :*: ns) = go (acc + SIZEOF_WORD32) ns

  put n = Put \pHeader s -> let
    go :: Node -> Addr# -> State# RealWorld -> Int# -> (# Addr#, State# RealWorld, Int# #)
    go (N0         ) p s l = (# p, s, l #)
    go (N1# a      ) p s l = case unPut (put a) p s of
      (# p, s #) -> (# p, s, l +# 1# #)
    go (N2# ab     ) p s l = case unPut (put ab) p s of
      (# p, s #) -> (# p, s, l +# 2# #)
    go (N3# ab c   ) p s l = case unPut (put ab <> put c) p s of
      (# p, s #) -> (# p, s, l +# 3# #)
    go (N4# ab cd  ) p s l = case unPut (put ab <> put cd) p s of
      (# p, s #) -> (# p, s, l +# 4# #)
    go (N5# ab cd e) p s l = case unPut (put ab <> put cd <> put e) p s of
      (# p, s #) -> (# p, s, l +# 5# #)
    go (x :*: n)     p s l = case unPut (put x) p s of
      (# p, s #) -> go n p s (l +# 1#)
    in case go n (plusAddr# pHeader SIZEOF_HSINT#) s 0# of
      (# p, s, l #) -> case writeIntOffAddr# pHeader 0# l s of
        s -> (# p, s #)

  get = do
    I# l <- get
    ensure (I# l * SIZEOF_WORD32) \p' -> Get \e p s ->
      let
          {-# INLINE rd32 #-}
          rd32 :: Addr# -> State# RealWorld -> (# Addr#, State# RealWorld, Word32 #)
          rd32 p s = case plusAddr# p (-SIZEOF_WORD32#) of
            p -> case readWord32OffAddr# p 0# s of
              (# s, x #) -> (# p, s, W32# x #)

          {-# INLINE rd64 #-}
          rd64 :: Addr# -> State# RealWorld -> (# Addr#, State# RealWorld, Word64 #)
          rd64 p s = case plusAddr# p (-SIZEOF_WORD64#) of
            p -> case readWord64OffAddr# p 0# s of
              (# s, x #) -> (# p, s, W64# x #)

          go' :: Addr# -> State# RealWorld -> Int# -> Node -> (# State# RealWorld, Node #)
          go' p s l n = case l of
            0# -> (# s, n #)
            _  -> case rd32 p s of
              (# p, s, x #) -> let n' = x :*: n in go' p s (l -# 1#) n'

          go :: Addr# -> State# RealWorld -> Int# -> (# State# RealWorld, Node #)
          go p s l = case l of
            0# -> (# s, N0 #)
            1# -> case rd32 p s of (# p, s, a #) -> (# s, N1# a #)
            2# -> case rd64 p s of (# p, s, ab #) -> (# s, N2# ab #)
            3# -> case rd32 p s of
              (# p, s, c #) -> case rd64 p s of
                (# p, s, ab #) -> (# s, N3# ab c #)
            4# -> case rd64 p s of
              (# p, s, cd #) -> case rd64 p s of
                (# p, s, ab #) -> (# s, N4# ab cd #)
            5# -> case rd32 p s of
              (# p, s, e #) -> case rd64 p s of
                (# p, s, cd #) -> case rd64 p s of
                  (# p, s, ab #) -> (# s, N5# ab cd e #)
            l  -> case rd32 p s of
              (# p, s, e #) -> case rd64 p s of
                (# p, s, cd #) -> case rd64 p s of
                  (# p, s, ab #) -> go' p s (l -# 5#) (N5# ab cd e)

      in case go p' s l of (# s, n #) -> (# p', s, n #)
