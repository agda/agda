
{-# LANGUAGE Strict, MagicHash, AllowAmbiguousTypes, UnboxedTuples, CPP #-}
{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}

{-# OPTIONS_GHC -ddump-to-file -ddump-simpl -dsuppress-all -dno-suppress-type-signatures #-}

module Agda.TypeChecking.Serialise.Node where

import GHC.Exts
import GHC.Word
import Agda.Utils.Serialize
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
  | N6# !Word64 !Word64 !Word64 !Node
  deriving (Show)

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
{-# INLINE N1 #-}

pattern N2 :: Word32 -> Word32 -> Node
pattern N2 a b <- N2# (splitW64 -> (a, b)) where
  N2 a b = N2# (packW64 a b)
{-# INLINE N2 #-}

pattern N3 :: Word32 -> Word32 -> Word32 -> Node
pattern N3 a b c <- N3# (splitW64 -> (a, b)) c where
  N3 a b c = N3# (packW64 a b) c
{-# INLINE N3 #-}

pattern N4 :: Word32 -> Word32 -> Word32 -> Word32 -> Node
pattern N4 a b c d <- N4# (splitW64 -> (a, b)) (splitW64 -> (c, d)) where
  N4 a b c d = N4# (packW64 a b) (packW64 c d)
{-# INLINE N4 #-}

pattern N5 :: Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> Node
pattern N5 a b c d e <- N5# (splitW64 -> (a, b)) (splitW64 -> (c, d)) e where
  N5 a b c d e = N5# (packW64 a b) (packW64 c d) e
{-# INLINE N5 #-}

pattern N6 :: Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> Node -> Node
pattern N6 a b c d e f n <- N6# (splitW64 -> (a, b)) (splitW64 -> (c, d)) (splitW64 -> (e, f)) n where
  N6 a b c d e f n = N6# (packW64 a b) (packW64 c d) (packW64 e f) n
{-# INLINE N6 #-}
{-# complete N0, N1, N2, N3, N4, N5, N6 #-}

instance Eq Node where
  N0          == N0             = True
  N1# a       == N1# a'         = a == a'
  N2# ab      == N2# ab'        = ab == ab'
  N3# ab c    == N3# ab' c'     = ab == ab' && c == c'
  N4# ab cd   == N4# ab' cd'    = ab == ab' && cd == cd'
  N5# ab cd e == N5# ab' cd' e' = ab == ab' && cd == cd' && e == e'
  N6# ab cd ef n == N6# ab' cd' ef' n' =
    ab == ab' && cd == cd' && ef == ef' && n == n'
  _ == _ = False

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
    go h N0           = h
    go h (N1# a)      = h `combine` fromIntegral a
    go h (N2# a)      = h `combine` fromIntegral a
    go h (N3# a b)    = h `combine` fromIntegral a `combine` fromIntegral b
    go h (N4# a b)    = h `combine` fromIntegral a `combine` fromIntegral b
    go h (N5# a b c)  = h `combine` fromIntegral a `combine` fromIntegral b
                        `combine` fromIntegral c
    go h (N6# a b c n) = let h' = h `combine` fromIntegral a
                                   `combine` fromIntegral b `combine` fromIntegral c
                         in go h' n

  hash = hashWithSalt seed where
#if WORD_SIZE_IN_BITS == 64
      seed = 3032525626373534813
#else
      seed = 1103515245
#endif

--------------------------------------------------------------------------------

instance Serialize Node where
  size = go SIZEOF_HSINT where
    go :: Int -> Node -> Int
    go !acc = \case
      N0    -> acc
      N1#{} -> acc + SIZEOF_WORD32
      N2#{} -> acc + SIZEOF_WORD64
      N3#{} -> acc + SIZEOF_WORD64 + SIZEOF_WORD32
      N4#{} -> acc + SIZEOF_WORD64 + SIZEOF_WORD64
      N5#{} -> acc + SIZEOF_WORD64 + SIZEOF_WORD64 + SIZEOF_WORD32
      N6# _ _ _ n -> go (acc + SIZEOF_WORD64 + SIZEOF_WORD64 + SIZEOF_WORD64) n

  put n = Put \hd s -> let
    setHeader :: Int -> Addr# -> Put
    setHeader n hd = Put \p s -> case unPut (put n) hd s of
      (# _, s #) -> (# p, s #)

    go :: Node -> Int -> Addr# -> Put
    go n l hd = Put \p s -> case n of
      N0             -> unPut (setHeader l hd) p s
      N1# a          -> unPut (put a <> setHeader (l + 1) hd) p s
      N2# ab         -> unPut (put ab <> setHeader (l + 2) hd) p s
      N3# ab c       -> unPut (put ab <> put c <> setHeader (l + 3) hd) p s
      N4# ab cd      -> unPut (put ab <> put cd <> setHeader (l + 4) hd) p s
      N5# ab cd e    -> unPut (put ab <> put cd <> put e <> setHeader (l + 5) hd) p s
      N6# ab cd ef n -> unPut (put ab <> put cd <> put ef <> go n (l + 6) hd) p s

    in unPut (go n 0 hd) (plusAddr# hd SIZEOF_HSINT#) s

  get = do {l <- get; ensure (unsafeShiftL l 2) \_ -> go l} where
    g32 :: Get Word32; {-# INLINE g32 #-}
    g32 = Get \_ p s -> case readWord32OffAddr# p 0# s of
            (# s, x #) -> (# plusAddr# p SIZEOF_WORD32#, s, W32# x #)
    g64 :: Get Word64; {-# INLINE g64 #-}
    g64 = Get \_ p s -> case readWord64OffAddr# p 0# s of
            (# s, x #) -> (# plusAddr# p SIZEOF_WORD64#, s, W64# x #)

    go :: Int -> Get Node
    go l = Get \e p s -> case l of
      0 -> unGet (pure N0) e p s
      1 -> unGet (N1# <$> g32) e p s
      2 -> unGet (N2# <$> g64) e p s
      3 -> unGet (N3# <$> g64 <*> g32) e p s
      4 -> unGet (N4# <$> g64 <*> g64) e p s
      5 -> unGet (N5# <$> g64 <*> g64 <*> g32) e p s
      l -> unGet (N6# <$> g64 <*> g64 <*> g64 <*> go (l - 6)) e p s
