{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
module Agda.Utils.Arena
  ( Arena, withArena
  , Ptr
  , derefPtr
  , allocPtr
  )
  where

import Data.Kind (Type)

import GHC.Compact (Compact(..))
import GHC.Exts (Compact#, compactNew#, compactAdd#, Addr#, anyToAddr#, addrToAny#, keepAlive#)
import GHC.IO (IO(..), unIO)

-- | Reference to an "arena" of allocation quantified over the lifetime.
--
-- Arenas are backed by a native 'Compact' region, but allow values
-- contained within to be represented by addresses rather than GC
-- pointers, as long as the arena is alive when pointers are
-- dereferenced. Parametrising by the lifetime guarantees this.
newtype Arena r = Arena { getArena :: Compact# }
type role Arena nominal

-- | A pointer (immutable) to within an 'Arena'.
data Ptr r (a :: Type) = Ptr { getPtr :: Addr# }
type role Ptr nominal representational

-- | Run a computation which does not leak 'Ptr's and can place
-- allocations into the given 'Compact' region.
withArena :: forall r. (forall p. Arena p -> IO r) -> IO r
withArena k = IO \s -> case compactNew# 31268## s of
  (# s , c# #) -> keepAlive# c# s \s -> unIO (k (Arena c#)) s
  -- Size number taken from impl. of ghc-compact, I suspect so the
  -- allocator gives us 32K-word blocks after accounting for
  -- StgCompactNFDataBlock overhead and rounding.
{-# INLINE withArena #-}

-- | Derefence a pointer to within an 'Arena'.
--
-- The reference to the arena itself is needed so the garbage collector
-- doesn't kill the compact region before the value is consumed.
derefPtr :: forall r a. Ptr r a -> a
derefPtr (Ptr a) = case addrToAny# a of
  (# a #) -> a
{-# INLINE derefPtr #-}

-- | Move a value into an 'Arena'.
--
-- Returns the compacted value and a cheap 'Ptr' that refers to it.
allocPtr :: forall r a. Arena r -> a -> IO (a, Ptr r a)
allocPtr (Arena c) !a = IO \s -> case compactAdd# c a s of
  (# s , a #) -> case anyToAddr# a s of
    (# s , addr #) -> (# s , (a , Ptr addr) #)
{-# INLINE allocPtr #-}
