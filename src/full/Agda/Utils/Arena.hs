{-# LANGUAGE MagicHash, UnboxedTuples, RoleAnnotations #-}
module Agda.Utils.Arena
  ( Arena, withArena
  , Ptr
  , derefPtr
  , allocPtr
  )
  where

import GHC.Compact
import GHC.Exts (Addr#, anyToAddr#, addrToAny#, keepAlive#)
import GHC.IO (IO(..), unIO)

-- | Reference to an "arena" of allocation quantified over the lifetime.
--
-- Arenas are backed by a native 'Compact' region, but allow values
-- contained within to be represented by addresses rather than GC
-- pointers, as long as the arena is alive when pointers are
-- dereferenced. Parametrising by the lifetime guarantees this.
newtype Arena r = Arena { getArena :: Compact () }
type role Arena nominal

-- | A pointer (immutable) to within an 'Arena'.
data Ptr r a = Ptr { theAddress :: !Addr# }
type role Ptr nominal representational

-- | Run a computation which does not leak 'Ptr's and can place
-- allocations into the given 'Compact' region.
withArena :: forall r. Compact () -> (forall p. Arena p -> r) -> r
withArena c k = k (Arena c)
{-# INLINE withArena #-}

-- | Derefence a pointer to within an 'Arena'.
--
-- The reference to the arena itself is needed so the garbage collector
-- doesn't kill the compact region before the value is consumed.
derefPtr :: forall r a. Arena r -> Ptr r a -> IO a
derefPtr arena (Ptr a) = IO \s -> keepAlive# arena s \s ->
  case addrToAny# a of
    (# a #) -> (# s , a #)
{-# INLINE derefPtr #-}

-- | Move a value into an 'Arena'.
--
-- Returns the compacted value and a cheap 'Ptr' that refers to it.
allocPtr :: forall r a. Arena r -> a -> IO (a, Ptr r a)
allocPtr (Arena c) a = do
  !ac <- compactAdd c a
  let a = getCompact ac
  IO \s -> a `seq` case anyToAddr# a s of
    (# s , addr #) -> (# s , (a , Ptr addr) #)
{-# INLINE allocPtr #-}
