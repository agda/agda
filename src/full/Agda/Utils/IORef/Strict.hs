-- | A variant of 'IORef' that ensures the value stored
-- inside the reference is always in WHNF.
--
-- This module should be imported qualified, ala
--
-- @
-- import Agda.Utils.IORef.Strict qualified as Strict
-- @
module Agda.Utils.IORef.Strict
  (
    -- * Strict IO references #strict-ioref#
    --
    -- $strictIORef
    IORef
  , newIORef
  , readIORef
  , writeIORef
  , modifyIORef
  , atomicModifyIORef
  ) where

import Control.Exception (evaluate)

import Data.Coerce
import Data.IORef qualified as Lazy


-- $strictIORef
-- A classic laziness footgun is that 'IORef' does not force
-- values written to it to weak-head normal form. This is a
-- common source of space leaks, as illustrated by the following
-- (somewhat contrived) example:
--
-- @
-- gotcha :: IO ()
-- gotcha = do
--   ref <- newIORef 1
--   loop ref (10 ^ 9)
--   n <- readIORef ref
--   print n
--   where
--     loop :: IORef Int -> Int -> IO ()
--     loop ref i =
--       if i == 0 then
--         pure ()
--       else do
--         n <- readIORef ref
--         writeIORef ref (n + 1)
--         loop ref (i - 1)
-- @
--
-- As the name suggests, this is a classic example of a space leak.
-- When we start the loop, @ref@ contains 1. At each iteration, we
-- read the contents of @ref@ into @n@, and write a *thunk* to @ref@
-- that will compute @n + 1@ when forced. This results in a chain of
-- 1 billion thunks being allocated and kept live until we 'print'
-- the value stored in @ref@, which causes us to force the thunk chain.
-- The solution is to replace @writeIORef ref (n + 1)@ with @writeIORef ref $! (n + 1)@,
-- which forces the thunk @n + 1@ to weak-heak normal form, which prevents
-- the thunk chain from building up inside of the 'IORef'.
--
-- Lazy IO references can also cause programs to keep data live
-- for much longer than required, leading to memory leaks. The
-- basic anatomy of this class of leaks is something like the following:
--
-- @
-- import Control.Concurrent
-- import Data.IORef
-- import GHC.Profiling
-- import System.Mem
-- import System.IO
--
-- memoryLeak :: IO ()
-- memoryLeak = do
--   let bigList = [1..10 ^ 6]
--   -- Force the spine of the list to make GHC allocate the whole thing.
--   print (length bigList)
--   hFlush stdout
--   -- Make an 'IORef' that uses 'bigList', and then do some unrelated slow computation.
--   ref <- newIORef (sum bigList)
--   loop 10
--   -- Finally print the value in the reference.
--   n <- readIORef ref
--   putStrLn $! show n
--   where
--     loop :: Int -> IO ()
--     loop 0 = pure ()
--     loop i = do
--       threadDelay (10 ^ 6)
--       performBlockingMajorGC
--       requestHeapCensus
--       putStrLn "Working..."
--       hFlush stdout
--       loop (i - 1)
-- @
--
-- If we run this program with @+RTS -l -hT -RTS@ and view the resulting @.eventlog@ file
-- with [eventlog2html](https://mpickering.github.io/eventlog2html/), we will see that
-- @bigList@ is kept live for the duration of @loop@, despite the repeated calls to
-- @performBlockingMajorGC@. This is because @newIORef (sum bigList)@ allocates a thunk
-- for @sum bigList@, which @newIORef@ does not force. This thunk references @bigList@,
-- so the garbage collector is forced to keep @bigList@ live until we actually force the
-- value stored inside @ref@ by printing it. We can avoid this by replacing the @newIORef@
-- call with @newIORef $! (sum bigList)@, which forces the @sum bigList@ thunk to weak-head
-- normal form, which removes the final reference to @bigList@. The GC will then free it on the
-- first @performBlockingMajorGC@ call.
--
-- These sorts of mistakes are very easy to make, and very hard to diagnose. This
-- module attempts to (partially) solve the problem by providing an opaque wrapper around 'Data.IORef.IORef',
-- along with a corresponding API that ensures that the value stored in the reference
-- is always in weak-head normal form.
--
-- == When should I use strict references?
--
-- The short answer is: "If you are unsure, you should probably use strict references".
--
-- The less short answer depends on your usage patterns:
--
-- * Do you repeatedly read and then write to the reference? If so, you probably
--   want to use strict references to avoid space leaks like the first example.
--
-- * Do you use the reference to store things that are computed from things that
--   shouldn't be kept live? If so, you probably want to use strict references to avoid
--   memory leaks like the second example.
--
-- * Do you use the reference to store something that is expensive to compute
--   that you rarely use? If so, you might want to use 'IORef' to
--   avoid doing redundant work, though warnings about repeated read/writes and memory
--   leaks still apply.
--
-- == Caveats
--
-- The API for strict 'IORef' only ensures that the value in the reference is in
-- weak-head normal form, *not* normal form. This is done for the sake of efficiency:
-- using 'Control.DeepSeq.NFData' to place the value into normal form requires us to
-- fully traverse the value being stored inside of the reference, which can be quite
-- expensive for recursive structures.
--
-- This design decision does lead to some unfortunate gotchas. Namely, if you store
-- a type inside of a strict 'IORef' that has non-strict fields, it is still possible
-- to have space/memory leaks. This is best explained by an example:
--
-- @
-- gotcha :: IO ()
-- gotcha = do
--   ref <- Strict.newIORef (Just 1)
--   loop ref (10 ^ 9)
--   n <- Strict.readIORef ref
--   print n
--   where
--     loop :: Strict.IORef (Maybe Int) -> Int -> IO ()
--     loop ref i =
--       if i == 0 then
--         pure ()
--       else do
--         n <- Strict.readIORef ref
--         Strict.writeIORef ref (fmap (+ 1) n)
--         loop ref (i - 1)
-- @
--
-- This leaks even though we are using a strict 'IORef', as 'Agda.Utils.IORef.Strict.writeIORef' only forces the
-- thunk containing the 'Just', and *not* the thunk stored within the 'Just'. Similar problems
-- exist with @Strict.IORef (a, b)@, as pairs in Haskell are lazy.
--
-- In light of this, users are encouraged to use strict 'IORef' in concert with types that have strict
-- fields. This ensures that forcing the outer constructor of the type also forces the fields, avoiding any potential
-- leaks. If this is not possible, users are encouraged to use strict let bindings, 'seq', and
-- extreme care.
--
-- == Implementation notes
--
-- When forcing values to WHNF before writing to the reference, we have two options
--
-- * Use @Lazy.writeIORef ref $! a@
-- * Use @Lazy.writeIORef ref =<< evaluate a@
--
-- These are subtly different in the presence of exceptions. The former
-- unfolds to:
--
-- @
-- let !a' = a
-- in writeIORef ref a'
-- @
--
-- If forcing @a@ to WHNF causes an exception to get thrown, then we don't produce any IO action at
-- all. Conversely, @writeIORef ref =<< evaluate a@ will always produce an IO action that itself will
-- throw when evaluated.
--
-- In practice, this means that
--
-- @
-- (writeIORef ref $! (error "a")) >> error "b"
-- @
--
-- can throw either @"a"@ or @"b"@ depending on what the optimizer decides to do, whereas
--
-- @
-- evaluate (error "a") >>= writeIORef ref >> error "b"
-- @
--
-- must always throw @"a"@.
--
-- We opt to use @writeIORef ref $! a@ in this module, as it gives the optimizer more leeway
-- when doing code transformations that might move where a value gets forced (EG: worker-wrapper).
-- This is a safe choice, as Agda does not rely on precise exception semantics for correctness.

-- | Strict IO references.
newtype IORef a = StrictIORef (Lazy.IORef a)

-- | Create a new strict 'IORef'.
--
-- This will force the value to WHNF before creating the reference.
newIORef :: a -> IO (IORef a)
newIORef = \a -> StrictIORef <$> (Lazy.newIORef $! a)
{-# INLINE newIORef #-}

-- | Read the contents of a strict 'IORef'.
readIORef :: IORef a -> IO a
readIORef = \(StrictIORef ref) -> Lazy.readIORef ref
{-# INLINE readIORef #-}

-- | Write to a strict 'IORef'.
--
-- This will force the value to WHNF before writing.
writeIORef :: IORef a -> a -> IO ()
writeIORef = \(StrictIORef ref) a -> Lazy.writeIORef ref $! a
{-# INLINE writeIORef #-}

-- | Modify a strict 'IORef' by a applying a function to the value stored in the reference.
--
-- This will force the value to WHNF before writing.
modifyIORef :: IORef a -> (a -> a) -> IO ()
modifyIORef = \ref f -> do
  a <- readIORef ref
  writeIORef ref (f a)
{-# INLINE modifyIORef #-}

-- | Atomically modify the contents of a strict 'IORef'.
-- Both the stored value and the result are forced.
atomicModifyIORef :: IORef a -> (a -> (a, b)) -> IO b
atomicModifyIORef (StrictIORef r) = Lazy.atomicModifyIORef' r
