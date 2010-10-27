{-# OPTIONS_GHC -fglasgow-exts #-}

module PointerST where

import Control.Monad.ST
import Data.STRef
import qualified Data.Map as Map

type Ptr s a = STRef s a

type HeapM = ST

runHeap :: (forall s. HeapM s a) -> a
runHeap h = runST h

deref :: Ptr s a -> HeapM s a
deref p = readSTRef p

store :: Ptr s a -> a -> HeapM s ()
store p v = writeSTRef p v

free :: Ptr s a -> HeapM s ()
free p = return ()

alloc :: a -> HeapM s (Ptr s a)
alloc = newSTRef

onThunk :: Ptr s a -> (a -> HeapM s a) -> HeapM s a
onThunk p f = do
    v <- deref p
    w <- f v
    store p w
    return w
