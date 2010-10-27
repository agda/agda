
module Pointer where

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

newtype Ptr a = Ptr { rawPtr :: Int }
    deriving (Eq, Ord)

data Heap a = Heap { nextPtr :: Int
		   , thunks  :: Map (Ptr a) a
		   }

type HeapM a = State (Heap a)

runHeap :: HeapM a b -> b
runHeap h = evalState h (Heap 0 Map.empty)

deref :: Ptr a -> HeapM a a
deref p = do
    heap <- gets thunks
    return $ heap Map.! p

store :: Ptr a -> a -> HeapM a ()
store p v = modify $ \h -> h { thunks = Map.insert p v $ thunks h }

free :: Ptr a -> HeapM a ()
free p = modify $ \h -> h { thunks = Map.delete p $ thunks h }

fresh :: HeapM a (Ptr a)
fresh = do
    h <- get
    let n = nextPtr h
    put $ h { nextPtr = n + 1 }
    return $ Ptr n

onThunk :: Ptr a -> (a -> HeapM a a) -> HeapM a a
onThunk p f = do
    v <- deref p
    w <- f v
    store p w
    return w

alloc :: a -> HeapM a (Ptr a)
alloc v = do
    p <- fresh
    store p v
    return p
