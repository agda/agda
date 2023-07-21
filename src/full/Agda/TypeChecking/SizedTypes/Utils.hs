{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.SizedTypes.Utils where

import Data.IORef
import qualified Debug.Trace as Debug
import System.IO.Unsafe

import Agda.Utils.Function

{-# NOINLINE debug #-}
debug :: IORef Bool
debug = unsafePerformIO $ newIORef False

setDebugging :: Bool -> IO ()
setDebugging = writeIORef debug

trace :: String -> a -> a
trace s = applyWhen (unsafePerformIO $ readIORef debug) $ Debug.trace s

traceM :: Applicative f => String -> f ()
traceM s = trace s $ pure ()

class Eq a => Top a where
  top   :: a
  isTop :: a -> Bool
  isTop = (==top)

class Plus a b c where
  plus :: a -> b -> c

instance Plus Int Int Int where
  plus = (+)

class MeetSemiLattice a where
  meet :: a -> a -> a

-- | Semiring with idempotent '+' == dioid
class (MeetSemiLattice a, Top a) => Dioid a where
  compose     :: a -> a -> a  -- ^ E.g. +
  unitCompose :: a            -- ^ neutral element of @compose@, e.g. zero
