{-# LANGUAGE TypeFamilies, FlexibleInstances, StandaloneDeriving #-}
module Terms.None where

import Control.Applicative

import Types.Monad

data None = None

instance Functor (TermMonad None) where
  fmap f (TMNone x) = TMNone (f x)

instance Applicative (TermMonad None) where
  pure = TMNone
  TMNone f <*> TMNone x = TMNone (f x)

-- deriving instance Applicative (TermMonad None)
instance Monad (TermMonad None) where
  return = TMNone
  TMNone x >>= f = f x

instance TermRep None where
  type Var None = ()
  type Term None = ()
  type Type None = ()
  type Context None = ()
  newtype TermMonad None a = TMNone { unTMNone :: a }
  type TermState None = ()

  liftTC (TMNone x) = return x

  initialTermState = return ()
  emptyCxt = return ()
  lookupCxt x cxt = return ((), TypedVar x ())
  extendCxt e cxt = return ()
  updateCxt x e cxt = return ()

