------------------------------------------------------------------------
-- The Maybe type
------------------------------------------------------------------------

module Data.Maybe where

------------------------------------------------------------------------
-- The type

data Maybe (a : Set) : Set where
  just    : a -> Maybe a
  nothing : Maybe a

------------------------------------------------------------------------
-- Maybe monad

open import Monad

MaybeMonad : RawMonad Maybe
MaybeMonad = record
  { return = just
  ; bind   = _>>=_
  }
  where
  _>>=_ : forall {a b} -> Maybe a -> (a -> Maybe b) -> Maybe b
  nothing >>= f = nothing
  just x  >>= f = f x

MaybeMonadZero : RawMonadZero Maybe
MaybeMonadZero = record
  { monad = MaybeMonad
  ; zero  = nothing
  }

MaybeMonadPlus : RawMonadPlus Maybe
MaybeMonadPlus = record
  { monadZero = MaybeMonadZero
  ; plus      = _++_
  }
  where
  _++_ : forall {a} -> Maybe a -> Maybe a -> Maybe a
  nothing ++ y = y
  just x  ++ y = just x
