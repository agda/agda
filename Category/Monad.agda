------------------------------------------------------------------------
-- Monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

module Category.Monad where

open import Data.Function
open import Category.Monad.Indexed
open import Data.Unit

RawMonad : (Set -> Set) -> Set1
RawMonad M = RawIMonad {⊤} (\_ _ -> M)

RawMonadZero : (Set -> Set) -> Set1
RawMonadZero M = RawIMonadZero {⊤} (\_ _ -> M)

RawMonadPlus : (Set -> Set) -> Set1
RawMonadPlus M = RawIMonadPlus {⊤} (\_ _ -> M)

module RawMonad {M : Set -> Set} (Mon : RawMonad M) where
  open RawIMonad Mon public

module RawMonadZero {M : Set -> Set} (Mon : RawMonadZero M) where
  open RawIMonadZero Mon public

module RawMonadPlus {M : Set -> Set} (Mon : RawMonadPlus M) where
  open RawIMonadPlus Mon public
