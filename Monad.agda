------------------------------------------------------------------------
-- Monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

module Monad where

open import Data.Function
open import Monad.Indexed
open import Data.Unit

RawMonad : (Set -> Set) -> Set1
RawMonad M = RawIMonad {⊤} (\_ _ -> M)

RawMonadZero : (Set -> Set) -> Set1
RawMonadZero M = RawIMonadZero {⊤} (\_ _ -> M)

RawMonadPlus : (Set -> Set) -> Set1
RawMonadPlus M = RawIMonadPlus {⊤} (\_ _ -> M)

module RawMonad {M : Set -> Set}(Mon : RawMonad M) where
  private open module M = RawIMonad Mon public

module RawMonadZero {M : Set -> Set}(Mon : RawMonadZero M) where
  private open module M = RawIMonadZero Mon public

module RawMonadPlus {M : Set -> Set}(Mon : RawMonadPlus M) where
  private open module M = RawIMonadPlus Mon public

module MonadOps (M : Set -> Set) (Mon : RawMonad M) where
  private open module M = IMonadOps _ Mon public

module MonadZeroOps (M : Set -> Set) (Mon : RawMonadZero M) where
  private open module M = IMonadZeroOps _ Mon public

module MonadPlusOps (M : Set -> Set) (Mon : RawMonadPlus M) where
  private open module M = IMonadPlusOps _ Mon public
