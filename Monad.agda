------------------------------------------------------------------------
-- Monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

module Monad where

open import Data.Function

record RawMonad (M : Set -> Set) : Set1 where
  return : forall {a} -> a -> M a
  bind   : forall {a b} -> M a -> (a -> M b) -> M b

record RawMonadZero (M : Set -> Set) : Set1 where
  monad  : RawMonad M
  zero   : forall {a} -> M a

record RawMonadPlus (M : Set -> Set) : Set1 where
  monadZero : RawMonadZero M
  plus      : forall {a} -> M a -> M a -> M a

module MonadOps (M : Set -> Set) (Mon : RawMonad M) where

  private
    module MM = RawMonad Mon
    open MM public using (return)

  infixl 4 _<*>_
  infixl 3 _ap_
  infixl 1 _>>=_
  infixr 1 _=<<_

  _>>=_ : forall {a b} -> M a -> (a -> M b) -> M b
  _>>=_ = MM.bind

  _=<<_ : forall {a b} -> (a -> M b) -> M a -> M b
  f =<< c = c >>= f

  -- _<*>_ is also known as liftM.

  _<*>_ : forall {a b} -> (a -> b) -> M a -> M b
  f <*> x = x >>= (return ∘ f)

  liftM₂ : forall {a b c} -> (a -> b -> c) -> M a -> M b -> M c
  liftM₂ f x y = x >>= \x' -> y >>= \y' -> return (f x' y')

  _ap_ : forall {a b} -> M (a -> b) -> M a -> M b
  f ap x = f >>= \f' -> x >>= \x' -> return (f' x')

module MonadZeroOps (M : Set -> Set) (Mon : RawMonadZero M) where

  private
    module MZ = RawMonadZero Mon
    open MZ public using (zero)
    open module MO = MonadOps M MZ.monad public

module MonadPlusOps (M : Set -> Set) (Mon : RawMonadPlus M) where

  private
    module MP = RawMonadPlus Mon
    open module MZO = MonadZeroOps M MP.monadZero public

  infixr 5 _++_

  _++_ : forall {a} -> M a -> M a -> M a
  _++_ = MP.plus
