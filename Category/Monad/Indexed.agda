------------------------------------------------------------------------
-- Monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

module Category.Monad.Indexed where

open import Data.Function

record RawIMonad {I : Set}(M : I -> I -> Set -> Set) : Set1 where
  return : forall {i a} -> a -> M i i a
  bind   : forall {i j k a b} -> M i j a -> (a -> M j k b) -> M i k b

record RawIMonadZero {I : Set}(M : I -> I -> Set -> Set) : Set1 where
  monad  : RawIMonad M
  mzero  : forall {i j a} -> M i j a

record RawIMonadPlus {I : Set}(M : I -> I -> Set -> Set) : Set1 where
  monadZero : RawIMonadZero M
  plus      : forall {i j a} -> M i j a -> M i j a -> M i j a

module IMonadOps {I : Set}(M : I -> I -> Set -> Set) (Mon : RawIMonad M) where

  private
    module MM = RawIMonad Mon
    open MM public using (return)

  infixl 4 _<$>_ _<*>_
  infixl 1 _>>=_ _>>_
  infixr 1 _=<<_

  _>>=_ : forall {i j k a b} -> M i j a -> (a -> M j k b) -> M i k b
  _>>=_ = MM.bind

  _>>_ : forall {i j k a b} -> M i j a -> M j k b -> M i k b
  m₁ >> m₂ = m₁ >>= \_ -> m₂

  _=<<_ : forall {i j k a b} -> (a -> M j k b) -> M i j a -> M i k b
  f =<< c = c >>= f

  -- _<$>_ is also known as liftM.

  _<$>_ : forall {i j a b} -> (a -> b) -> M i j a -> M i j b
  f <$> x = x >>= (return ∘ f)

  _<*>_ : forall {i j k a b} -> M i j (a -> b) -> M j k a -> M i k b
  f <*> x = f >>= \f' -> x >>= \x' -> return (f' x')

  liftM₂ : forall {i j k a b c} -> (a -> b -> c) -> M i j a -> M j k b -> M i k c
  liftM₂ f x y = f <$> x <*> y

module IMonadZeroOps {I : Set}(M : I -> I -> Set -> Set) (Mon : RawIMonadZero M) where

  private
    module MZ = RawIMonadZero Mon
    open MZ public using (mzero)
    open module MO = IMonadOps M MZ.monad public

module IMonadPlusOps {I : Set}(M : I -> I -> Set -> Set) (Mon : RawIMonadPlus M) where

  private
    module MP = RawIMonadPlus Mon
    open module MZO = IMonadZeroOps M MP.monadZero public

  infixr 5 _++_

  _++_ : forall {i j a} -> M i j a -> M i j a -> M i j a
  _++_ = MP.plus
