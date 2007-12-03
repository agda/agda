------------------------------------------------------------------------
-- Monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

module Category.Monad.Indexed where

open import Data.Function
open import Category.Applicative.Indexed

record RawIMonad {I : Set}(M : IFun I) : Set1 where
  infixl 1 _>>=_
  field
    return : forall {i A} -> A -> M i i A
    _>>=_  : forall {i j k A B} -> M i j A -> (A -> M j k B) -> M i k B

record RawIMonadZero {I : Set}(M : IFun I) : Set1 where
  field
    monad : RawIMonad M
    mzero : forall {i j A} -> M i j A

record RawIMonadPlus {I : Set}(M : IFun I) : Set1 where
  infixr 5 _++_
  field
    monadZero : RawIMonadZero M
    _++_      : forall {i j A} -> M i j A -> M i j A -> M i j A

module IMonadOps {I : Set} {M : IFun I}
                 (Mon : RawIMonad M)
                 where

  open RawIMonad Mon public

  infixl 1 _>>_
  infixr 1 _=<<_

  _>>_ : forall {i j k A B} -> M i j A -> M j k B -> M i k B
  m₁ >> m₂ = m₁ >>= \_ -> m₂

  _=<<_ : forall {i j k A B} -> (A -> M j k B) -> M i j A -> M i k B
  f =<< c = c >>= f

  rawIApplicative : RawIApplicative M
  rawIApplicative = record
    { pure  = return
    ; _<*>_ = \f x -> f >>= \f' -> x >>= \x' -> return (f' x')
    }

  open IApplicativeOps rawIApplicative public

module IMonadZeroOps {I : Set} {M : IFun I}
                     (Mon : RawIMonadZero M)
                     where
  open RawIMonadZero Mon public
  open IMonadOps monad public

module IMonadPlusOps {I : Set} {M : IFun I}
                     (Mon : RawIMonadPlus M) where

  open RawIMonadPlus Mon public
  open IMonadZeroOps monadZero public
