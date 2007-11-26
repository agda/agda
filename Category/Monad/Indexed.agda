------------------------------------------------------------------------
-- Monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

module Category.Monad.Indexed where

open import Data.Function
open import Category.Applicative.Indexed

record RawIMonad {I : Set}(M : IFun I) : Set1 where
  return : forall {i A} -> A -> M i i A
  bind   : forall {i j k A B} -> M i j A -> (A -> M j k B) -> M i k B

record RawIMonadZero {I : Set}(M : IFun I) : Set1 where
  monad : RawIMonad M
  mzero : forall {i j A} -> M i j A

record RawIMonadPlus {I : Set}(M : IFun I) : Set1 where
  monadZero : RawIMonadZero M
  plus      : forall {i j A} -> M i j A -> M i j A -> M i j A

module IMonadOps {I : Set} {M : IFun I}
                 (Mon : RawIMonad M)
                 where

  private
    module MM = RawIMonad Mon
    open MM public using (return)

  infixl 1 _>>=_ _>>_
  infixr 1 _=<<_

  _>>=_ : forall {i j k A B} -> M i j A -> (A -> M j k B) -> M i k B
  _>>=_ = MM.bind

  _>>_ : forall {i j k A B} -> M i j A -> M j k B -> M i k B
  m₁ >> m₂ = m₁ >>= \_ -> m₂

  _=<<_ : forall {i j k A B} -> (A -> M j k B) -> M i j A -> M i k B
  f =<< c = c >>= f

  rawIApplicative : RawIApplicative M
  rawIApplicative = record
    { pure = return
    ; fapp = \f x -> f >>= \f' -> x >>= \x' -> return (f' x')
    }

  private
    open module RIA = IApplicativeOps rawIApplicative public

module IMonadZeroOps {I : Set} {M : IFun I}
                     (Mon : RawIMonadZero M)
                     where

  private
    module MZ = RawIMonadZero Mon
    open MZ public using (mzero)
    open module MO = IMonadOps MZ.monad public

module IMonadPlusOps {I : Set} {M : IFun I}
                     (Mon : RawIMonadPlus M) where

  private
    module MP = RawIMonadPlus Mon
    open module MZO = IMonadZeroOps MP.monadZero public

  infixr 5 _++_

  _++_ : forall {i j A} -> M i j A -> M i j A -> M i j A
  _++_ = MP.plus
