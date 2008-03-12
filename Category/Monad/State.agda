------------------------------------------------------------------------
-- The state monad
------------------------------------------------------------------------

module Category.Monad.State where

open import Category.Monad
open import Category.Monad.Indexed
open import Category.Monad.Identity
open import Data.Product
open import Data.Function
open import Data.Unit
open import Category.Applicative.Indexed

------------------------------------------------------------------------
-- Indexed state monads

IStateT : {I : Set} -> (I -> Set) -> (Set -> Set) -> IFun I
IStateT S M i j A = S i -> M (A × S j)

StateTIMonad : forall {I} (S : I -> Set) {M} ->
               RawMonad M -> RawIMonad (IStateT S M)
StateTIMonad S Mon = record
  { return = \x s -> return (x , s)
  ; _>>=_  = \m f s -> m s >>= uncurry f
  }
  where open RawMonad Mon

StateTIMonadZero : forall {I} (S : I -> Set) {M} ->
                   RawMonadZero M -> RawIMonadZero (IStateT S M)
StateTIMonadZero S Mon = record
  { monad = StateTIMonad S (RawMonadZero.monad Mon)
  ; ∅     = const ∅
  }
  where open RawMonadZero Mon

StateTIMonadPlus : forall {I} (S : I -> Set) {M} ->
                   RawMonadPlus M -> RawIMonadPlus (IStateT S M)
StateTIMonadPlus S Mon = record
  { monadZero = StateTIMonadZero S (RawIMonadPlus.monadZero Mon)
  ; _∣_       = \m₁ m₂ s -> m₁ s ∣ m₂ s
  }
  where open RawMonadPlus Mon

------------------------------------------------------------------------
-- Ordinary state monads

StateT : Set -> (Set -> Set) -> Set -> Set
StateT S M = IStateT {⊤} (\_ -> S) M _ _

State : Set -> Set -> Set
State S = StateT S Identity

StateMonad : (S : Set) -> RawMonad (State S)
StateMonad S = StateTIMonad _ IdentityMonad

------------------------------------------------------------------------
-- State monad operations

record RawIMonadState {I : Set} (S : I -> Set)
                      (M : I -> I -> Set -> Set) : Set1 where
  field
    monad : RawIMonad M
    get   : forall {i} -> M i i (S i)
    put   : forall {i j} -> S j -> M i j ⊤

  open RawIMonad monad public

  modify : forall {i j} -> (S i -> S j) -> M i j ⊤
  modify f = get >>= put ∘ f

StateTIMonadState : forall {I} (S : I -> Set) {M} ->
                    RawMonad M -> RawIMonadState S (IStateT S M)
StateTIMonadState S Mon = record
  { monad = StateTIMonad S Mon
  ; get   = \s   -> return (s , s)
  ; put   = \s _ -> return (_ , s)
  }
  where open RawIMonad Mon
