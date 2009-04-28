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

IStateT : {I : Set} → (I → Set) → (Set → Set) → IFun I
IStateT S M i j A = S i → M (A × S j)

StateTIMonad : ∀ {I} (S : I → Set) {M} →
               RawMonad M → RawIMonad (IStateT S M)
StateTIMonad S Mon = record
  { return = λ x s → return (x , s)
  ; _>>=_  = λ m f s → m s >>= uncurry f
  }
  where open RawMonad Mon

StateTIMonadZero : ∀ {I} (S : I → Set) {M} →
                   RawMonadZero M → RawIMonadZero (IStateT S M)
StateTIMonadZero S Mon = record
  { monad = StateTIMonad S (RawMonadZero.monad Mon)
  ; ∅     = const ∅
  }
  where open RawMonadZero Mon

StateTIMonadPlus : ∀ {I} (S : I → Set) {M} →
                   RawMonadPlus M → RawIMonadPlus (IStateT S M)
StateTIMonadPlus S Mon = record
  { monadZero = StateTIMonadZero S (RawIMonadPlus.monadZero Mon)
  ; _∣_       = λ m₁ m₂ s → m₁ s ∣ m₂ s
  }
  where open RawMonadPlus Mon

------------------------------------------------------------------------
-- State monad operations

record RawIMonadState {I : Set} (S : I → Set)
                      (M : I → I → Set → Set) : Set₁ where
  field
    monad : RawIMonad M
    get   : ∀ {i} → M i i (S i)
    put   : ∀ {i j} → S j → M i j ⊤

  open RawIMonad monad public

  modify : ∀ {i j} → (S i → S j) → M i j ⊤
  modify f = get >>= put ∘ f

StateTIMonadState : ∀ {I} (S : I → Set) {M} →
                    RawMonad M → RawIMonadState S (IStateT S M)
StateTIMonadState S Mon = record
  { monad = StateTIMonad S Mon
  ; get   = λ s   → return (s , s)
  ; put   = λ s _ → return (_ , s)
  }
  where open RawIMonad Mon

------------------------------------------------------------------------
-- Ordinary state monads

RawMonadState : Set → (Set → Set) → Set₁
RawMonadState S M = RawIMonadState {⊤} (λ _ → S) (λ _ _ → M)

module RawMonadState {S : Set} {M : Set → Set}
                     (Mon : RawMonadState S M) where
  open RawIMonadState Mon public

StateT : Set → (Set → Set) → Set → Set
StateT S M = IStateT {⊤} (λ _ → S) M _ _

StateTMonad : ∀ S {M} → RawMonad M → RawMonad (StateT S M)
StateTMonad S = StateTIMonad (λ _ → S)

StateTMonadZero : ∀ S {M} → RawMonadZero M → RawMonadZero (StateT S M)
StateTMonadZero S = StateTIMonadZero (λ _ → S)

StateTMonadPlus : ∀ S {M} → RawMonadPlus M → RawMonadPlus (StateT S M)
StateTMonadPlus S = StateTIMonadPlus (λ _ → S)

StateTMonadState : ∀ S {M} → RawMonad M → RawMonadState S (StateT S M)
StateTMonadState S = StateTIMonadState (λ _ → S)

State : Set → Set → Set
State S = StateT S Identity

StateMonad : (S : Set) → RawMonad (State S)
StateMonad S = StateTMonad S IdentityMonad

StateMonadState : ∀ S → RawMonadState S (State S)
StateMonadState S = StateTMonadState S IdentityMonad

LiftMonadState : ∀ {S₁} S₂ {M} →
                 RawMonadState S₁ M →
                 RawMonadState S₁ (StateT S₂ M)
LiftMonadState S₂ Mon = record
  { monad = StateTIMonad (λ _ → S₂) monad
  ; get   = λ s → get >>= λ x → return (x , s)
  ; put   = λ s′ s → put s′ >> return (_ , s)
  }
  where open RawIMonadState Mon
