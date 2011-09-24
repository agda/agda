------------------------------------------------------------------------
-- The Agda standard library
--
-- The state monad
------------------------------------------------------------------------

module Category.Monad.State where

open import Category.Applicative.Indexed
open import Category.Monad
open import Category.Monad.Identity
open import Category.Monad.Indexed
open import Data.Product
open import Data.Unit
open import Function
open import Level

------------------------------------------------------------------------
-- Indexed state monads

IStateT : ∀ {i f} {I : Set i} → (I → Set f) → (Set f → Set f) → IFun I f
IStateT S M i j A = S i → M (A × S j)

StateTIMonad : ∀ {i f} {I : Set i} (S : I → Set f) {M} →
               RawMonad M → RawIMonad (IStateT S M)
StateTIMonad S Mon = record
  { return = λ x s → return (x , s)
  ; _>>=_  = λ m f s → m s >>= uncurry f
  }
  where open RawMonad Mon

StateTIMonadZero : ∀ {i f} {I : Set i} (S : I → Set f) {M} →
                   RawMonadZero M → RawIMonadZero (IStateT S M)
StateTIMonadZero S Mon = record
  { monad = StateTIMonad S (RawMonadZero.monad Mon)
  ; ∅     = const ∅
  }
  where open RawMonadZero Mon

StateTIMonadPlus : ∀ {i f} {I : Set i} (S : I → Set f) {M} →
                   RawMonadPlus M → RawIMonadPlus (IStateT S M)
StateTIMonadPlus S Mon = record
  { monadZero = StateTIMonadZero S (RawIMonadPlus.monadZero Mon)
  ; _∣_       = λ m₁ m₂ s → m₁ s ∣ m₂ s
  }
  where open RawMonadPlus Mon

------------------------------------------------------------------------
-- State monad operations

record RawIMonadState {i f} {I : Set i} (S : I → Set f)
                      (M : IFun I f) : Set (i ⊔ suc f) where
  field
    monad : RawIMonad M
    get   : ∀ {i} → M i i (S i)
    put   : ∀ {i j} → S j → M i j (Lift ⊤)

  open RawIMonad monad public

  modify : ∀ {i j} → (S i → S j) → M i j (Lift ⊤)
  modify f = get >>= put ∘ f

StateTIMonadState : ∀ {i f} {I : Set i} (S : I → Set f) {M} →
                    RawMonad M → RawIMonadState S (IStateT S M)
StateTIMonadState S Mon = record
  { monad = StateTIMonad S Mon
  ; get   = λ s   → return (s , s)
  ; put   = λ s _ → return (_ , s)
  }
  where open RawIMonad Mon

------------------------------------------------------------------------
-- Ordinary state monads

RawMonadState : ∀ {f} → Set f → (Set f → Set f) → Set _
RawMonadState S M = RawIMonadState {I = ⊤} (λ _ → S) (λ _ _ → M)

module RawMonadState {f} {S : Set f} {M : Set f → Set f}
                     (Mon : RawMonadState S M) where
  open RawIMonadState Mon public

StateT : ∀ {f} → Set f → (Set f → Set f) → Set f → Set f
StateT S M = IStateT {I = ⊤} (λ _ → S) M _ _

StateTMonad : ∀ {f} (S : Set f) {M} → RawMonad M → RawMonad (StateT S M)
StateTMonad S = StateTIMonad (λ _ → S)

StateTMonadZero : ∀ {f} (S : Set f) {M} →
                  RawMonadZero M → RawMonadZero (StateT S M)
StateTMonadZero S = StateTIMonadZero (λ _ → S)

StateTMonadPlus : ∀ {f} (S : Set f) {M} →
                  RawMonadPlus M → RawMonadPlus (StateT S M)
StateTMonadPlus S = StateTIMonadPlus (λ _ → S)

StateTMonadState : ∀ {f} (S : Set f) {M} →
                   RawMonad M → RawMonadState S (StateT S M)
StateTMonadState S = StateTIMonadState (λ _ → S)

State : ∀ {f} → Set f → Set f → Set f
State S = StateT S Identity

StateMonad : ∀ {f} (S : Set f) → RawMonad (State S)
StateMonad S = StateTMonad S IdentityMonad

StateMonadState : ∀ {f} (S : Set f) → RawMonadState S (State S)
StateMonadState S = StateTMonadState S IdentityMonad

LiftMonadState : ∀ {f S₁} (S₂ : Set f) {M} →
                 RawMonadState S₁ M →
                 RawMonadState S₁ (StateT S₂ M)
LiftMonadState S₂ Mon = record
  { monad = StateTIMonad (λ _ → S₂) monad
  ; get   = λ s → get >>= λ x → return (x , s)
  ; put   = λ s′ s → put s′ >> return (_ , s)
  }
  where open RawIMonadState Mon
