-- Andreas, 2016-05-04 shrunk from the standard library

open import Common.Product

record ⊤ : Set where

IFun : Set → Set1
IFun I = I → I → Set → Set

------------------------------------------------------------------------
-- Indexed state monads

record RawIMonad {I : Set} (M : (i j : I) → Set → Set) : Set1 where
  field
    return : ∀ {i A} → A → M i i A
    _>>=_  : ∀ {i j k A B} → M i j A → (A → M j k B) → M i k B

record RawIMonadZero  {I : Set} (M : IFun I) : Set1 where
  field
    monad : RawIMonad M
    ∅     : ∀ {i j A} → M i j A

  open RawIMonad monad public

record RawIMonadPlus  {I : Set} (M : IFun I) : Set1 where
  field
    monadZero : RawIMonadZero M
    _∣_       : ∀ {i j A} → M i j A → M i j A → M i j A

  open RawIMonadZero monadZero public


RawMonad : (Set → Set) → Set1
RawMonad M = RawIMonad {I = ⊤} (λ _ _ → M)

RawMonadZero : (Set → Set) → Set1
RawMonadZero M = RawIMonadZero {I = ⊤} (λ _ _ → M)

RawMonadPlus : (Set → Set) → Set1
RawMonadPlus M = RawIMonadPlus {I = ⊤} (λ _ _ → M)

module RawMonad {M : Set → Set} (Mon : RawMonad M) where
  open RawIMonad Mon public

module RawMonadZero {M : Set → Set} (Mon : RawMonadZero M) where
  open RawIMonadZero Mon public

module RawMonadPlus {M : Set → Set} (Mon : RawMonadPlus M) where
  open RawIMonadPlus Mon public



IStateT : ∀  {I : Set} (S : I → Set) (M : Set → Set) (i j : I) (A : Set) → Set
IStateT S M i j A = S i → M (A × S j)

StateTIMonad : ∀ {I : Set} (S : I → Set) {M} →
               RawMonad M → RawIMonad (IStateT S M)
StateTIMonad S Mon = record
  { return = λ x s → return (x , s)
  ; _>>=_  = λ m f s → m s >>= λ as → let a , s' = as in f a s'
  }
  where open RawMonad Mon

StateTIMonadZero : ∀ {I : Set} (S : I → Set) {M} →
                   RawMonadZero M → RawIMonadZero (IStateT S M)
StateTIMonadZero S Mon = record
  { monad = StateTIMonad S (RawMonadZero.monad Mon)
  ; ∅     = λ s → ∅
  }
  where open RawMonadZero Mon

StateTIMonadPlus : ∀ {I : Set} (S : I → Set) {M} →
                   RawMonadPlus M → RawIMonadPlus (IStateT S M)
StateTIMonadPlus S Mon = record
  { monadZero = StateTIMonadZero S (RawIMonadPlus.monadZero Mon)
  ; _∣_       = λ m₁ m₂ s → m₁ s ∣ m₂ s
  }
  where open RawMonadPlus Mon

-- test = {!RawIMonadPlus.monadZero!}
-- test' = {! RawMonadPlus.monadZero !}
