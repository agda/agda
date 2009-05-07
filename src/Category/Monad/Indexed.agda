------------------------------------------------------------------------
-- Indexed monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

module Category.Monad.Indexed where

open import Data.Function
open import Category.Applicative.Indexed

record RawIMonad {I : Set} (M : IFun I) : Set₁ where
  infixl 1 _>>=_ _>>_
  infixr 1 _=<<_

  field
    return : ∀ {i A} → A → M i i A
    _>>=_  : ∀ {i j k A B} → M i j A → (A → M j k B) → M i k B

  _>>_ : ∀ {i j k A B} → M i j A → M j k B → M i k B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : ∀ {i j k A B} → (A → M j k B) → M i j A → M i k B
  f =<< c = c >>= f

  join : ∀ {i j k A} → M i j (M j k A) → M i k A
  join m = m >>= id

  rawIApplicative : RawIApplicative M
  rawIApplicative = record
    { pure = return
    ; _⊛_  = λ f x → f >>= λ f' → x >>= λ x' → return (f' x')
    }

  open RawIApplicative rawIApplicative public

record RawIMonadZero {I : Set} (M : IFun I) : Set₁ where
  field
    monad : RawIMonad M
    ∅     : ∀ {i j A} → M i j A

  open RawIMonad monad public

record RawIMonadPlus {I : Set} (M : IFun I) : Set₁ where
  infixr 3 _∣_
  field
    monadZero : RawIMonadZero M
    _∣_       : ∀ {i j A} → M i j A → M i j A → M i j A

  open RawIMonadZero monadZero public
