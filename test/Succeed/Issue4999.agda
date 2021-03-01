
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Equality

data ⊥ : Set where

infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

<?> = '\xFFFD'

infix 0 _∋_
_∋_ : (A : Set) → A → A
A ∋ x = x

_ = primNatToChar 0xD7FF ≢ <?> ∋ λ ()
_ = primNatToChar 0xD800 ≡ <?> ∋ refl
_ = primNatToChar 0xDFFF ≡ <?> ∋ refl
_ = primNatToChar 0xE000 ≢ <?> ∋ λ ()
