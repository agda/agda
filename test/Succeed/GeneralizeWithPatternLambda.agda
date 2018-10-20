
open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

variable
  ℓ : Level
  A  : Set ℓ
  n  : Nat

infixr 4 _∷_

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : A → Vec A n → Vec A (suc n)

variable
  xs : Vec A n

data T (n : Nat) (f : Nat → Nat) : Set where
  it : T n f

appT : ∀ {f} → T n f → Nat
appT {n = n} {f = f} it = f n

length : Vec A n → Nat
length {n = n} _ = n

-- This should not break.
bar : (xs : Vec Nat n) → T n λ { m → m + length xs }
bar xs = it

ys : Vec Nat 5
ys = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

-- Check that it doesn't
no-fail : appT (bar ys) ≡ 10
no-fail = refl
