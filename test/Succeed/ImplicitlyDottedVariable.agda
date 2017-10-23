open import Agda.Builtin.Nat

data Vec (A : Set) : Nat → Set where
  [] : Vec A 0
  cons : (n : Nat) → A → Vec A n → Vec A (suc n)

tail : {A : Set} (n : Nat) → Vec A (suc n) → Vec A n
tail n (cons n x xs) = xs

tail' : {A : Set} (n : Nat) → Vec A (suc n) → Vec A n
tail' 0 (cons 0 x []) = []
tail' (suc n) (cons (suc n) x (cons n x₁ xs)) = (cons n x₁ xs)
