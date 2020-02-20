module _ where

open import Common.Prelude

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {@0 n} → A → Vec A n → Vec A (suc n)

sum : ∀ {@0 n} → Vec Nat n → Nat
sum (x ∷ xs) = x + sum xs
sum []       = 0

foldl : ∀ {A} (B : Nat → Set)
      → (f : ∀ {@0 n} → B n → A → B (suc n))
      → (z : B 0)
      → ∀ {@0 n} → Vec A n → B n
foldl B f z (x ∷ xs) = foldl (λ n → B (suc n)) f (f z x) xs
foldl B f z [] = z

reverse : ∀ {A} {@0 n} → Vec A n → Vec A n
reverse = foldl (Vec _) (λ xs x → x ∷ xs) []

downFrom : ∀ n → Vec Nat n
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

main : IO Unit
main = printNat (sum (reverse (downFrom 100000)))
