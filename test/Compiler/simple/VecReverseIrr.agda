
module _ where

open import Common.Prelude

data Vec (A : Set) : ..(_ : Nat) → Set where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

sum : ∀ {n} → Vec Nat n → Nat
sum (x ∷ xs) = x + sum xs
sum [] = 0

foldl : ∀ {A}{B : ..(_ : Nat) → Set} → (∀ ..{n} → B n → A → B (suc n)) → B 0 → ∀ ..{n} → Vec A n → B n
foldl {B = B} f z (x ∷ xs) = foldl {B = λ n → B (suc n)} f (f z x) xs
foldl f z [] = z

reverse : ∀ {A n} → Vec A n → Vec A n
reverse = foldl {B = Vec _} (λ xs x → x ∷ xs) []

downFrom : ∀ n → Vec Nat n
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

len : ∀ {n} → Vec Nat n → Nat
len [] = 0
len (_∷_ {n} x xs) = n

main : IO Unit
main = printNat (sum (reverse (downFrom 6000)))
