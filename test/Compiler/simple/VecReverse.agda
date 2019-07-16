
module _ where

open import Common.Prelude
open import Lib.Vec

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
      (f : ∀ {x} (y : B x) → C x y)
      (g : ∀ x → B x)
      → ∀ x → C x (g x)
(f ∘ g) x = f (g x)

sum : ∀ {n} → Vec Nat n → Nat
sum (x ∷ xs) = x + sum xs
sum []       = 0

foldl : ∀ {A} (B : Nat → Set)
      → (∀ {n} → B n → A → B (suc n))
      → B 0
      → ∀ {n} → Vec A n → B n
foldl B f z (x ∷ xs) = foldl (λ n → B (suc n)) f (f z x) xs
foldl B f z [] = z

reverse : ∀ {A n} → Vec A n → Vec A n
reverse = foldl (Vec _) (λ xs x → x ∷ xs) []

downFrom : ∀ n → Vec Nat n
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

main : IO Unit
main = printNat (sum (reverse (downFrom 600)))  -- 10000 gives a stack overflow on JS
