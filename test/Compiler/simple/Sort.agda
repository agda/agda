
module _ where

open import Common.Prelude

_<_ : Nat → Nat → Bool
a < b with b ∸ a
... | zero  = false
... | suc _ = true

insert : Nat → List Nat → List Nat
insert x [] = x ∷ []
insert x (y ∷ xs) = if x < y then x ∷ y ∷ xs else (y ∷ insert x xs)

sort : List Nat → List Nat
sort [] = []
sort (x ∷ xs) = insert x (sort xs)

downFrom : Nat → List Nat
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

mapM! : {A : Set} → (A → IO Unit) → List A → IO Unit
mapM! f [] = return unit
mapM! f (x ∷ xs) = f x >>= λ _ → mapM! f xs

main : IO Unit
main = mapM! printNat (sort (downFrom 1200))

-- 1000   0.6s
-- 2000   4.8s
-- 4000   36.2s
