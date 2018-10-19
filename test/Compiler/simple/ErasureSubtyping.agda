-- Andreas, 2018-10-16, erased lambda-arguments

open import Agda.Builtin.List
open import Common.Prelude

sum : List Nat → Nat
sum (x ∷ xs) = x + sum xs
sum [] = 0

zipWith : {A B C : Set} (f : A → B → C) → List A → List B → List C
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
zipWith _ _ _ = []

-- Shorten the first list to the length of the second.

restrict : {A : Set} (xs ys : List A) → List A
restrict = zipWith (λ x (@0 _) → x)

-- It does not matter that we annotated the second argument as erased,
-- since the compiler does not actually erase function arguments, only
-- their content to the empty tuple.  Thus, this is no type error.

main : IO Unit
main = printNat (sum (restrict (13 ∷ 14 ∷ 15 ∷ 16 ∷ []) (1 ∷ 2 ∷ 3 ∷ [])))

-- Expected output: 42
