-- {-# OPTIONS -v treeless.opt:20 #-}
   -- Andreas, 2019-05-07, #3732: cannot have treeless printout in golden value
   -- because it is different for the MAlonzo and JS versions now.

module _ where

open import Common.Prelude

module _ {a} {A : Set a} (_<_ : A → A → Bool) where
  merge : List A → List A → List A
  merge [] ys = ys
  merge xs [] = xs
  merge xs@(x ∷ xs₁) ys@(y ∷ ys₁) =
    if x < y then (x ∷ merge xs₁ ys)  -- Generated treeless code should preserve
             else (y ∷ merge xs ys₁)  -- xs and ys (and not expand to _∷_).

open import Agda.Builtin.Nat

mapM! : {A : Set} → (A → IO Unit) → List A → IO Unit
mapM! f [] = return unit
mapM! f (x ∷ xs) = f x >>= λ _ → mapM! f xs

xs ys : List Nat
xs = 2 ∷ 3 ∷ 5 ∷ 10 ∷ 20 ∷ []
ys = 0 ∷ 1 ∷ 2 ∷ 8 ∷ 10 ∷ 15 ∷ []

main : IO Unit
main = mapM! printNat (merge _<_ xs ys)
