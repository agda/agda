
module Issue422 where

data Bool : Set where
  true false : Bool

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

foo : Bool → Bool → Bool
foo true  b    = b
foo n      true = true
foo false b    = false

good : foo false true ≡ true
good = refl
