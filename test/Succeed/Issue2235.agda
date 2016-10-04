
data ⊥ : Set where

data Bool : Set where
  false true : Bool

data _≡_ (x : Bool) : Bool → Set where
  refl : x ≡ x

true≠false : false ≡ true → ⊥
true≠false ()
