module Issue318 where

data Bool : Set where

module A where
  data _≤_ : Bool → Bool → Set where

open A hiding (_≤_)

data _≤_ : Bool → Bool → Set where