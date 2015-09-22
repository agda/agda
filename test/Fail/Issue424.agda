{-# OPTIONS --no-unreachable-check #-}

module Issue424 where

data _≡_ {A : Set₁} (x : A) : A → Set where
  refl : x ≡ x

f : Set → Set
f A = A
f A = A

fails : (A : Set) → f A ≡ A
fails A = refl

-- The case tree compiler used to treat f as a definition with an
-- absurd pattern.
