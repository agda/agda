module CoinductiveConstructorAndOpenPublic where

module A where

  codata C : Set where
    c : C

  f : C → C
  f c = c

open A public

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

g : C → C
g c = c

lemma : g (f c) ≡ g c
lemma = refl

-- The following problem was due to not unfolding coinductive
-- constructors properly:

-- CoinductiveConstructorAndOpenPublic.agda:20,1-13
-- Incomplete pattern matching for f. No match for c
-- when checking that the clause lemma = refl has type
-- g (f .CoinductiveConstructorAndOpenPublic.c-2) ≡
-- g .CoinductiveConstructorAndOpenPublic.c-3
