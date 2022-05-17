-- Andreas, 2015-06-28
-- {-# OPTIONS -v tc.polarity:20  #-}

{-# OPTIONS --sized-types #-}

open import Common.Size

-- List should be monotone in both arguments
-- (even as phantom type).

data List (i : Size) (A : Set) : Set where
  [] : List i A

castL : ∀{i A} → List i A → List ∞ A
castL x = x

castLL : ∀{i A} → List i (List i A) → List ∞ (List ∞ A)
castLL x = x

-- Stream should be antitone in the first and monotone in the second argument
-- (even with field `tail' missing).

record Stream (i : Size) (A : Set) : Set where
  coinductive
  field
    head : A

castS : ∀{i A} → Stream ∞ A → Stream i A
castS x = x

castSS : ∀{i A} → Stream ∞ (Stream ∞ A) → Stream i (Stream i A)
castSS x = x
