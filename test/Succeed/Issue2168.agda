-- Andreas, 2016-09-09 issue #2168 reported by Nisse
-- {-# OPTIONS -v tc.cover.splittree:30 -v tc.cc:40 #-}

open import Common.Equality

data Unit : Set where
  unit : Unit

data Bool : Set where
  true false : Bool

f : Unit → Bool → Bool
f unit true = false
f = λ _ _ → true

-- Testing definitional equality:

f-1 : f unit true ≡ false
f-1 = refl

f-2 : f unit false ≡ true
f-2 = refl
