-- Andreas 2015-01-07 fixing polarity of projection-like functions

-- {-# OPTIONS -v tc.polarity:20 -v tc.proj.like:10 #-}
-- {-# OPTIONS -v tc.conv.elim:25 --show-implicit #-}

{-# OPTIONS --sized-types #-}

open import Common.Size

-- List covariant covariant
data List (i : Size) (A : Set) : Set where
  [] : List i A
  cons : ∀{j : Size< i} → A → List j A → List i A

-- Id mixed mixed mixed covariant
-- Id is projection-like in argument l
Id : ∀{i A} (l : List i A) → Set → Set
Id [] X = X
Id (cons _ _) X = X

-- should pass
cast : ∀{i A} (l : List i A) → Id l (List i A) → Id l (List ∞ A)
cast l x = x
