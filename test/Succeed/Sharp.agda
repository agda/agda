{-# OPTIONS --cohesion #-}

module _ where

data Sharp (@♯ A : Set) : Set where
  con : (@♯ x : A) → Sharp A

{-# MODALOP Sharp #-}

unit : {A : Set} → A → Sharp A
unit x = con x

mult : {A : Set} → Sharp (Sharp A) → Sharp A
mult (con (con x)) = con x

counit : ∀ {@♭ A : Set} → @♭ (Sharp A) → A
counit (con x) = x

postulate
  A : Set
  P : @♭ A → Set
  p : (@♭ a : A) → P a

test : (a : A) → Sharp (P a)
test a = con (p a)
