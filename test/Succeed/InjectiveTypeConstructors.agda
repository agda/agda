{-# OPTIONS --injective-type-constructors #-}

module InjectiveTypeConstructors where

data D (A : Set) : Set where

data _==_ (A : Set) : Set → Set where
  refl : A == A

D' = D

injD : ∀ {A B} → D A == D' B → A == B
injD refl = refl
