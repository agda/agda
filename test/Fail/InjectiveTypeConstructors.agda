-- Needs the --injective-type-constructors option enabled to type check.
module InjectiveTypeConstructors where

data D (A : Set) : Set where

data _==_ (A : Set) : Set → Set where
  refl : A == A

injD : ∀ {A B} → D A == D B → A == B
injD refl = refl
