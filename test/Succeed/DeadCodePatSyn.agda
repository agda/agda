
module _ where

open import DeadCodePatSyn.Lib

typeOf : {A : Set} → A → Set
typeOf {A} _ = A

-- Check that pattern synonyms count when computing dead code
f : typeOf not-hidden → Set₁
f not-hidden = Set
