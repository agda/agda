module Issue690a where

postulate A : Set

data T : Set → Set where
  c : T (T A)
