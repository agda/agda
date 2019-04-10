postulate
  I : Set
  f : Set → I

mutual

  data P : I → Set where

  Q : I → Set
  Q x = P (f (P x))
