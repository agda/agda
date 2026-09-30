data A : Set where
  a : A

data P : A → Set where

data Q : Set where
  cons : P a → Q

x : Q
x = cons {! !}
