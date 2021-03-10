{-# OPTIONS --auto-inline #-}
module _ where

data Sigma (A : Set)(B : A → Set) : Set where
  _,_ : (x : A) → B x → Sigma A B

record Top : Set where

_o_ : {A B : Set}{C : Set1} →
      (f : B → C) → (g : A → B) → (A → C)
f o g = \ x → f (g x)

mutual
  data U  : Set where
    top : U
    sig : (X : U) → (T X → U) → U

  T : U → Set
  T top = Top
  T (sig a b) = Sigma (T a) (T o b)
