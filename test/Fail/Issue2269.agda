{-# OPTIONS --instance-search-depth=10 #-}
data ⊥ : Set where

it : {A : Set} {{_ : A}} → A
it {{x}} = x

postulate Eq : Set → Set

instance
  postulate weaken : {{_ : Eq ⊥}} → Eq _

loop : Eq ⊥
loop = it
