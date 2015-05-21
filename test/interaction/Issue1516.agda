
{-# OPTIONS --copatterns #-}

record U : Set where
  coinductive
  field out : U

u : {A : Set} → U
u = {!!}

record Wrap (A : Set) : Set where
  field
    wrapped : A

wrap : ∀{A}{a : A} → Wrap A
wrap = {!!}
