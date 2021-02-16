{-# OPTIONS --show-implicit #-}

data Bool : Set where
  true : Bool
  false : Bool

data D : Set where
  d : D

data E : Set where
  e : E

HSet : Set₁
HSet = {b : Bool} → Set

-- Here HA is HSet
-- The output of this function is the set E, for input HSet G.
⊨_ : HSet → Set
⊨_ HA = HA {true}

G : HSet
G {true} = E
G {false} = D

noo : ⊨ G {false}
noo = {!!}

boo : ⊨ λ {b} → G {b}
boo = {!!}
