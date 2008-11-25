
module BadInductionRecursion3 where

data Bool : Set where
  false : Bool
  true  : Bool

data Two : Bool -> Set where
  zero : Two false
  suc  : Two false -> Two true

mutual
  data D : Set where
    d : forall u -> D′ true u -> D

  D′ : forall b -> Two b -> Set
  D′ ._ zero    = D
  D′ ._ (suc n) = D′ _ n -> Bool

_·_ : D -> D -> D
d (suc zero) f · x = f x

ω : D 
ω = d (suc zero) (\x -> x · x)

Ω : D
Ω = ω · ω
