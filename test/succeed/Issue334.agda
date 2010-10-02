-- 2010-10-02
-- termination checker now recognizes projections

module Issue334 where

data Functor : Set₁ where
  |Id|  : Functor
  _|x|_ : Functor → Functor → Functor

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

[_] : Functor → Set → Set
[ |Id|    ] X = X
[ F |x| G ] X = [ F ] X × [ G ] X

data µ_ (F : Functor) : Set where
  <_> : [ F ] (µ F) → µ F

mapFold : ∀ {X} F G → ([ G ] X → X) → [ F ] (µ G) → [ F ] X
mapFold |Id|         G  φ < x >   = φ (mapFold G G φ x)
mapFold (F1 |x| F2 ) G  φ (x , y) = mapFold F1 G φ x , mapFold F2 G φ y

-- after record pattern translation, this becomes
-- mapFold (F1 |x| F2) G φ r = mapFold F1 G φ (proj₁ r) , mapFold F2 G φ (proj₂ r)
-- foetus now honors  proj₁ p <= p