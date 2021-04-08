{-# OPTIONS --cubical #-}
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Sigma

data S1 : Set where
  base : S1
  loop : base ≡ base

data Torus : Set where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

t2c : Torus → Σ S1 \ _ → S1
t2c point = ( base , base )
t2c (line1 i) = ( loop i , base )
t2c (line2 i) = ( base , loop i )
t2c (square i1 i2) = ( loop i1 , loop i2 )
