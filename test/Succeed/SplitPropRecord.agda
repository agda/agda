{-# OPTIONS --prop #-}

open import Agda.Primitive

record LiftP {ℓ ℓ'}(A : Prop ℓ) : Prop (ℓ ⊔ ℓ') where
  constructor liftP
  field
    unliftP : A
open LiftP public

unliftP' : {ℓ ℓ' ℓ'' : Level} {A : Prop ℓ}{B : Set ℓ''}(f : A → B) → LiftP {ℓ}{ℓ'} A → B
unliftP' f (liftP x) = f x
