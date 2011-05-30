{-# OPTIONS -v tc.lhs.unify:50 #-}
module Issue292b where

data ⊥ : Set where

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

infix 4 _≅_

data _≅_ {A : Set} (x : A) : ∀ {B : Set} → B → Set where
  refl : x ≅ x

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

data Bool : Set where true false : Bool

data D : Bool -> Set where
  tt : D true
  ff : D false

P : Set -> Set
P S = Σ S (\s → s ≅ tt)

pbool : P (D true)
pbool = tt , refl

¬pbool2 : ¬ P (D false)
¬pbool2 ( ff , () )

-- Now we can show that D true ≠ D false
-- but they are isomorphic 
