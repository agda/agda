-- Andreas, 2011-05-30
-- {-# OPTIONS -v tc.lhs.unify:50 #-}
module Issue292c where

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

data Unit1 : Set where unit1 : Unit1
data Unit2 : Set where unit2 : Unit2

D : Bool -> Set
D true  = Unit1
D false = Unit2

P : Set -> Set
P S = Σ S (\s → s ≅ unit1)

pbool : P (D true)
pbool = unit1 , refl

¬pbool2 : ¬ P (D false)
¬pbool2 ( unit2 , () )

{- expected error
unit2 ≅ unit1 should be empty, but that's not obvious to me
when checking that the clause ¬pbool2 (unit2 , ()) has type
¬ P (D false)
-}
