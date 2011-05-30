-- Andreas, 2011-05-30
-- {-# OPTIONS -v tc.lhs.unify:50 #-}
module Issue292 where
 
data Bool  : Set where true  false  : Bool
data Bool2 : Set where true2 false2 : Bool2

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

P : Set -> Set
P S = Σ S (\s → s ≅ true)

pbool : P Bool
pbool = true , refl

-- the following should fail:
¬pbool2 : ¬ P Bool2
¬pbool2 ( true2 , () )
¬pbool2 ( false2 , () )

{- using subst, one could now prove distinctness of types, which we don't want
tada : ¬ (Bool ≡ Bool2)
tada eq = ¬pbool2 (subst (\ S → P S) eq pbool )
-}